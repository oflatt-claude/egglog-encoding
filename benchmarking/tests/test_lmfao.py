"""Selected batch plans execute correctly and report optimizer work separately."""

from __future__ import annotations

import json
import random
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any

import duckdb
import pytest

from benchmarking.lmfao import cli, model, sql
from benchmarking.lmfao.batch import BatchExtractor, Graph
from benchmarking.lmfao.optimizer import seconds_summary
from benchmarking.targets import sha256_file

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = Path(__file__).with_name("fixtures") / "lmfao"
QUERIES = [
    model.Query(),
    model.Query((), ("x",)),
    model.Query((), ("x", "x")),
    model.Query(("k",)),
    model.Query(("k",), ("x",)),
    model.Query(("z",)),
    model.Query(("k", "z")),
    model.Query(("z", "k")),
    model.Query(("k", "k")),
    model.Query(("k", "z", "x")),
]


def expected(rows: list[dict[str, Any]]) -> list[dict[tuple[Any, ...], Fraction]]:
    outputs = []
    for query in QUERIES:
        groups = {} if query.groups else {(): Fraction(0)}
        for row in rows:
            key = tuple(row[g] for g in query.groups)
            weight = Fraction(1)
            for factor in query.factors:
                weight *= row[factor]
            groups[key] = groups.get(key, Fraction(0)) + weight
        outputs.append(groups)
    return outputs


@pytest.mark.parametrize("mode", ["independent", "pack", "fuse", "grouping"])
def test_selected_batch_sql_matches_independent_bag_oracle(mode: str) -> None:
    manifest = json.loads((FIXTURES / "manifest.json").read_text())
    path = FIXTURES / f"{mode}.json"
    assert sha256_file(path) == manifest[mode]["graph_sha256"]
    assert sha256_file(ROOT / f"benchmarks/lmfao/correctness/{mode}.egg") == manifest[mode]["input_sha256"]
    graph = Graph(json.loads(path.read_text()), {"R": ["k", "z", "x"]})
    extractor = BatchExtractor(graph, {c: 100 for c in graph.sources}, dict.fromkeys(range(len(QUERIES)), 10))
    selected, info = extractor.extract(dag_timeout=5)
    assert info["optimal"]
    assert info["estimated_cost"] <= info["original_plan_dag_cost"]
    if mode in ("fuse", "grouping"):
        assert graph.nodes[selected[graph.root]]["op"] == ("FusedBatch" if mode == "fuse" else "GroupingBatch")
    with pytest.raises(ValueError, match="absent"):
        extractor.sql(selected | {graph.root: "fabricated-node"})
    plans = {tuple(extractor.sql(selected, lowering_control=control)[0]) for control in (False, True)}
    rng = random.Random(81294)
    for trial in range(16):
        data: list[dict[str, Any]] = [
            {"k": rng.choice([None, 0, 1]), "z": rng.randrange(3), "x": Fraction(rng.randrange(-4, 5), 2)}
            for _ in range(trial % 9)
        ]
        want = expected(data)
        db = duckdb.connect()
        try:
            db.execute("SET threads=1")
            db.execute("CREATE TABLE R (k BIGINT, z BIGINT, x DOUBLE)")
            if data:
                db.executemany("INSERT INTO R VALUES (?, ?, ?)", [(r["k"], r["z"], float(r["x"])) for r in data])
            for plan in plans:
                connection = db.cursor()
                try:
                    for statement in plan:
                        connection.execute(statement)
                    for i, rows in enumerate(want):
                        result = connection.execute(f"SELECT * FROM q{i}").fetchall()
                        assert len(result) == len(rows)
                        assert {tuple(r[:-1]): r[-1] for r in result} == rows
                finally:
                    connection.close()
        finally:
            db.close()


@pytest.mark.parametrize("rows", [[], [(None,), (None,), (2,)]])
def test_scalar_and_null_group_are_distinct(rows: list[tuple[int | None]]) -> None:
    choices = [
        sql.Choice(0, "scalar", (), "CAST(1 AS DOUBLE)"),
        sql.Choice(1, "grouped", ('"k"',), "CAST(1 AS DOUBLE)"),
    ]
    db = duckdb.connect()
    try:
        db.execute("SET threads=1")
        db.execute("CREATE TABLE R(k BIGINT)")
        if rows:
            db.executemany("INSERT INTO R VALUES (?)", rows)
        for statement in sql.execution_sql("SELECT * FROM R", choices, fuse=True, grouping_sets=True):
            db.execute(statement)
        assert db.execute("SELECT * FROM q0").fetchall() == [(len(rows),)]
        assert {(k,): n for k, n in db.execute("SELECT * FROM q1").fetchall()} == Counter(rows)
    finally:
        db.close()


def test_fixed_workload_is_the_140_query_configuration() -> None:
    queries = model.queries()
    assert len(queries) == 140
    assert Counter(len(q.groups) for q in queries) == {0: 10, 1: 52, 2: 78}
    assert len(model.schema()[1]) == 6
    assert len(model.features()) == 16


def test_cli_rounds_mean_samples_and_reject_invalid_limits(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    calls: list[Any] = []
    monkeypatch.setattr(cli, "run", calls.append)
    argv = ["--data", str(tmp_path), "--output-dir", str(tmp_path / "out")]
    assert cli.main([*argv, "--rounds", "1", "--dag-timeout", "2"]) == 0
    assert calls[0].samples == 1 and calls[0].dag_timeout == 2
    for value in ["-1", "nan", "inf"]:
        with pytest.raises(SystemExit):
            cli.main([*argv, "--dag-timeout", value])
    assert seconds_summary([]) is None


def test_nonlinear_bag_multiplicity_is_rejected() -> None:
    graph = json.loads((FIXTURES / "nonlinear.json").read_text())
    with pytest.raises(ValueError, match="linear in bag multiplicity"):
        Graph(graph, {"R": ["k", "z", "x"]})


def test_optimizer_report_keeps_failures_and_distinct_timing_scopes() -> None:
    from benchmarking.lmfao.optimizer import summarize_optimizer
    from benchmarking.tests.report_fixtures import make_record, make_timing_summary

    good = make_record(0, started_at="2026-11-06T00:00:00Z", wall_sec=2.0, timing_summary=make_timing_summary())
    failure = make_record(1, started_at="2026-11-06T00:00:01Z", status="timed-out", timeout_sec=60)
    result = summarize_optimizer([good, failure], 12, 3, "missing 1 row(s)")
    assert result["rewrite_round_budget"] == 12 and result["completed_samples"] == 1
    assert result["process_seconds"] == {"median_seconds": 2.0, "min_seconds": 2.0, "max_seconds": 2.0, "samples": 1}
    assert result["ruleset_work_seconds"]["median_seconds"] == 0.8
    assert result["failures"] == [failure] and result["issue"]
    missing = summarize_optimizer([failure], 12, 3, "timeout")
    assert missing["process_seconds"] is None and missing["ruleset_work_seconds"] is None
