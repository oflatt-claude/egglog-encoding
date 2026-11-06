"""Executable root/pushdown/sharing choices preserve natural-join bag queries."""

from __future__ import annotations

import itertools
import json
import random
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from benchmarking.lmfao import cli, model
from benchmarking.lmfao.logical import Extractor, Graph
from benchmarking.lmfao.optimizer import seconds_summary
from benchmarking.targets import sha256_file

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = Path(__file__).with_name("fixtures") / "lmfao"
QUERIES = [
    model.Query(),
    model.Query((), ("unit_sales",)),
    model.Query((), ("unit_sales", "oilprize")),
    model.Query(("family",)),
    model.Query(("family",), ("unit_sales",)),
    model.Query(("city",), ("oilprize", "oilprize")),
]


def join(tables: list[list[dict[str, Any]]]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for rows in itertools.product(*tables):
        merged: dict[str, Any] = {}
        for row in rows:
            if any(merged[k] != v for k, v in row.items() if k in merged):
                break
            merged.update(row)
        else:
            result.append(merged)
    return result


def evaluate(plan: dict[str, Any], data: dict[str, list[dict[str, Any]]]) -> list[dict[tuple[Any, ...], Fraction]]:
    attrs, schema, _ = model.schema()
    names, tables, functions = [a for a, _ in attrs], list(schema), model.function_specs()
    computed: dict[int, list[dict[tuple[Any, ...], Fraction]]] = {}

    def view(i: int) -> list[dict[tuple[Any, ...], Fraction]]:
        if i in computed:
            return computed[i]
        v = plan["views"][i]
        columns = []
        for aggregate in v["aggregates"]:
            inputs = [data[tables[v["origin"]]]]
            for j, (child, col) in enumerate(aggregate["incoming"]):
                keys = [names[k] for k in plan["views"][child]["keys"]]
                inputs.append(
                    [
                        {**dict(zip(keys, key, strict=True)), f"weight{j}": weight}
                        for key, weight in view(child)[col].items()
                    ]
                )
            result: dict[tuple[Any, ...], Fraction] = defaultdict(Fraction)
            for row in join(inputs):
                weight = Fraction(1)
                for f in aggregate["functions"]:
                    name, power = functions[f]
                    weight *= row[name] ** power
                for j in range(len(aggregate["incoming"])):
                    weight *= row[f"weight{j}"]
                result[tuple(row[names[k]] for k in v["keys"])] += weight
            columns.append(result)
        computed[i] = columns
        return columns

    return [view(o["view"])[o["aggregate"]] for o in plan["outputs"]]


@pytest.mark.parametrize("mode", ["single-root", "roots", "shared"])
def test_extracted_dag_preserves_original_queries(mode: str) -> None:
    manifest = json.loads((FIXTURES / "manifest.json").read_text())
    path = FIXTURES / f"{mode}.json"
    assert sha256_file(path) == manifest[mode]["graph_sha256"]
    assert sha256_file(ROOT / f"benchmarks/lmfao/correctness/{mode}.egg") == manifest[mode]["input_sha256"]
    g = Graph(json.loads(path.read_text()))
    assert len(g.outputs) == len(QUERIES)
    for _, root, _ in g.outputs:
        roots = {g.regions[g.views[n].region].origin for n in g.options[root]}
        assert roots == ({"Sales"} if mode == "single-root" else set(model.schema()[1]))
    assert bool(g.producers) == (mode != "roots")
    stats = {(v.region, v.keys): (100, 10) for v in g.views.values()}
    stats.update(dict.fromkeys(g.producers.values(), (100, 10)))
    ex = Extractor(g, stats)
    selected, info = ex.extract(5)
    assert info["solver"]["optimal"]
    with pytest.raises(ValueError, match="exported alternative"):
        ex.score(selected | {g.outputs[0][1]: "invented-node"})
    choices = [selected]
    # Exercise every orientation, including roots the cost model did not choose.
    for root in ["Sales"] if mode == "single-root" else model.schema()[1]:
        forced = {c: ns[0] for c, ns in g.options.items()}
        for _, c, _ in g.outputs:
            forced[c] = next(n for n in g.options[c] if g.regions[g.views[n].region].origin == root)
        choices.append(forced)
    rng = random.Random(804)
    for trial in range(8):
        data = {}
        for name, fields in model.schema()[1].items():
            rows = [
                {
                    k: Fraction(rng.randrange(-3, 4), 2)
                    if k in {"unit_sales", "oilprize", "transactions"}
                    else rng.randrange(2)
                    for k in fields
                }
                for _ in range(trial % 4 + 1)
            ]
            data[name] = rows + [rows[0]]  # Preserve bag multiplicities in every relation.
        expected = []
        for q in QUERIES:
            answer: dict[tuple[Any, ...], Fraction] = defaultdict(Fraction)
            for row in join(list(data.values())):
                weight = Fraction(1)
                for f in q.factors:
                    weight *= row[f]
                answer[tuple(row[k] for k in q.groups)] += weight
            expected.append(answer)
        for selection in choices:
            assert evaluate(ex.plan(selection), data) == expected


def test_fixed_workload_is_original_covariance_configuration() -> None:
    assert len(model.queries()) == 140
    assert Counter(len(q.groups) for q in model.queries()) == {0: 10, 1: 52, 2: 78}
    assert len(model.schema()[1]) == 6 and len(model.features()) == 16


def test_cli_limits(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    calls: list[Any] = []
    monkeypatch.setattr(cli, "run", calls.append)
    argv = ["--data", str(tmp_path), "--backend", str(tmp_path / "multifaq"), "--output-dir", str(tmp_path / "out")]
    assert cli.main([*argv, "--rounds", "1", "--dag-timeout", "2"]) == 0
    assert calls[0].samples == 1 and calls[0].dag_timeout == 2
    for value in ["0", "-1", "nan", "inf"]:
        with pytest.raises(SystemExit):
            cli.main([*argv, "--dag-timeout", value])
    for name, value in [("treatment", "slotted"), ("variant", "shared")]:
        with pytest.raises(SystemExit):
            cli.main([*argv, f"--{name}", value, f"--{name}", value])
    assert seconds_summary([]) is None


def test_optimizer_report_keeps_failures_and_timing_scopes() -> None:
    from benchmarking.lmfao.optimizer import summarize_optimizer
    from benchmarking.tests.report_fixtures import make_record, make_timing_summary

    good = make_record(0, started_at="2026-11-06T00:00:00Z", wall_sec=2.0, timing_summary=make_timing_summary())
    failure = make_record(1, started_at="2026-11-06T00:00:01Z", status="timed-out", timeout_sec=60)
    result = summarize_optimizer([good, failure], 64, 3, "missing 1 row(s)")
    assert result["rewrite_round_budget"] == 64 and result["completed_samples"] == 1
    assert result["process_seconds"]["median_seconds"] == 2
    assert result["ruleset_work_seconds"]["median_seconds"] == 0.8
    assert result["failures"] == [failure] and result["issue"]


def test_backend_requires_explicit_import_acknowledgement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    from benchmarking.lmfao import backend

    def fake_command(args: list[str], directory: Path, log: str, **kwargs: Any) -> float:
        (directory / log).write_text("ordinary compiler; ignored plan environment variable\n")
        return 0.0

    monkeypatch.setattr(backend, "command", fake_command)
    with pytest.raises(ValueError, match="did not acknowledge"):
        backend.prepare(tmp_path / "multifaq", tmp_path, tmp_path / "out", tmp_path / "plan.json")


def test_cpp_timing_retains_whole_process_and_upstream_scope(tmp_path: Path) -> None:
    from benchmarking.lmfao import backend

    program = tmp_path / "lmfao"
    program.write_text('#!/bin/sh\nprintf "Data loading: 9ms.\\nData sorting: 2ms.\\nData process: 37ms.\\n"\n')
    program.chmod(0o755)
    row = backend.execute(tmp_path, 0, 5)
    assert row["process_seconds"] > 0
    assert row["computation_seconds"] == 0.037
    assert (tmp_path / "run-0.log").read_text().endswith("Data process: 37ms.\n")


def test_pipeline_charges_statistics_and_export_but_not_validation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    now = 0.0

    def spend(seconds: float) -> None:
        nonlocal now
        now += seconds

    monkeypatch.setattr(cli, "time", SimpleNamespace(perf_counter=lambda: now))
    documents = {"shared-slotted": {"statistics": 20}, "shared-slotted-ref-multi": {"statistics": 30}}

    def collect(output: Path, *args: Any, **kwargs: Any) -> tuple[dict[str, Any], dict[str, Any]]:
        for label, document in documents.items():
            cli.write_json(output / f"{label}-graph.json", document)
        return documents, {
            "optimizer": {label: {"process_seconds": 999} for label in documents},
            "graph_collection": {label: {"seconds": 11 + 2 * i} for i, label in enumerate(documents)},
        }

    def graph(document: dict[str, Any]) -> dict[str, Any]:
        spend(2)
        return document

    class Database:
        def close(self) -> None:
            spend(1)

    def load(directory: Path) -> tuple[Database, dict[str, Any]]:
        spend(10)
        return Database(), {"input_rows": {"Sales": 2}}

    def statistics(db: Database, graph: dict[str, Any]) -> tuple[dict[Any, Any], list[Any]]:
        spend(graph["statistics"])
        return {}, []

    class Extraction:
        def __init__(self, *args: Any) -> None:
            spend(2)

        def extract(self, timeout: float) -> tuple[dict[str, Any], dict[str, Any]]:
            spend(3)
            return {}, {}

        def plan(self, selected: Any) -> dict[str, Any]:
            spend(7)
            return {"views": [{"aggregates": [{}]}]}  # Both engines select the same plan.

    def oracle(db: Database) -> list[Any]:
        spend(2000)
        return []

    def prepare(compiler: Path, data: Path, directory: Path, plan: Path | None, **kwargs: Any) -> dict[str, Any]:
        directory.mkdir()
        (directory / "lmfao").touch()
        spend(42)
        return {"generation_seconds": 2, "compilation_seconds": 40}

    def validate(*args: Any, **kwargs: Any) -> dict[str, Any]:
        spend(1000)
        return {"queries_checked": 140}

    def execute(directory: Path, repeat: int, timeout: int) -> dict[str, float]:
        elapsed = (1.0 if directory.name == "original" else 0.5) + repeat / 10
        spend(elapsed)
        return {"process_seconds": elapsed, "computation_seconds": elapsed / 2}

    monkeypatch.setattr(cli, "collect_optimizers", collect)
    monkeypatch.setattr(cli, "Graph", graph)
    monkeypatch.setattr(cli, "load_data", load)
    monkeypatch.setattr(cli, "collect_statistics", statistics)
    monkeypatch.setattr(cli, "Extractor", Extraction)
    monkeypatch.setattr(cli, "reference_results", oracle)
    monkeypatch.setattr(cli.backend, "prepare", prepare)
    monkeypatch.setattr(cli.backend, "validate", validate)
    monkeypatch.setattr(cli.backend, "execute", execute)
    compiler = tmp_path / "multifaq"
    compiler.touch()
    output = tmp_path / "out"
    assert (
        cli.main(["--data", str(tmp_path), "--backend", str(compiler), "--output-dir", str(output), "--rounds", "2"])
        == 0
    )
    report = json.loads(capsys.readouterr().out)
    assert report == json.loads((output / "pipeline.json").read_text())
    costs = report["accounted_pipeline"]
    assert costs["original"]["one_time_phase_sum_seconds"] == 42
    assert costs["shared-slotted"]["one_time_phase_sum_seconds"] == 98
    assert costs["shared-slotted-ref-multi"]["one_time_phase_sum_seconds"] == 110
    assert costs["shared-slotted-ref-multi"]["execution_label"] == "shared-slotted"
    assert costs["original"]["statistics_seconds"] == 0
    assert costs["original"]["optimization_and_generation_seconds"] == 2
    assert costs["shared-slotted"]["statistics_seconds"] == 31
    assert costs["shared-slotted"]["optimization_and_generation_seconds"] == 27
    assert costs["shared-slotted"]["compilation_seconds"] == 40
    assert report["metadata"]["validation_preparation_seconds"] == 2011
    assert len(report["builds"]) == len(report["validation"]) == 2
    assert "not a measured end-to-end" in report["phase_scope"]
    comparison = (output / "comparison.md").read_text()
    assert "| shared / egglog | All six | Enabled | 0.2750 | 2 |" in comparison
    assert "| shared / native multipattern | All six | Enabled | 0.2750 | 2 |" in comparison
    assert "| shared / egglog | 31.0000 | 27.0000 | 40.0000 |" in comparison


def test_comparison_caption_names_ablation_pairs_and_preserves_missing_results() -> None:
    from benchmarking.lmfao.report import comparison_markdown

    labels = ("original", "single-root-slotted", "roots-slotted", "shared-slotted-ref-multi")
    result = comparison_markdown(
        {
            "optimizer": dict.fromkeys(labels[1:]),
            "accounted_pipeline": {},
        }
    )
    assert "| single-root / egglog | Sales only | Enabled | unavailable | — |" in result
    assert "| roots / egglog | All six | Disabled | unavailable | — |" in result
    assert "| shared / native multipattern | All six | Enabled | unavailable | — |" in result
    assert "compare shared with single-root" in result and "shared with roots" in result
    assert "identical-subexpression reuse" in result and "loading and sorting" in result
    assert "N × execution" in result
