"""Executable root/pushdown/sharing choices preserve natural-join bag queries."""

from __future__ import annotations

import itertools
import json
import os
import signal
import subprocess
import sys
import time
from collections import Counter, defaultdict
from contextlib import suppress
from fractions import Fraction
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from benchmarking.lmfao import cli, model
from benchmarking.lmfao.optimizer import extractor_path, seconds_summary

ROOT = Path(__file__).resolve().parents[2]
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
    attrs, schema = model.WORKLOAD.attributes, model.WORKLOAD.relations
    names, tables, functions = [a for a, _ in attrs], list(schema), model.WORKLOAD.functions
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


@pytest.fixture(scope="module")
def extractor_binary() -> Path:
    subprocess.run(["cargo", "build", "--locked", "-p", "lmfao-extract"], cwd=ROOT, check=True)
    return extractor_path("debug")


@pytest.mark.parametrize("target", [None, "custom-target", "/tmp/lmfao-custom-target"])
def test_extractor_path_honors_cargo_target_dir(target: str | None, monkeypatch: pytest.MonkeyPatch) -> None:
    if target is None:
        monkeypatch.delenv("CARGO_TARGET_DIR", raising=False)
    else:
        monkeypatch.setenv("CARGO_TARGET_DIR", target)
    assert extractor_path("release") == ROOT / (target or "target") / "release/lmfao-extract"


def test_fixed_workload_is_original_covariance_configuration() -> None:
    assert len(model.WORKLOAD.queries) == 140
    assert Counter(len(q.groups) for q in model.WORKLOAD.queries) == {0: 10, 1: 52, 2: 78}
    assert len(model.WORKLOAD.relations) == 6


def test_cli_limits(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    calls: list[Any] = []
    monkeypatch.setattr(cli, "run", calls.append)
    argv = ["--data", str(tmp_path), "--backend", str(tmp_path / "multifaq"), "--output-dir", str(tmp_path / "out")]
    assert cli.main([*argv, "--rounds", "1", "--dag-timeout", "2"]) == 0
    assert calls[0].samples == 1 and calls[0].dag_timeout == 2
    for value in ["0", "-1", "nan", "inf"]:
        with pytest.raises(SystemExit):
            cli.main([*argv, "--dag-timeout", value])
    for option in ("--rounds", "--rewrite-rounds", "--timeout-sec", "--jobs"):
        with pytest.raises(SystemExit):
            cli.main([*argv, option, "0"])
    with pytest.raises(SystemExit):
        cli.main([*argv, "--report", "-"])
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
        backend.generate(tmp_path / "multifaq", tmp_path, tmp_path / "out", {})


def test_cpp_timing_retains_whole_process_and_upstream_scope(tmp_path: Path) -> None:
    from benchmarking.lmfao import backend

    program = tmp_path / "lmfao"
    program.write_text('#!/bin/sh\nprintf "Data loading: 9ms.\\nData sorting: 2ms.\\nData process: 37ms.\\n"\n')
    program.chmod(0o755)
    row = backend.execute(tmp_path, 0, 5)
    assert row["process_seconds"] > 0
    assert row["computation_seconds"] == 0.037
    assert (tmp_path / "run-0.log").read_text().endswith("Data process: 37ms.\n")


@pytest.mark.parametrize("nested_optimizer", [False, True])
def test_backend_timeout_stops_optimizer_and_compiler_children(tmp_path: Path, nested_optimizer: bool) -> None:
    from benchmarking.lmfao import backend

    script = (
        "import subprocess, sys, time; from pathlib import Path; "
        "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
        "Path('child.pid').write_text(str(child.pid)); print('started', flush=True); time.sleep(60)"
    )
    args = [sys.executable, "-c", script]
    env = {**os.environ, "PYTHONPATH": str(ROOT)}
    if nested_optimizer:
        extractor = tmp_path / "extractor"
        extractor.write_text(
            f"#!{sys.executable}\nimport os, time\nfrom pathlib import Path\n"
            f"Path({str(tmp_path / 'child.pid')!r}).write_text(str(os.getpid()))\ntime.sleep(60)\n"
        )
        extractor.chmod(0o755)
        config = tmp_path / "optimizer.json"
        config.write_text(
            json.dumps(
                dict(
                    rewrite_rounds=192,
                    treatment="slotted",
                    extractor=str(extractor),
                    timeout=60,
                    dag_timeout=5,
                    memory_limit_bytes=None,
                )
            )
        )
        args = [
            sys.executable,
            "-m",
            "benchmarking.lmfao.optimize",
            str(config),
            str(model.FIXTURES / "workload.json"),
            str(tmp_path / "plan.json"),
        ]
    try:
        with pytest.raises(RuntimeError, match="failed; see") as error:
            backend.command(args, tmp_path, "command.log", env=env, timeout=2)
        assert isinstance(error.value.__cause__, subprocess.TimeoutExpired)
        if not nested_optimizer:
            assert (tmp_path / "command.log").read_text() == "started\n"
        pid = int((tmp_path / "child.pid").read_text())
        deadline = time.monotonic() + 2
        while time.monotonic() < deadline:
            state = subprocess.run(
                ["ps", "-o", "state=", "-p", str(pid)], capture_output=True, text=True, check=False
            ).stdout.strip()
            if not state or state.startswith("Z"):
                break
            time.sleep(0.01)
        else:
            pytest.fail("backend descendant survived timeout")
    finally:
        if (tmp_path / "child.pid").exists():
            with suppress(ProcessLookupError):
                os.kill(int((tmp_path / "child.pid").read_text()), signal.SIGKILL)


def test_pipeline_charges_hook_once_and_excludes_validation_and_diagnostics(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    now = 0.0

    def spend(seconds: float) -> None:
        nonlocal now
        now += seconds

    monkeypatch.setattr(cli, "time", SimpleNamespace(perf_counter=lambda: now))
    documents: dict[str, Any] = {"slotted": {"treatment": "slotted"}, "debruijn": {"treatment": "off"}}

    def collect(output: Path, *args: Any, **kwargs: Any) -> tuple[dict[str, Any], dict[str, Any]]:
        spend(999)
        return documents, {
            "optimizer": {
                label: {"process_seconds": {"median_seconds": 999}, "completed_samples": 2} for label in documents
            },
            "rewrite_round_budget": 192,
            "optimizer_memory_limit_bytes": 16 * 1024**3,
            "extractor_path": "/lmfao-extract",
        }

    class Database:
        def close(self) -> None:
            spend(1)

    def load(directory: Path) -> tuple[Database, dict[str, Any]]:
        assert all((tmp_path / "out" / label / "plan.json").exists() for label in documents)
        spend(10)
        return Database(), {"input_rows": {"Sales": 2}}

    def oracle(db: Database) -> list[Any]:
        spend(2000)
        return []

    def generate(compiler: Path, data: Path, directory: Path, optimizer: Any, **kwargs: Any) -> dict[str, Any]:
        directory.mkdir()
        plan = {
            "views": [{"origin": 0, "destination": 0, "keys": [], "aggregates": [{"functions": [], "incoming": []}]}],
            "outputs": [{"view": 0, "aggregate": 0, "root": 0}],
        }
        cli.write_json(directory / "plan.json", plan)
        elapsed = 2 if optimizer is None else (27 if optimizer["treatment"] == "slotted" else 29)
        cli.write_json(
            directory / "extraction.json", {"estimated_cost": 3, "phases_seconds": {"rewriting": elapsed - 2}}
        )
        spend(elapsed)
        return {"generation_seconds": elapsed}

    def compile(directory: Path, **kwargs: Any) -> dict[str, Any]:
        (directory / "lmfao").touch()
        spend(40)
        return {"compilation_seconds": 40}

    def validate(*args: Any, **kwargs: Any) -> dict[str, Any]:
        spend(1000)
        return {"queries_checked": 140}

    def execute(directory: Path, repeat: int, timeout: int) -> dict[str, float]:
        elapsed = (1.0 if directory.name == "original" else 0.5) + repeat / 10
        spend(elapsed)
        return {"process_seconds": elapsed, "computation_seconds": elapsed / 2}

    monkeypatch.setattr(cli, "collect_optimizers", collect)
    monkeypatch.setattr(cli, "verify_backend", lambda _: {"lmfao_commit": model.COMMIT})
    monkeypatch.setattr(cli, "load_data", load)
    monkeypatch.setattr(cli, "reference_results", oracle)
    monkeypatch.setattr(cli.backend, "generate", generate)
    monkeypatch.setattr(cli.backend, "compile", compile)
    monkeypatch.setattr(cli.backend, "validate", validate)
    monkeypatch.setattr(cli.backend, "execute", execute)
    compiler = tmp_path / "multifaq"
    compiler.touch()
    output = tmp_path / "out"
    assert (
        cli.main(
            [
                "--data",
                str(tmp_path),
                "--backend",
                str(compiler),
                "--output-dir",
                str(output),
                "--rounds",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    report = json.loads(capsys.readouterr().out)
    assert report == json.loads((output / "pipeline.json").read_text())
    costs = report["accounted_pipeline"]
    assert costs["original"]["one_time_phase_sum_seconds"] == 42
    assert costs["slotted"]["one_time_phase_sum_seconds"] == 67
    assert costs["debruijn"]["one_time_phase_sum_seconds"] == 69
    assert costs["debruijn"]["execution_label"] == "slotted"
    assert costs["original"]["optimization_and_generation_seconds"] == 2
    assert costs["slotted"]["optimization_and_generation_seconds"] == 27
    assert costs["slotted"]["compilation_seconds"] == 40
    assert report["metadata"]["validation_preparation_seconds"] == 2011
    assert len(report["builds"]) == 4 and len(report["validation"]) == 3
    assert "compilation_seconds" not in report["builds"]["debruijn"]
    assert "not a measured end-to-end" in report["phase_scope"]
    comparison = (output / "comparison.md").read_text()
    assert "Slotted egglog" in comparison and "Ordinary egglog (de Bruijn)" in comparison
    assert "27.000 | 40.000 | 0.2750" in comparison
    assert "2 egraph / 2 execution" in comparison


def test_optimizer_rejects_workload_drift_before_rewriting(tmp_path: Path) -> None:
    from benchmarking.lmfao.optimize import run

    source = tmp_path / "workload.json"
    changed = {**model.WORKLOAD.document, "root": "1"}
    source.write_text(json.dumps(changed))
    with pytest.raises(ValueError, match="frontend differs"):
        run({}, source, tmp_path / "plan.json")
    assert not (tmp_path / "plan.json").exists()


def test_report_distinguishes_replication_and_resource_failures() -> None:
    from benchmarking.lmfao.report import comparison_markdown

    result = comparison_markdown(
        {
            "rewrite_round_budget": 192,
            "optimizer": {"debruijn": {"failures": [{"status": "memory-limit"}]}},
            "optimizer_memory_limit_bytes": 16 * 1024**3,
            "accounted_pipeline": {},
        }
    )
    assert "LMFAO configured roots" in result
    assert "LMFAO + paper root heuristic" in result
    assert "Ordinary egglog (de Bruijn) (memory-limit)" in result
    assert "not the paper's full 127M-row experiment" in result
    assert "our implementation" in result and "allocator/address-space cap" in result
