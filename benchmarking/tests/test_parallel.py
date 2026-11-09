"""Thread identity, bounded collection, and the shared scaling figure contract."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest

from benchmarking import benchmark, collection, figures, models, processes, targets
from benchmarking.engines import Treatment
from benchmarking.figure_results import figure_results, latex_results
from benchmarking.reports.interactive_runtime import InteractiveRuntime, scope_for_comparison
from benchmarking.reports.store import CacheKey, ReportStore

from .report_fixtures import make_record, make_target


def test_threads_are_endpoint_identity_and_cli_selectors() -> None:
    args = benchmark.parse_benchmark_args(["--treatment", "off", "--threads", "4", "--compare-threads", "1"])
    serial, parallel = benchmark.endpoint_requests(args)
    assert serial.threads == 1 and parallel.threads == 4
    shared, checked = benchmark.endpoint_requests(benchmark.parse_benchmark_args(["--threads", "4"]))
    assert shared.threads == checked.threads == 4
    for threads in (0, -1, True):
        with pytest.raises(ValueError, match="positive integer"):
            models.EndpointRequest(serial.target, "off", threads=threads)
    with pytest.raises(ValueError, match="only supported by egglog"):
        models.EndpointRequest(serial.target, "egg", threads=4)


def test_cached_serial_rows_do_not_fill_parallel_runs_or_hide_them_in_the_ui(tmp_path: Path) -> None:
    target = make_target(target_label="scaling", binary_sha256="sha256:bin")
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    store = ReportStore(tmp_path / "report.jsonl")
    for threads in (1, 4):
        store.append(make_record(0, started_at="2026-11-08T00:00:00Z", threads=threads))
    requests = tuple(
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "off", threads=n), (file,))
        for n in (1, 2, 4)
    )
    plans = collection.plan_collection(store, requests, {target.request: target}, 1, 120, False)
    assert [(r.threads, r.missing_observations) for r in plans[0].runs] == [(1, 0), (2, 1), (4, 0)]
    serial = models.BenchmarkEndpoint(target.row, target.binary_sha256, "off")
    parallel = replace(serial, threads=4)
    assert CacheKey.for_endpoint(serial, file) != CacheKey.for_endpoint(parallel, file)
    comparison = models.ComparisonSpec(serial, parallel, (file,), 1, 120)
    runtime = InteractiveRuntime(store.grouped_report(), scope_for_comparison(comparison))
    payload = runtime.initial_payload(comparison)
    selectors = payload["selectors"]
    assert isinstance(selectors, dict)
    assert selectors["baseline_endpoint_id"] != selectors["candidate_endpoint_id"]
    assert "4 threads" in json.dumps(selectors)
    assert "Phase timings are unavailable" in json.dumps(payload)


def test_parallel_worker_uses_whole_process_metrics_without_serial_phase_summary(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    file = tmp_path / "file.egg"
    file.write_text("(check (= 1 1))")
    spec = models.FileSpec(str(file), file, targets.sha256_file(file))
    commands = []

    def run(command: list[str], *_args: Any, **_kwargs: Any) -> processes.TimingResult:
        commands.append(command)
        return processes.TimingResult("success", processes.TimingRow(1.25, 1024), None)

    monkeypatch.setattr(collection, "run_command", run)
    result = collection.run_process(Path("engine"), tmp_path, spec, "proof-testing", 90, threads=4)
    assert result.timing_summary is None
    assert result.result.timing.wall_sec == 1.25
    assert commands[0][commands[0].index("-j") + 1] == "4"
    assert "--proof-testing" in commands[0] and "--timing-summary" not in commands[0]
    row = collection.flat_report_record(
        started_at="2026-11-08T00:00:00Z",
        target=make_target(),
        timeout_sec=90,
        run=collection.BenchmarkRunPlan(spec, "proof-testing", 1, (), 1, threads=4),
        observation=result,
    )
    store = ReportStore(tmp_path / "result.jsonl")
    store.append(row)
    assert store.records[0]["threads"] == 4 and store.records[0]["timing_summary"] is None


def scaling_data(tmp_path: Path) -> tuple[list[dict[str, Any]], ReportStore]:
    store = ReportStore(tmp_path / "report.jsonl")
    inputs = []
    modes: tuple[tuple[Treatment, int], ...] = (("off", 1), ("off", 2), ("proofs", 1), ("proofs", 2))
    for name, means in (
        ("a", (4, 2, 12, 3)),
        ("b", (2, 2, 4, 2)),
        # Excluded solely by serial proofs-off time, even though its other modes are slow.
        ("fast", (0.1, 20, 999, 0.1)),
    ):
        for (treatment, threads), mean in zip(modes, means, strict=True):
            indices = []
            for _ in range(2):
                indices.append(store.row_count)
                store.append(
                    make_record(
                        0,
                        started_at="2026-11-08T00:00:00Z",
                        file_sha256=name,
                        treatment=treatment,
                        threads=threads,
                        wall_sec=mean,
                        max_rss_bytes=1048576,
                    )
                )
            inputs.append(
                {
                    "logical_id": name,
                    "label": name,
                    "family": "eggcc" if name == "a" else "misaal",
                    "file_sha256": name,
                    "binary_sha256": "sha256:bin",
                    "treatment": treatment,
                    "threads": threads,
                    "selected_row_indices": indices,
                    "exclusion": None,
                }
            )
    return inputs, store


def test_scaling_uses_each_modes_own_serial_mean_and_one_fixed_cohort(tmp_path: Path) -> None:
    inputs, store = scaling_data(tmp_path)
    result = figure_results("parallel-scaling", inputs, store.grouped_report(), 2, 12.7062)
    assert result["cohort_n"] == 2
    points = {(p["treatment"], p["threads"]): p for p in result["scaling"]}
    assert points["off", 1]["speedup"] == points["proofs", 1]["speedup"] == 1
    assert points["off", 2]["speedup"] == 1.5
    assert points["proofs", 2]["speedup"] == 3
    assert points["off", 2]["q25"] == 1.25 and points["off", 2]["q75"] == 1.75
    assert all(p["workloads"] == 2 for p in points.values())
    serial = [c for c in result["comparisons"] if c["threads"] == 1]
    assert all(c["metrics"]["runtime"]["ci_low"] == c["metrics"]["runtime"]["ci_high"] == 1 for c in serial)
    family_points = {(p["family"], p["treatment"], p["threads"]): p for p in result["family_scaling"]}
    assert family_points["eggcc", "off", 2]["speedup"] == 2
    assert family_points["misaal", "off", 2]["speedup"] == 1
    assert all(p["workloads"] == 1 for p in family_points.values())
    macros, table = latex_results(result)
    assert "All projects & Recording & 2 & 1.000 & 3.000" in table
    assert "Eggcc & Off & 1 & 1.000 & 2.000" in table
    assert "off-2threads" in macros and "proofs-2threads" in macros


def test_scaling_refuses_incomplete_cohort_instead_of_selecting_only_successes(tmp_path: Path) -> None:
    inputs, store = scaling_data(tmp_path)
    inputs[1]["selected_row_indices"] = []
    with pytest.raises(ValueError, match="incomplete cohort"):
        figure_results("parallel-scaling", inputs, store.grouped_report(), 2, 12.7062)


def test_scaling_catalog_uses_rq2_inputs_and_recording_only() -> None:
    config = figures.load_config(figures.DEFAULT_CONFIG)
    catalog = {figure.name: figure for figure in config.figures}
    scaling = catalog["parallel-scaling"]
    assert scaling.patterns == catalog["corpus-proof-recording-cdf"].patterns
    assert scaling.treatments == ("off", "proofs")
    assert scaling.threads == (1, 2, 4, 8)


@pytest.mark.parametrize("threads", [[], [1, 1], [0, 2], [True], [2, 4]])
def test_scaling_catalog_rejects_ambiguous_or_missing_serial_reference(tmp_path: Path, threads: list[int]) -> None:
    config = tmp_path / "catalog.json"
    config.write_text(
        json.dumps(
            {
                "rounds": 1,
                "figures": {
                    "parallel-scaling": {
                        "spec": "chart.json",
                        "files": ["*.egg"],
                        "treatments": ["off", "proofs"],
                        "threads": threads,
                    }
                },
            }
        )
    )
    with pytest.raises(ValueError):
        figures.load_config(config)
