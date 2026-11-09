"""Collect LMFAO rewrite timings through the shared benchmark/cache machinery."""

from __future__ import annotations

import json
import os
import statistics
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

from rich.console import Console

from benchmarking.collection import BenchmarkRequest, collect, plan_collection, resolve_requests
from benchmarking.engines import Treatment
from benchmarking.models import BenchmarkEndpoint, EndpointRequest
from benchmarking.reports.store import ReportRecord, ReportStore, select_observations
from benchmarking.targets import parse_target, sha256_file
from benchmarking.workloads import resolve_files

ROOT = Path(__file__).resolve().parents[2]


def extractor_path(profile: str) -> Path:
    target = Path(os.environ.get("CARGO_TARGET_DIR", "target"))
    executable = "lmfao-extract.exe" if os.name == "nt" else "lmfao-extract"
    return ROOT / target / profile / executable


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def seconds_summary(values: Iterable[float]) -> dict[str, float | int] | None:
    samples = list(values)
    if not samples:
        return None
    return {
        "median_seconds": statistics.median(samples),
        "min_seconds": min(samples),
        "max_seconds": max(samples),
        "samples": len(samples),
    }


def summarize_optimizer(rows: list[ReportRecord], budget: int, requested: int, issue: str | None) -> dict[str, Any]:
    completed = [row for row in rows if row["status"] == "success"]
    return {
        "rewrite_round_budget": budget,
        "requested_samples": requested,
        "completed_samples": len(completed),
        "issue": issue,
        "process_seconds": seconds_summary(row["wall_sec"] for row in completed if row["wall_sec"] is not None),
        "ruleset_work_seconds": seconds_summary(
            sum(
                r["assembly_ns"] + r["search_ns"] + r["apply_ns"] + r["execution_ns"] + r["merge_ns"]
                for r in row["timing_summary"]["rulesets"]
            )
            / 1e9
            for row in completed
            if row["timing_summary"] is not None
        ),
        "failures": [row for row in rows if row["status"] != "success"],
    }


def collect_optimizers(
    output: Path,
    samples: int,
    timeout: int,
    report_path: Path | None,
    memory_limit_bytes: int | None,
    *,
    rewrite_rounds: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Measure the executable scoped lowering with the shared collector."""
    from .program import program

    modes: dict[str, Treatment] = {"slotted": "slotted", "debruijn": "off"}
    request = parse_target(str(ROOT))
    files = {}
    requests = []
    for mode, treatment in modes.items():
        path = output / f"{mode}.egg"
        path.write_text(program(mode, rounds=rewrite_rounds))
        files[mode] = resolve_files([str(path)], ROOT)[0]
        requests.append(
            BenchmarkRequest(EndpointRequest(request, treatment, memory_limit_bytes=memory_limit_bytes), (files[mode],))
        )
    store = ReportStore(report_path or output / "optimizer.jsonl")
    console = Console(stderr=True)
    targets = resolve_requests(tuple(requests), store, samples, timeout, False, ROOT, ROOT, console)
    pending = plan_collection(store, tuple(requests), targets, samples, timeout, False)
    collect(store, pending, tuple(requests), targets, timeout, console)
    subprocess.run(
        ["cargo", "build", "--locked", "--release", "-p", "lmfao-extract"],
        cwd=ROOT,
        check=True,
        stdout=sys.stderr,
    )
    target = targets[request]
    report: dict[str, Any] = {
        "rewrite_round_budget": rewrite_rounds,
        "optimizer": {},
        "extractor_path": str(extractor_path("release")),
        "extractor_sha256": sha256_file(extractor_path("release")),
        "binary_paths": {t: str(target.binary_path_for(t)) for t in modes.values()},
        "binary_sha256": {t: target.binary_sha256_for(t) for t in modes.values()},
        "optimizer_report": str(store.path),
        "optimizer_memory_limit_bytes": memory_limit_bytes,
    }
    successful = {}
    for mode, treatment in modes.items():
        label = f"{mode}"
        endpoint = BenchmarkEndpoint(
            target.row, target.binary_sha256_for(treatment), treatment, memory_limit_bytes=memory_limit_bytes
        )
        selection = select_observations(store, endpoint, files[mode], samples, timeout)
        rows = [row.record for row in selection.rows]
        result = summarize_optimizer(rows, rewrite_rounds, samples, selection.issue)
        memory = [r["max_rss_bytes"] for r in rows if r["status"] == "success" and r["max_rss_bytes"] is not None]
        result.update(
            input_sha256=files[mode].sha256,
            max_rss_bytes=statistics.median(memory) if memory else None,
        )
        report["optimizer"][label] = result
        if selection.issue is None and all(r["status"] == "success" for r in rows) and len(rows) == samples:
            successful[label] = {"treatment": treatment}
    write_json(output / "optimizer-summary.json", report)
    return successful, report
