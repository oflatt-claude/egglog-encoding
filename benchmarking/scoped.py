"""Collect optimizer time, extracted terms and graph sizes for binding experiments."""

from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
from pathlib import Path
from typing import Any

from rich.console import Console

from benchmarks.reproduction.slotted import reference

from .collection import BenchmarkRequest, collect, plan_collection, resolve_requests
from .engines import Treatment
from .lmfao.optimizer import ROOT, seconds_summary
from .models import BenchmarkEndpoint, EndpointRequest
from .native_memory import native_memory_command
from .processes import terminate_process_group
from .reports.store import ReportStore, select_observations
from .targets import parse_target, sha256_file
from .workloads import resolve_files


def graph_size(binary: Path, path: Path, *, slotted: bool, timeout: int) -> dict[str, Any]:
    """Separate source-language nodes from implementation and substitution machinery."""
    diagnostic = path.with_name(path.stem + "-graph.egg")
    logical = path.with_name(path.stem + "-logical.json")
    diagnostic.write_text(path.read_text() + (f"\n(slotted-export {json.dumps(str(logical))})\n" if slotted else ""))
    command, env = native_memory_command(
        [
            str(binary),
            *(["--slotted"] if slotted else []),
            "--to-json",
            "--max-functions",
            "1000000",
            "--max-calls-per-function",
            "1000000",
            str(diagnostic),
        ],
        os.environ,
    )
    result = subprocess.run(command, env=env, capture_output=True, text=True, check=True, timeout=timeout)
    if "Omitted:" in result.stderr or "Truncated:" in result.stderr:
        raise RuntimeError("graph-size diagnostic was truncated")
    physical = json.loads(diagnostic.with_suffix(".json").read_text())
    source = json.loads(logical.read_text()) if slotted else physical
    operators = {
        f[1] for f in reference.parse(path.read_text()) if f[0] == "constructor" and f[1] not in ("Shift", "Subst")
    }
    nodes = list(source["nodes"].values()) if slotted else [n for n in source["nodes"].values() if n["op"] in operators]
    helpers = [n for n in physical["nodes"].values() if n["op"] in ("Shift", "Subst")]
    return {
        "source_nodes": len(nodes),
        "source_classes": len({n["eclass"] for n in nodes}),
        "explicit_scope_helper_nodes": len(helpers),
        "serialized_nodes": len(physical["nodes"]),
        "serialized_classes": len(physical["class_data"]),
    }


def optimize_programs(
    args: argparse.Namespace, programs: dict[str, tuple[Treatment, str]]
) -> tuple[dict[str, Any], dict[str, Any]]:
    if args.cpu is not None:
        os.sched_setaffinity(0, {args.cpu})
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    console = Console(stderr=True)
    request = parse_target(args.target)
    requests = []
    files = {}
    for mode, (treatment, source) in programs.items():
        path = out / f"{mode}.egg"
        path.write_text(source)
        files[mode] = resolve_files([str(path)], ROOT)[0]
        requests.append(BenchmarkRequest(EndpointRequest(request, treatment), (files[mode],)))
    store = ReportStore(args.report or out / "optimizer.jsonl")
    targets = resolve_requests(tuple(requests), store, args.rounds, args.timeout_sec, False, ROOT, ROOT, console)
    plans = plan_collection(store, tuple(requests), targets, args.rounds, args.timeout_sec, False)
    collect(store, plans, tuple(requests), targets, args.timeout_sec, console)
    target = targets[request]
    optimizer: dict[str, Any] = {}
    selected: dict[str, Any] = {}
    for mode, (treatment, source) in programs.items():
        endpoint = BenchmarkEndpoint(target.row, target.binary_sha256_for(treatment), treatment)
        observations = select_observations(store, endpoint, files[mode], args.rounds, args.timeout_sec)
        if observations.issue or any(row.record["status"] != "success" for row in observations.rows):
            raise RuntimeError(f"optimizer collection failed for {mode}")
        binary = target.binary_path_for(treatment)
        assert binary is not None
        command, env = native_memory_command(
            [str(binary), *(["--slotted"] if treatment == "slotted" else []), str(files[mode].absolute_path)],
            os.environ,
        )
        memory_path = out / f"{mode}-native-rss.txt"
        # Exec GNU time before forking the engine, so Python's footprint does not set its RSS floor.
        command = ["/usr/bin/time", "-f", "%M", "-o", str(memory_path), *command]
        process = subprocess.Popen(
            command, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True
        )
        try:
            stdout, stderr = process.communicate(timeout=args.timeout_sec)
            if process.returncode:
                raise subprocess.CalledProcessError(process.returncode, command, stdout, stderr)
        finally:
            terminate_process_group(process)
        extracted = reference.parse(stdout)[0]
        selected[mode] = extracted
        rss = [row.record["max_rss_bytes"] for row in observations.rows]
        assert all(value is not None for value in rss)
        memory = [value for value in rss if value is not None]
        optimizer[mode] = {
            "process_seconds": seconds_summary(
                row.record["wall_sec"] for row in observations.rows if row.record["wall_sec"] is not None
            ),
            "max_rss_bytes": {"median": statistics.median(memory), "min": min(memory), "max": max(memory)},
            "fresh_exec_max_rss_bytes": int(memory_path.read_text().strip()) * 1024,
            "graph": graph_size(
                binary, files[mode].absolute_path, slotted=treatment == "slotted", timeout=args.timeout_sec
            ),
            "rewrite_round_budget": sum(int(f[1]) for f in reference.parse(source) if f[0] == "run"),
            "binary_sha256": sha256_file(binary),
            "input_sha256": files[mode].sha256,
        }
    return optimizer, selected
