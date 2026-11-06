"""Subprocess entrypoint called by LMFAO's logical-optimizer hook."""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from benchmarking.workloads import resolve_files
from benchmarks.reproduction.slotted.lmfao import frozen

from . import model
from .logical import Extractor, Graph
from .optimizer import ROOT, export_graph, write_json


def run(config: dict[str, Any], source: Path, destination: Path) -> None:
    out = destination.parent
    phases = {}
    start = time.perf_counter()
    definition = model.Workload.read(source)
    if definition.document != model.WORKLOAD.document:
        raise ValueError("LMFAO frontend differs from the frozen benchmark workload; regenerate explicitly")
    files = frozen(modes=(config["variant"],), definition=definition)
    for name, contents in files.items():
        (out / name).write_text(contents)
    manifest = json.loads(files["manifest.json"])
    file = resolve_files([str(out / manifest["variants"][0]["file"])], ROOT)[0]
    phases["translation"] = time.perf_counter() - start
    start = time.perf_counter()
    document = export_graph(
        Path(config["binary"]),
        file,
        config["treatment"],
        out / "graph.json",
        manifest["export_names"],
        config["timeout"],
        config["memory_limit_bytes"],
    )
    phases["rewriting_and_export"] = time.perf_counter() - start
    start = time.perf_counter()
    graph = Graph(document, definition)
    phases["graph_decoding"] = time.perf_counter() - start
    start = time.perf_counter()
    extractor = Extractor(graph)
    selected, info = extractor.extract(config["dag_timeout"])
    phases["extraction"] = time.perf_counter() - start
    start = time.perf_counter()
    plan = extractor.plan(selected)
    write_json(destination, plan)
    phases["plan_serialization"] = time.perf_counter() - start
    info.update(
        phases_seconds=phases,
        source_workload_sha256=sha256_file(source),
        source_graph_sha256=sha256_file(out / "graph.json"),
        views=len(plan["views"]),
        aggregates=sum(len(v["aggregates"]) for v in plan["views"]),
    )
    write_json(out / "extraction.json", info)


if __name__ == "__main__":
    settings, source, destination = map(Path, sys.argv[1:])
    run(json.loads(settings.read_text()), source, destination)
