"""Run the fixed LMFAO batching case study through the shared optimizer collector."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
import time
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from benchmarking.config import DEFAULT_MEMORY_LIMIT_BYTES, DEFAULT_TIMEOUT_SEC
from benchmarking.native_memory import add_memory_limit_options

from . import model
from .batch import BatchExtractor, Graph
from .data import execute, load_data, reference_results, strong_baseline
from .optimizer import collect_optimizers, seconds_summary, write_json


def status(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


def run(args: argparse.Namespace) -> None:
    if args.cpu is not None:
        os.sched_setaffinity(0, {args.cpu})
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    documents, optimizer = collect_optimizers(out, args.samples, args.timeout, args.report, args.memory_limit_bytes)
    if "grouping-slotted" not in documents or "independent-slotted" not in documents:
        raise RuntimeError("the batching experiment requires original and rewritten egglog graphs")
    start = time.perf_counter()
    db, metadata = load_data(args.data)
    try:
        expected = reference_results(db)
        parsed = {name: Graph(doc, model.schema()[1]) for name, doc in documents.items()}
        source_rows = {}
        for g in parsed.values():
            for source_sql, _ in g.sources.values():
                if source_sql not in source_rows:
                    source_rows[source_sql] = db.execute(f"SELECT COUNT(*) FROM ({source_sql})").fetchall()[0][0]
        metadata.update(
            {
                "lmfao_commit": model.COMMIT,
                "cpu_affinity": sorted(os.sched_getaffinity(0)),
                "preparation_seconds": time.perf_counter() - start,
                "binary_sha256": optimizer["binary_sha256"],
                "optimizer_scope": "Fresh process, parsing and rewriting; "
                "export, comparison, extraction and execution excluded.",
                "timing_scope": "SQL planning, join, aggregation and output materialization; loading, statistics, "
                "e-graph processing, Python SQL generation, result fetching/checking and cleanup excluded.",
                "arithmetic": "DOUBLE timed weights; independent DECIMAL oracle; "
                "exact keys/counts, moments rtol=1e-9/atol=1e-7.",
                "dag_timeout_seconds": args.dag_timeout,
                "lowering_control": "The zero-round program is additionally compiled with global batching enabled. "
                "This is an explicitly labelled compiler control, not an e-graph result.",
                "representation": "The original named SDQL Sum queries; "
                "Batch, FusedBatch and GroupingBatch are introduced "
                "only by rewrites. The partial-aggregate tensor experiment is a separate representation.",
            }
        )
        write_json(out / "metadata.json", metadata)
        write_json(
            out / "statistics.json",
            {
                "sources": [{"sql": sql, "rows": rows} for sql, rows in source_rows.items()],
                "output_cardinalities": {i: len(rows) for i, rows in enumerate(expected)},
            },
        )
        plans = {"sql-grouping-sets": strong_baseline()}
        phase_plans: dict[str, Any] = {}
        aliases = {}
        controls = []
        for name, g in parsed.items():
            status(f"Extracting {name}")
            start = time.perf_counter()
            ex = BatchExtractor(
                g,
                {c: source_rows[sql] for c, (sql, _) in g.sources.items()},
                {i: len(rows) for i, rows in enumerate(expected)},
            )
            selected, info = ex.extract(dag_timeout=args.dag_timeout)
            info["extraction_seconds"] = time.perf_counter() - start
            info["source_graph_sha256"] = hashlib.sha256((out / f"{name}-graph.json").read_bytes()).hexdigest()
            for control in [False, True] if name == "independent-slotted" else [False]:
                label = name + ("-lowering-control" if control else "")
                start = time.perf_counter()
                statements, operators = ex.sql(selected, lowering_control=control)
                details = info | {
                    "operators": operators,
                    "lowering_control": control,
                    "lowering_seconds": time.perf_counter() - start,
                    "materialized_tables": sum(s.startswith("CREATE TEMP TABLE") for s in statements),
                }
                phase_plans[label] = {
                    "optimizer_variant": name,
                    "extraction_seconds": info["extraction_seconds"],
                    "sql_generation_seconds": details["lowering_seconds"],
                    "lowering_control": control,
                }
                write_json(out / f"{label}-plan.json", details)
                (out / f"{label}.sql").write_text(";\n\n".join(statements) + ";\n")
                if control:
                    controls.append((label, statements))
                    continue
                same = next((other for other, sql in plans.items() if sql == statements), None)
                if same is not None:
                    aliases[label] = same
                else:
                    plans[label] = statements
        # Prefer the extracted program's name when its SQL equals the compiler
        # control. Preserve both plans and explicitly alias the shared timing.
        for label, statements in controls:
            same = next((other for other, sql in plans.items() if sql == statements), None)
            if same is not None:
                aliases[label] = same
            else:
                plans[label] = statements
        write_json(out / "identical-sql.json", aliases)
        for label, sql in plans.items():
            (out / f"{label}.sql").write_text(";\n\n".join(sql) + ";\n")
        validation = {}
        for label, sql in plans.items():
            validation[label] = execute(db, sql, expected, model.queries())
            status(f"  {label}: all 140 outputs agree; {validation[label]['seconds']:.3f}s")
        write_json(out / "validation.json", validation)
        rows, labels = [], list(plans)
        with (out / "execution.jsonl").open("w") as stream:
            for repeat in range(args.samples):
                order = labels[repeat % len(labels) :] + labels[: repeat % len(labels)]
                if repeat % 2:
                    order.reverse()
                for label in order:
                    row = {"label": label, "repeat": repeat, **execute(db, plans[label], expected, model.queries())}
                    rows.append(row)
                    stream.write(json.dumps(row) + "\n")
                    stream.flush()
                    status(f"  sample {repeat + 1}/{args.samples} {label}: {row['seconds']:.3f}s")
        summary = {label: seconds_summary(r["seconds"] for r in rows if r["label"] == label) for label in labels}
        write_json(out / "summary.json", summary)
        for label, phases in phase_plans.items():
            phases["execution_label"] = aliases.get(label, label)
        report = {
            **optimizer,
            "preparation_seconds": metadata["preparation_seconds"],
            "plans": phase_plans,
            "execution": summary,
            "execution_scope": metadata["timing_scope"],
            "phase_scope": "Extraction and Python SQL generation are single observations per plan. "
            "Optimizer and execution samples are separate; their medians are not a measured end-to-end time.",
        }
        write_json(out / "pipeline.json", report)
        print(json.dumps(report, indent=2))
    finally:
        db.close()


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, required=True, help="Pinned upstream data/favorita-small directory")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--rounds", "--samples", dest="samples", type=int, default=5, help="Measured executions, not rewrite rounds"
    )
    parser.add_argument("--timeout-sec", "--timeout", dest="timeout", type=int, default=DEFAULT_TIMEOUT_SEC)
    parser.add_argument(
        "--report", type=Path, help="Shared append-only optimizer cache; default OUTPUT/optimizer.jsonl"
    )
    add_memory_limit_options(parser, default=DEFAULT_MEMORY_LIMIT_BYTES)
    parser.add_argument("--dag-timeout", type=float, default=30, help="DAG solver budget; 0 uses the heuristic")
    parser.add_argument("--cpu", type=int)
    args = parser.parse_args(argv)
    if args.report == Path("-"):
        parser.error("--report requires a filesystem path, not '-'")
    if args.samples < 1 or args.timeout < 1:
        parser.error("rounds and timeout must be positive")
    if not math.isfinite(args.dag_timeout) or args.dag_timeout < 0:
        parser.error("DAG timeout must be finite and nonnegative")
    args.output_dir = args.output_dir.resolve()
    args.data = args.data.resolve()
    if args.report is not None:
        args.report = args.report.resolve()
    run(args)
    return 0
