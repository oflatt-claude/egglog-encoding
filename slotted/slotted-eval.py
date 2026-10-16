#!/usr/bin/env python3
"""Run the paper's array and SDQL evaluations.

    ./bench.py slotted array --params 0
    ./bench.py slotted sdql --kernel mmm --phase 1st
    ./bench.py slotted --jobs 4 --report /tmp/eval.jsonl
    ./bench.py slotted --from /tmp/eval.jsonl

The flow is prepare inputs -> reuse or collect -> check -> cache -> report.
Each side gets one timed goal check and a separate, untimed graph export.
Default execution is serial, with release binaries, a 300-second process timeout,
and the paper's rewrite budgets. Parallel timings include resource contention.

Workload generation is in eval_workloads; subprocess timing is in eval_run.
Graph export, raw counts, and verified isomorphism checks are in eval_verify.
The exact pairs are encoding/ref-multi and encoding-no-aliasing/ref-nested-snapshot;
ref-nested keeps the paper's syntactic substitution as a timing baseline.
Missing evidence fails the correctness gate. --no-counts opts into timing/goals only.

All observations share the proof benchmark's ReportStore through eval_cache;
benchmarking.reports.slotted builds the same tables and checks for the CLI and nightly.
See ENCODING.md for comparison policies and limitations.
"""

import argparse
import multiprocessing
import signal
import subprocess
import sys
import time
import traceback
from dataclasses import asdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]

import paper_fixtures as pf  # noqa: E402
from eval_cache import Cache  # noqa: E402
from eval_observation import Row  # noqa: E402
from eval_run import GROUP_CAP, Config, Progress, build, run_egglog, run_reference  # noqa: E402

from benchmarking.reports.render import render_html_report_document, render_markdown_report_document  # noqa: E402
from benchmarking.reports.slotted import SIDES, slotted_report  # noqa: E402
from benchmarking.reports.store import ReportStore  # noqa: E402

REPORT = Path(".reports.jsonl")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("study", nargs="?", default="all", choices=("all", "array", "sdql"))
    ap.add_argument("--side", default="all", help="comma-separated subset of " + ",".join(SIDES))
    ap.add_argument(
        "--nested-compat",
        action="store_true",
        help="shorthand: select encoding-no-aliasing instead of encoding and ref-nested-snapshot instead of ref-nested",
    )
    ap.add_argument("--params", type=int, nargs="*", default=[0, 1, 2], help="array: extra function parameters")
    ap.add_argument(
        "--rounds", type=int, default=None, help="iterations; default 6 for array, the artifact's limit for sdql"
    )
    ap.add_argument(
        "--kernel",
        nargs="*",
        default=list(pf.KERNELS),
        choices=pf.KERNELS,
        help="sdql: kernels to run",
    )
    ap.add_argument(
        "--phase",
        nargs="*",
        default=list(pf.PHASES),
        choices=pf.PHASES,
        help="sdql: compiler phases to run",
    )
    ap.add_argument(
        "--rules",
        type=int,
        default=44,
        choices=(12, 44),
        help="sdql: the full set, or the suite's goal-directed BATAX second-phase subset",
    )
    ap.add_argument(
        "--counts",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="count the final e-graphs' classes and nodes at the requested round budget, and compare"
        " the encoding's graph with each reference side's (isomorphic, different, or inconclusive);"
        " require verified equality for encoding/ref-multi and encoding-no-aliasing/ref-nested-snapshot"
        " when both sides of a pair are selected",
    )
    ap.add_argument(
        "--group-cap",
        type=int,
        default=GROUP_CAP,
        help="maximum live slots the oracle enumerates a symmetry group over when dumping;"
        " raising this limit has factorial cost (default %(default)s)",
    )
    ap.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="seconds per benchmark or graph-dump subprocess (default: 300); "
        "Python graph checks have no wall-clock limit",
    )
    ap.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="maximum concurrent workloads (default: 1, serial); parallel timings include contention",
    )
    ap.add_argument(
        "--report",
        "--jsonl",
        dest="jsonl",
        type=Path,
        default=REPORT,
        help=f"record one JSON object per run here (default {REPORT.name})",
    )
    ap.add_argument(
        "--from",
        dest="report",
        type=Path,
        nargs="?",
        const=REPORT,
        help=f"print the table from a record instead of running (default {REPORT.name})",
    )
    ap.add_argument("--html", type=Path, help="also write the table as an HTML page here")
    ap.add_argument("--no-build", action="store_true", help="skip `cargo build`; the binaries are known current")
    ap.add_argument(
        "--force-run", action="store_true", help="append fresh observations instead of reusing exact cached results"
    )
    args = ap.parse_args(argv)
    if str(args.jsonl) == "-":
        ap.error("--report requires a filesystem path")
    if args.jobs < 1:
        ap.error("--jobs must be at least 1")

    config = Config(group_cap=args.group_cap)
    sides = SIDES if args.side == "all" else tuple(s.strip() for s in args.side.split(","))
    bad = [s for s in sides if s not in SIDES]
    if bad:
        ap.error(f"unknown side {bad}; choose from {SIDES}")
    if args.nested_compat:
        aliases = {"encoding": "encoding-no-aliasing", "ref-nested": "ref-nested-snapshot"}
        sides = tuple(dict.fromkeys(aliases.get(s, s) for s in sides))

    try:
        if args.report:
            records = ReportStore(args.report.expanduser()).records
            if args.study != "all":
                records = [r for r in records if "slotted" in r and r["slotted"]["study"] == args.study]
            print(f"{args.report}: latest cached workload versions", file=sys.stderr)
        else:
            records = collect(args, sides, ap, config=config)
        report = slotted_report(records, sides=sides, counts=args.counts)
        print(render_markdown_report_document(report.catalog))
        if args.html:
            cache_path = args.report or args.jsonl
            if args.html.resolve() == cache_path.resolve():
                raise ValueError("HTML output must differ from the JSONL report path")
            args.html.write_text(render_html_report_document(report.catalog))
            print(f"wrote {args.html}", file=sys.stderr)
        return 1 if report.errors else 0
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"slotted evaluation failed: {error}", file=sys.stderr)
        return 2
    except Exception:
        # Preserve programming errors as tracebacks, with the collection-error status.
        traceback.print_exc()
        return 2


def collect_workload(workload, args, sides, config, progress):
    """One timing run per side; collect untimed evidence and then compare the group."""
    import eval_verify as verification

    rows = []
    for side in sides:
        row = Row(workload.study, workload.case, side, workload.rounds, workload.rules)
        row.paper, row.jobs = workload.paper, args.jobs
        if side.startswith("ref-"):
            run_reference(workload.reference(side), row, args.timeout, progress, config=config)
        else:
            run_egglog(workload.program, workload.case, row, args.timeout, progress, config=config)
        if args.counts:
            verification.collect_graph(workload, row, args.timeout, progress, config=config)
        progress(row, "done")
        rows.append(row)
    if args.counts:
        verification.compare(rows, progress)
    for row in rows:
        # Comparisons are finished. Do not retain or send large graphs to the parent.
        row.graph = None
    return rows


def stop_worker(_signum, _frame):
    # Unwind subprocess.run and scratch-file finally blocks when the pool is stopped.
    raise SystemExit(0)


def init_worker():
    # The parent handles Ctrl-C by terminating the pool; workers clean up their children.
    signal.signal(signal.SIGINT, signal.SIG_IGN)


def parallel_workload(payload):
    workload, args, sides, config = payload
    # Only unwind our own work. Idle workers must use the default SIGTERM handler:
    # raising while multiprocessing waits on a queue lock can hang pool shutdown.
    previous = signal.signal(signal.SIGTERM, stop_worker)
    try:
        with Progress(parallel=True) as progress:
            return collect_workload(workload, args, sides, config, progress)
    finally:
        signal.signal(signal.SIGTERM, previous)


def collect(args, sides, ap, *, config=None):
    """Build both sides and run the requested workloads: the rows a report is made of."""
    import eval_workloads as workloads

    started = time.perf_counter()
    config = config or Config()
    tasks = []
    if args.study in ("all", "array"):
        tasks += [("array", n) for n in args.params]
    if args.study in ("all", "sdql"):
        selected = [w for w in pf.WORKLOADS if w[0] in args.kernel and w[1] in args.phase]
        if args.rules == 12 and selected != [("batax", "2nd")]:
            ap.error("--rules 12 is the suite's BATAX second-phase subset: use --kernel batax --phase 2nd")
        tasks += [("sdql", w) for w in selected]
    if not args.no_build:
        build()
    for tool in (config.egglog, config.xmulti):
        if not tool.exists():
            ap.error(f"missing {tool.relative_to(ROOT)}; run without --no-build")
    print(f"egglog {config.egglog.relative_to(ROOT)}   xmulti {config.xmulti.relative_to(ROOT)}", file=sys.stderr)
    print("Samples: " + ", ".join(sides), file=sys.stderr)
    print(
        f"One dot per completed sample; slow phases shown after {Progress.delay}s. "
        f"Timeout: {args.timeout}s per process.",
        file=sys.stderr,
        flush=True,
    )

    prepared = {task: workloads.prepare(task, rounds=args.rounds, rules=args.rules) for task in tasks}
    manifests = {task: asdict(workload) for task, workload in prepared.items()}
    cache = Cache(args.jsonl.expanduser(), ROOT, config, args, manifests)
    rows_by_task = {}
    pending = []
    for task in tasks:
        reused = cache.reuse(task, sides)
        if reused is None:
            pending.append(task)
        else:
            rows_by_task[task] = reused
    print(f"Workloads: {len(rows_by_task)} cached, {len(pending)} to collect.", file=sys.stderr)

    def accept(task, group):
        rows_by_task[task] = cache.append(task, group)

    if args.jobs == 1:
        with Progress() as progress:
            for task in pending:
                accept(task, collect_workload(prepared[task], args, sides, config, progress))
    elif pending:
        workers = min(args.jobs, len(pending))
        print(
            f"Parallel workers: {workers} (limit {args.jobs}); dots follow completion order. "
            "Timings include contention.",
            file=sys.stderr,
            flush=True,
        )
        # Separate processes let Python graph checks use multiple cores too.
        context = multiprocessing.get_context("spawn")
        with context.Pool(workers, initializer=init_worker) as pool:
            payloads = ((prepared[task], args, sides, config) for task in pending)
            for task, group in zip(pending, pool.imap(parallel_workload, payloads), strict=True):
                accept(task, group)
            # On success let idle workers return normally. Pool.__exit__ terminates
            # them while queue locks may be held; signal-driven unwinding can hang.
            pool.close()
            pool.join()
        print(file=sys.stderr, flush=True)
    rows = [row for task in tasks for row in rows_by_task[task]]
    elapsed = int(time.perf_counter() - started)
    print(
        f"Selected {len(rows)} samples in {elapsed // 60}m {elapsed % 60:02d}s (build + runs + checks).",
        file=sys.stderr,
    )
    return rows


if __name__ == "__main__":
    sys.exit(main())
