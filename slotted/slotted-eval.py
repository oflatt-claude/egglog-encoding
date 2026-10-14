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
eval_report renders the two timing summaries and full evidence table.
See ENCODING.md for comparison policies and limitations.
"""

import argparse
import multiprocessing
import signal
import sys
import time
from dataclasses import asdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]

import eval_verify as verification  # noqa: E402
import eval_workloads as workloads  # noqa: E402
from eval_cache import Cache, load_rows  # noqa: E402
from eval_report import SIDES, Progress, Row, html, markdown_report, report_sections  # noqa: E402
from eval_run import GROUP_CAP, Config, build, run_egglog, run_reference  # noqa: E402

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
        default=list(workloads.pf.KERNELS),
        choices=workloads.pf.KERNELS,
        help="sdql: kernels to run",
    )
    ap.add_argument(
        "--phase",
        nargs="*",
        default=list(workloads.pf.PHASES),
        choices=workloads.pf.PHASES,
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
    ap.add_argument("--long", action="store_true", help="one row per run with every field, instead of the timing pivot")
    ap.add_argument("--merged", action="store_true", help=argparse.SUPPRESS)
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

    if args.report:
        # reporting alone: the rows come from an earlier run's record
        rows, when = load_rows(args.report, args.merged)
        rows = [r for r in rows if r.side in sides]
        print(f"{args.report}: latest cached observations (through {when})", file=sys.stderr)
        if args.study != "all":
            rows = [r for r in rows if r.study == args.study]
        if args.side == "all":
            sides = tuple(s for s in sides if any(r.side == s for r in rows))
    else:
        rows = collect(args, sides, ap, config=config)

    errors = verification.failures(rows, sides, args.counts)
    sections = report_sections(rows, sides, args.long, counts=args.counts)
    print(markdown_report(sections, errors))
    if args.html:
        args.html.write_text(html(sections, errors))
        print(f"wrote {args.html}", file=sys.stderr)
    return 1 if errors else 0


def nightly(report_path, *, env=None, timeout=150, jobs=1):
    """Populate the shared report cache using the paper's rewrite budgets."""
    build(env=env)
    return main(
        [
            "--no-build",
            "--timeout",
            str(timeout),
            "--jobs",
            str(jobs),
            "--params",
            "0",
            "1",
            "2",
            "3",
            "--report",
            str(report_path),
        ]
    )


def collect_workload(workload, args, sides, config, progress):
    """One timing run per side; collect untimed evidence and then compare the group."""
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
    started = time.perf_counter()
    config = config or Config()
    tasks = []
    if args.study in ("all", "array"):
        tasks += [("array", n) for n in args.params]
    if args.study in ("all", "sdql"):
        selected = [w for w in workloads.pf.WORKLOADS if w[0] in args.kernel and w[1] in args.phase]
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
    cache = None
    if getattr(args, "jsonl", None) is not None:
        manifests = {task: asdict(workload) for task, workload in prepared.items()}
        cache = Cache(args.jsonl, ROOT, config, args, manifests)
    rows_by_task = {}
    pending = []
    for task in tasks:
        reused = cache.reuse(task, sides) if cache else None
        if reused is None:
            pending.append(task)
        else:
            rows_by_task[task] = reused
    print(f"Workloads: {len(rows_by_task)} cached, {len(pending)} to collect.", file=sys.stderr)

    def accept(task, group):
        if cache:
            cache.append(task, group)
        rows_by_task[task] = group

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
