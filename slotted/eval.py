#!/usr/bin/env python3
"""The paper's case studies, from one command.

Schneider et al., *Slotted E-Graphs* (PLDI 2025) evaluates on two languages this
repository carries: the S4.1 functional array language, rewriting (A) into (B) with N
extra function parameters, and the S4.2 SDQL compiler, whose ten Table 1 workloads --
five kernels, two compiler phases each -- `slotted/paper_fixtures.py` carries from the
artifact. This runs each on up to three SIDES and reports the paper's criterion -- was
the target reached within the iteration budget -- with the time it took and, on
request, the size of the e-graph it built beside Table 1's:

    encoding    the egglog slotted encoding, `slotted/slotted-encoder.py`
    ref-multi   the reference crate through `MultiPattern`, the pattern language the
                encoding implements and the harness's oracle
    ref-nested  the reference crate through nested `Rewrite`/`ematch_all`, the matcher
                the paper's own experiments ran; incomplete on redundant slots, so it
                can reach less than `ref-multi`

Usage:
    python3 slotted/eval.py                         both studies, every side, paper budgets
    python3 slotted/eval.py array --params 0 1 2 3  the array goal with 0..3 parameters
    python3 slotted/eval.py sdql                    all ten SDQL workloads, all 44 rules
    python3 slotted/eval.py sdql --kernel ttm mmm --phase 1st
    python3 slotted/eval.py sdql --kernel batax --phase 2nd --rules 12
                                                    the suite's goal-directed BATAX subset
    python3 slotted/eval.py --side encoding,ref-nested --counts --jsonl eval.jsonl
    python3 slotted/eval.py sdql --phase 1st --html eval.html   the table as a page too
    python3 slotted/eval.py --from eval.jsonl                    the table again, from the record

Budgets default to the paper's: 6 iterations for the array goal, and for SDQL the
artifact runner's per-workload limit (13 for BATAX's first phase, 12 for its second, 30
for the rest); `--rounds` overrides them all. `--timeout` defaults to the artifact's
300 s per run. Both binaries are built in release first, the oracle without the crate's
`checks` feature, since the differential harness uses debug, checked builds and those
numbers mean nothing; `--no-build` skips that when they are known current. Each
reference row says which oracle answered. The table on stdout has one row per workload and
one column per side, holding that side's seconds when it reached the goal and what
happened otherwise; `--long` gives one row per run with every field instead, `--html`
writes the table as a page too, and `--jsonl` appends one JSON object per run to a file,
which is what a graph should be drawn from. `--from FILE` prints the table from such a
file without running anything, the latest record per workload and side, so collection
and reporting are separate steps.
"""

import argparse
import contextlib
import datetime
import importlib.util
import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "slotted"))
sys.path.insert(0, str(ROOT / "slotted" / "xdiff"))

import isomorphism as ISO  # noqa: E402
import xarray as XA  # noqa: E402

sc = __import__("slotted-egglog")
slotenc = __import__("slotted-encoder")
pf = __import__("paper_fixtures")

_spec = importlib.util.spec_from_file_location("cps", ROOT / "slotted" / "checks" / "check-paper-sdql.py")
cps = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cps)

SIDES = ("encoding", "ref-multi", "ref-nested")
SCRATCH = ROOT / "target" / "slotted"


#: Release builds of both sides: egglog, and the reference through `xmulti` without the
#: crate's `checks` feature, the way the paper's experiments ran it.
EGGLOG = ROOT / "target" / "release" / "egglog"
XMULTI = ROOT / "slotted" / "xmulti" / "target" / "release" / "xmulti"
BUILDS = (
    ("cargo", "build", "--release", "--bin", "egglog"),
    ("cargo", "build", "--release", "--no-default-features", "--manifest-path", "slotted/xmulti/Cargo.toml"),
)


def build():
    """Bring both binaries up to date, so a timing is of the code in the checkout.
    cargo's own output stays on stderr."""
    for cmd in BUILDS:
        if subprocess.run(cmd, cwd=ROOT, stdout=sys.stderr).returncode != 0:
            sys.exit(f"eval.py: `{' '.join(cmd)}` failed")


class Row:
    def __init__(self, study, case, side, rounds, rules=None):
        self.study, self.case, self.side, self.rounds, self.rules = study, case, side, rounds, rules
        self.goal, self.saturated, self.seconds = "?", "?", None
        self.classes, self.nodes = None, None
        self.checks = None  # the oracle's `CONFIG checks=` answer, for reference sides
        self.paper = None  # Table 1's slotted row for this workload, when it has one

    def as_dict(self):
        d = dict(vars(self))
        d["egglog"] = str(EGGLOG.relative_to(ROOT))
        d["xmulti"] = str(XMULTI.relative_to(ROOT))
        d["date"] = datetime.datetime.now().isoformat(timespec="seconds")
        return d

    @classmethod
    def from_dict(cls, d):
        """A row back from its `--jsonl` record."""
        row = cls(d["study"], d["case"], d["side"], d["rounds"], d.get("rules"))
        for field in ("goal", "saturated", "seconds", "classes", "nodes", "checks"):
            setattr(row, field, d.get(field, getattr(row, field)))
        row.paper = tuple(d["paper"]) if d.get("paper") is not None else None
        return row


def load_rows(path):
    """Every run recorded in a `--jsonl` file, the latest per workload and side kept,
    in the order they first appeared."""
    latest, order = {}, []
    with path.open() as f:
        for line in f:
            if not line.strip():
                continue
            row = Row.from_dict(json.loads(line))
            key = (row.study, row.case, row.rounds, row.rules, row.side)
            if key not in latest:
                order.append(key)
            latest[key] = row
    return [latest[key] for key in order]


# ------------------------------------------------------------------ the reference
def run_reference(spec, row, timeout, counts):
    """One `xmulti` run: the GOAL line is the criterion, the dump gives the counts."""
    if counts:
        spec += "dump\n"
    t0 = time.time()
    try:
        r = subprocess.run([str(XMULTI)], input=spec, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.time() - t0
        return
    row.seconds = time.time() - t0
    lines = r.stdout.splitlines()
    if r.returncode != 0 and "REFERENCE_LIMIT:" not in r.stderr:
        row.goal = "error: " + ((r.stderr.strip().splitlines() or ["?"])[-1])[:80]
        return
    row.goal = next((ln.split()[1] for ln in lines if ln.startswith("GOAL ")), "?")
    row.saturated = next((ln.split()[1] for ln in lines if ln.startswith("SATURATED ")), "?")
    row.checks = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG checks=")), None)
    if counts:
        # a symmetry group too large to enumerate leaves the counts unknown
        with contextlib.suppress(ValueError):
            row.classes, row.nodes = ISO.parse_reference(r.stdout).summary()


def rule_lines(lang, rules_path, selected, nested):
    """A rule file's rules as oracle spec lines, flattened or nested."""
    src = sc.Source(rules_path)
    out = []
    for form in sc.parse(rules_path.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        r = sc.rewrite_parts(src, form)
        if selected is not None and r["name"] not in selected:
            continue
        lhs = src.term(r["lhs"], ground=False)
        rhs = slotenc.pat_sexpr(lang, slotenc.rhs_of(lang, src.term(r["rhs"], ground=False)))
        if nested:
            out += ["rule", f"nested {slotenc.pat_sexpr(lang, slotenc.rhs_of(lang, lhs))}", f"rhs root {rhs}"]
        else:
            root, atoms = slotenc.flatten(lang, lhs)
            root, atom_text = slotenc.atom_lines(lang, root, atoms)
            out += ["rule", *atom_text, f"rhs {root} {rhs}"]
        for want, slot, pvars in r["conds"]:
            out.append(f"cond {'in' if want else 'notin'} {slot} {' '.join(pvars)}")
    return out


# ------------------------------------------------------------------- the encoding
def run_egglog(program, name, row, timeout, goal_of):
    """Run one egglog program; `goal_of(result)` reads the criterion off it."""
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{name}-{os.getpid()}.egg"
    path.write_text(program)
    t0 = time.time()
    try:
        r = subprocess.run([str(EGGLOG), str(path)], capture_output=True, text=True, cwd=ROOT, timeout=timeout)
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.time() - t0
        return
    finally:
        path.unlink(missing_ok=True)
    row.seconds = time.time() - t0
    row.goal = goal_of(r)


def encoding_counts(program, name, lang, row, timeout):
    """Classes and nodes of the encoding's final graph, read as the isomorphism checker reads it."""
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{name}-{os.getpid()}-counts.egg"
    jpath = path.with_suffix(".json")
    path.write_text(program)
    try:
        r = subprocess.run(
            [str(EGGLOG), "--to-json", *ISO.SERIALIZE_LIMITS, str(path)],
            capture_output=True,
            text=True,
            cwd=ROOT,
            timeout=timeout,
        )
        if r.returncode != 0 or ISO.incomplete_serialization(r.stderr) or not jpath.exists():
            return
        ISO.use_language(lang)
        g, issues = ISO.build_encoding_graph(json.loads(jpath.read_text()))
        if not issues:
            row.classes, row.nodes = g.summary()
    except (subprocess.TimeoutExpired, Exception):  # noqa: BLE001 -- counts are best effort
        return
    finally:
        path.unlink(missing_ok=True)
        jpath.unlink(missing_ok=True)


# ------------------------------------------------------------------ the array study
def array_rows(params, rounds, sides, counts, timeout):
    for n in params:
        case = XA.goal_cases([n], rounds=rounds)[0]
        a, b = case.probes
        head = [f"rounds {rounds}", f"term {XA.sexpr(a)}"]
        goal = [f"goal {XA.sexpr(b)}"]
        for side in sides:
            row = Row("array", case.name, side, rounds)
            if side == "ref-multi":
                lines = [ln for r in case.rules for ln in r.spec_lines()]
                run_reference("\n".join(head + lines + goal) + "\n", row, timeout, counts)
            elif side == "ref-nested":
                lines = rule_lines(XA.LANG, XA.ARRAY_SRC_RULES, None, nested=True)
                run_reference("\n".join(head + lines + goal) + "\n", row, timeout, counts)
            else:
                prog = XA.egg_program(case, mult=1, defer_probes=True)
                probes = len(case.probes)

                def goal_of(r, k=probes):
                    if r.returncode != 0:
                        return "error"
                    return "yes" if XA.parse_same_class(r.stdout, k).startswith("[0,1]") else "no"

                run_egglog(prog, case.name, row, timeout, goal_of)
                if counts:
                    bare = XA.Case(case.name, case.terms, case.rules, [], rounds=rounds)
                    prog = XA.egg_program(bare, mult=1).replace("(print-function SameClass 100000)", "")
                    encoding_counts(prog, case.name, XA.LANG, row, timeout)
            yield row


# ------------------------------------------------------------------- the SDQL study
def sdql_program(kernel, phase, rules, rounds, with_target):
    """One workload as a slotted source: the full library by include, or BATAX's own 12."""
    if rules == 12:
        # the goal-directed test, its own rules and schedule; only its terms are reused
        forms = sc.parse(cps.TEST.read_text())
        forms = [["run", str(rounds)] if f[:1] == ["run"] and f[1] != "0" else f for f in forms]
    else:
        forms = pf.test_forms(kernel, phase, rounds)
    if not with_target:
        # the saturated input alone, for counting: no target, no check
        forms = [f for f in forms if f[0] != "check" and f[:2] != ["let", "paper-target"]]
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{kernel}_{phase}-{rules}-{'goal' if with_target else 'counts'}-{os.getpid()}.egg"
    path.write_text("\n".join(sc.render(f) for f in forms) + "\n")
    try:
        return sc.compile_source(sc.Source(path))
    finally:
        path.unlink(missing_ok=True)


def sdql_rows(workloads, rules, rounds, sides, counts, timeout):
    lang = pf.reference_language()
    source = sc.Source(pf.RULES)
    for kernel, phase in workloads:
        start, target = pf.workload_text(kernel, phase, source, lang)
        budget = rounds or pf.iteration_limit(kernel, phase)
        selected = cps.SELECTED_RULES if rules == 12 else None
        head = [f"rounds {budget}", f"term {start}"]
        goal = [f"goal {target}"]
        name = f"{kernel}_{phase}-{rules}rules"
        for side in sides:
            row = Row("sdql", name, side, budget, rules)
            row.paper = pf.TABLE1[(kernel, phase)]
            if side.startswith("ref-"):
                lines = rule_lines(lang, pf.RULES, selected, nested=(side == "ref-nested"))
                run_reference("\n".join(head + lines + goal) + "\n", row, timeout, counts)
            else:

                def goal_of(r):
                    if r.returncode == 0:
                        return "yes"
                    return "no" if "(check" in r.stderr else "error"

                run_egglog(sdql_program(kernel, phase, rules, budget, True), name, row, timeout, goal_of)
                if counts:
                    encoding_counts(sdql_program(kernel, phase, rules, budget, False), name, lang, row, timeout)
            yield row


# ------------------------------------------------------------------------- output
LONG_HEAD = (
    "study",
    "case",
    "side",
    "rounds",
    "goal",
    "saturated",
    "seconds",
    "classes",
    "nodes",
    "paper (iters, nodes, classes, sat.)",
)


def paper_cell(r):
    return "" if r.paper is None else f"{r.paper[0]}, {r.paper[1]:,}, {r.paper[2]:,}, {'yes' if r.paper[3] else 'no'}"


def long_cells(r):
    """One row's cells, as text, in `LONG_HEAD` order: the record of one run."""
    secs = "" if r.seconds is None else f"{r.seconds:.1f}"
    side = r.side if r.checks is None else f"{r.side} (checks {r.checks})"
    counts = [str(r.classes or ""), str(r.nodes or "")]
    return [r.study, r.case, side, str(r.rounds), r.goal, r.saturated, secs, *counts, paper_cell(r)]


def timing_cell(r):
    """How one side did on one workload: its seconds when it reached the goal, and
    otherwise what happened, with the seconds it spent; counts follow when asked for."""
    secs = "" if r.seconds is None else f"{r.seconds:.1f}"
    cell = secs if r.goal == "yes" else (f"{r.goal} ({secs})" if secs and r.goal in ("no", "error") else r.goal)
    if r.classes is not None:
        cell += f" [{r.classes}/{r.nodes}]"
    return cell


def pivot(rows, sides):
    """One row per workload, one column per side, holding that side's timing."""
    labels = {}
    for r in rows:
        labels.setdefault(r.side, set()).add("" if r.checks is None else f" (checks {r.checks})")
    columns = [s + ("".join(labels[s]) if s in labels and len(labels[s]) == 1 else "") for s in sides]
    head = ["study", "case", "rounds", *columns, "paper (iters, nodes, classes, sat.)"]
    by_case, order = {}, []
    for r in rows:
        key = (r.study, r.case, r.rounds)
        if key not in by_case:
            by_case[key] = {"paper": paper_cell(r)}
            order.append(key)
        by_case[key][r.side] = timing_cell(r)
    table = []
    for study, case, rounds in order:
        got = by_case[(study, case, rounds)]
        table.append([study, case, str(rounds), *(got.get(s, "") for s in sides), got["paper"]])
    return head, table


def markdown(head, table):
    """A Markdown table with its columns padded, so it also reads aligned in a terminal."""
    table = [list(head)] + table
    widths = [max(len(row[i]) for row in table) for i in range(len(head))]

    def line(cells):
        return "| " + " | ".join(c.ljust(w) for c, w in zip(cells, widths, strict=True)) + " |"

    rule = "|" + "|".join("-" * (w + 2) for w in widths) + "|"
    return "\n".join([line(table[0]), rule] + [line(c) for c in table[1:]])


def html(head, table):
    """The same table as a standalone page."""
    import html as h

    head_cells = "".join(f"<th>{h.escape(c)}</th>" for c in head)
    body = "\n".join("<tr>" + "".join(f"<td>{h.escape(c)}</td>" for c in cells) + "</tr>" for cells in table)
    return (
        "<!doctype html><meta charset=utf-8><title>slotted eval</title>"
        "<style>body{font:14px system-ui,sans-serif;margin:2em}table{border-collapse:collapse}"
        "th,td{border:1px solid #bbb;padding:4px 10px;text-align:left;white-space:nowrap}"
        "th{background:#eee}tr:nth-child(even){background:#f7f7f7}</style>"
        f"<table><thead><tr>{head_cells}</tr></thead><tbody>\n{body}\n</tbody></table>\n"
    )


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("study", nargs="?", default="all", choices=("all", "array", "sdql"))
    ap.add_argument("--side", default="all", help="comma-separated subset of encoding,ref-multi,ref-nested")
    ap.add_argument("--params", type=int, nargs="*", default=[0, 1, 2], help="array: extra function parameters")
    ap.add_argument(
        "--rounds", type=int, default=None, help="iterations; default 6 for array, the artifact's limit for sdql"
    )
    ap.add_argument("--kernel", nargs="*", default=list(pf.KERNELS), choices=pf.KERNELS, help="sdql: kernels to run")
    ap.add_argument(
        "--phase", nargs="*", default=list(pf.PHASES), choices=pf.PHASES, help="sdql: compiler phases to run"
    )
    ap.add_argument(
        "--rules",
        type=int,
        default=44,
        choices=(12, 44),
        help="sdql: the full set, or the suite's goal-directed BATAX second-phase subset",
    )
    ap.add_argument("--counts", action="store_true", help="also count the final e-graph's classes and nodes")
    ap.add_argument("--timeout", type=int, default=300, help="seconds per run; the artifact's own budget")
    ap.add_argument("--jsonl", type=Path, help="append one JSON object per row here")
    ap.add_argument("--from", dest="report", type=Path, help="print the table from this JSONL instead of running")
    ap.add_argument("--html", type=Path, help="also write the table as an HTML page here")
    ap.add_argument("--long", action="store_true", help="one row per run with every field, instead of the timing pivot")
    ap.add_argument("--no-build", action="store_true", help="skip `cargo build`; the binaries are known current")
    args = ap.parse_args()

    sides = SIDES if args.side == "all" else tuple(s.strip() for s in args.side.split(","))
    bad = [s for s in sides if s not in SIDES]
    if bad:
        ap.error(f"unknown side {bad}; choose from {SIDES}")

    if args.report:
        # reporting alone: the rows come from an earlier run's record
        rows = [r for r in load_rows(args.report) if r.side in sides]
        if args.study != "all":
            rows = [r for r in rows if r.study == args.study]
        if args.side == "all":
            sides = tuple(s for s in SIDES if any(r.side == s for r in rows))
    else:
        rows = collect(args, sides, ap)

    head, table = (LONG_HEAD, [long_cells(r) for r in rows]) if args.long else pivot(rows, sides)
    print(markdown(head, table))
    if args.html:
        args.html.write_text(html(head, table))
        print(f"wrote {args.html}", file=sys.stderr)
    if args.jsonl and not args.report:
        with args.jsonl.open("a") as f:
            for r in rows:
                f.write(json.dumps(r.as_dict()) + "\n")
    return 0 if all(r.goal == "yes" for r in rows) else 1


def collect(args, sides, ap):
    """Build both sides and run the requested workloads: the rows a report is made of."""
    if not args.no_build:
        build()
    for tool in (EGGLOG, XMULTI):
        if not tool.exists():
            ap.error(f"missing {tool.relative_to(ROOT)}; run without --no-build")
    print(f"egglog {EGGLOG.relative_to(ROOT)}   xmulti {XMULTI.relative_to(ROOT)}", file=sys.stderr)

    rows = []
    if args.study in ("all", "array"):
        rows += list(array_rows(args.params, args.rounds or 6, sides, args.counts, args.timeout))
    if args.study in ("all", "sdql"):
        workloads = [w for w in pf.WORKLOADS if w[0] in args.kernel and w[1] in args.phase]
        if args.rules == 12 and workloads != [("batax", "2nd")]:
            ap.error("--rules 12 is the suite's BATAX second-phase subset: use --kernel batax --phase 2nd")
        rows += list(sdql_rows(workloads, args.rules, args.rounds, sides, args.counts, args.timeout))
    return rows


if __name__ == "__main__":
    sys.exit(main())
