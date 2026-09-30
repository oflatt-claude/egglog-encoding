#!/usr/bin/env python3
"""The paper's case studies, from one command.

Schneider et al., *Slotted E-Graphs* (PLDI 2025) evaluates on two languages this
repository carries: the S4.1 functional array language, rewriting (A) into (B) with N
extra function parameters, and the S4.2 SDQL compiler, whose ten Table 1 workloads --
five kernels, two compiler phases each -- `slotted/paper_fixtures.py` carries from the
artifact. This runs each on up to three SIDES and reports the paper's criterion -- was
the target reached within the iteration budget -- with the time it took, the size of
the e-graph it built beside Table 1's, whether it had settled, and how the encoding's
graph compares with each reference side's:

    encoding    the egglog slotted encoding, `slotted/slotted-encoder.py`
    ref-multi   the reference crate through `MultiPattern`, the pattern language the
                encoding implements and the harness's oracle
    ref-nested  the reference crate through nested `Rewrite`/`ematch_all`, the matcher
                the paper's own experiments ran; incomplete on redundant slots, so it
                can reach less than `ref-multi`; uses the artifact's syntactic substitution

Usage:
    python3 slotted/eval.py                         both studies, every side, paper budgets
    python3 slotted/eval.py array --params 0 1 2 3  the array goal with 0..3 parameters
    python3 slotted/eval.py sdql                    all ten SDQL workloads, all 44 rules
    python3 slotted/eval.py sdql --kernel ttm mmm --phase 1st
    python3 slotted/eval.py sdql --kernel batax --phase 2nd --rules 12
                                                    the suite's goal-directed BATAX subset
    python3 slotted/eval.py --side encoding,ref-nested --no-counts   timings alone
    python3 slotted/eval.py sdql --kernel ttm --phase 2nd --group-cap 12 --timeout 1200
                                                    TTM's second phase, dumped and compared
    python3 slotted/eval.py sdql --phase 1st --html eval.html   the table as a page too
    python3 slotted/eval.py --from                               the table again, from the record

Budgets default to the paper's: 6 iterations for the array goal, and for SDQL the
artifact runner's per-workload limit (13 for BATAX's first phase, 12 for its second, 30
for the rest); `--rounds` overrides them all. `--timeout` defaults to the artifact's
300 s per run. Both binaries are built in release first, the oracle without the crate's
`checks` feature, since the differential harness uses debug, checked builds and those
numbers mean nothing; `--no-build` skips that when they are known current. Each
reference row says which oracle answered. A compact summary groups systems under each
workload, following the layout of the paper's Table 1. It shows the round budget,
goal outcome, elapsed seconds, nodes, classes, and saturation. These are this run's
measurements; the budget is not the paper's completed iteration count. The full
table follows, with one row per workload,
with separate columns per side for goal outcome, elapsed seconds, and graph
`classes/nodes, sat. yes|no`: the final e-graph's size, and
whether one more round would have changed it -- the reference stops early and reports
that itself, the encoding runs its budget and is then asked, under `push`/`pop`, whether
a further round adds anything. A `vs ref-*` column says how the encoding's final graph
compares with that reference side's: `isomorphic` when `slotted/xdiff/isomorphism.py`
finds and verifies a witness; `different` when exact comparison rejects the graphs;
or `inconclusive` when a graph is unavailable or comparison exceeds a work limit.
Equal probe partitions or row counts do not establish graph equality. The side to
match is `ref-multi`, and the
oracle substitutes as the encoding does so that the two can build the same rows
(`slotted/ENCODING.md`, *Against the reference*); `isomorphic` is the expected verdict.
With counts enabled, a run comparing encoding with `ref-multi` exits successfully
only if all goals succeed, both class and node counts agree, and every workload has
that verified verdict. Counts are checked separately before witness search and remain
in the report even when search is inconclusive. `ref-nested`
uses the artifact's original `SynExprSubst`, without the correctness oracle's snapshot
or tie-breaking overhead, and remains a diagnostic comparison. Each reference row
records its substitution policy. Each side's goal is checked independently; a nested
failure does not imply an encoding failure. Elapsed time measures the whole run,
including unsuccessful runs, and is not time to a successful goal. The
comparison needs the oracle's dump, whose symmetry-group enumeration `--group-cap`
bounds; `--no-counts` skips counts, settling and comparison for timings alone. `--long` gives one row per run
with every field in the full table; the summary stays the same. `--html` writes both
tables as a page too. Every run is also
appended as one JSON object to
`eval.jsonl` at the repository root (`--jsonl` chooses another file), which is what a
graph should be drawn from; `--from [FILE]` prints the table from that record without
running anything -- the latest batch, that is the last invocation's rows, or with
`--merged` the latest entry per workload and side across every batch -- so collection
and reporting are separate steps. A comparison records both observation IDs; replacing
either side makes that comparison inconclusive until the selected pair is checked.
Report JSONL is a disposable cache. Older schemas must be recomputed into a fresh path.
"""

import argparse
import datetime
import importlib.util
import json
import os
import re
import subprocess
import sys
import time
import uuid
from dataclasses import asdict, dataclass, replace
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
#: Where every run is recorded unless `--jsonl` says otherwise: append-only, ignored by git.
REPORT = ROOT / "eval.jsonl"
REPORT_SCHEMA = 2


#: Release builds of both sides: egglog, and the reference through `xmulti` without the
#: crate's `checks` feature, the way the paper's experiments ran it.
EGGLOG = ROOT / "target" / "release" / "egglog"
#: `--group-cap`: how many live slots the oracle enumerates a symmetry group over when it
#: dumps its graph; past it the dump, and so the counts and the comparison, are unavailable.
#: The oracle's own default is 6, which stops at every second-phase SDQL graph; 10 covers
#: all but TTM's, whose 12-slot classes take the oracle minutes to enumerate.
GROUP_CAP = 10
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


@dataclass(frozen=True)
class Comparison:
    """A verdict about exactly two observations, including inconclusive outcomes."""

    encoding: str
    reference: str
    verdict: str


class Row:
    def __init__(self, study, case, side, rounds, rules=None):
        self.study, self.case, self.side, self.rounds, self.rules = study, case, side, rounds, rules
        self.observation = uuid.uuid4().hex
        self.goal, self.saturated, self.seconds = "?", "?", None
        self.classes, self.nodes = None, None
        self.checks = None  # the oracle's `CONFIG checks=` answer, for reference sides
        self.substitution = None  # the oracle's `CONFIG substitution=` answer
        self.paper = None  # Table 1's slotted row for this workload, when it has one
        #: encoding side: per reference side, how its final graph compares (`compare`)
        self.vs_ref = {}
        # not recorded: a reference side's dump, the encoding side's graph, for `compare`
        self.dump, self.graph = None, None
        self.graph_issue = None

    def workload(self):
        return self.study, self.case, self.rounds, self.rules

    def verdict(self, reference):
        if reference is None:
            return "inconclusive: reference observation unavailable"
        comparison = self.vs_ref.get(reference.side)
        if comparison is None:
            return "inconclusive: observations have not been compared"
        if (comparison.encoding, comparison.reference) != (self.observation, reference.observation):
            return "inconclusive: selected observations have not been compared"
        return comparison.verdict

    def as_dict(self, batch):
        d = dict(vars(self))
        d.pop("dump"), d.pop("graph")
        d["schema"] = REPORT_SCHEMA
        d["vs_ref"] = {side: asdict(comparison) for side, comparison in self.vs_ref.items()}
        d["egglog"] = str(EGGLOG.relative_to(ROOT))
        d["xmulti"] = str(XMULTI.relative_to(ROOT))
        d["date"] = datetime.datetime.now().isoformat(timespec="seconds")
        d["batch"] = batch  # one invocation of this script: what a report shows by default
        return d

    @classmethod
    def from_dict(cls, d):
        """A row back from its `--jsonl` record."""
        if d.get("schema") != REPORT_SCHEMA:
            raise SystemExit("eval.py: report cache schema changed; recompute into a fresh --jsonl path")
        row = cls(d["study"], d["case"], d["side"], d["rounds"], d.get("rules"))
        for field in (
            "observation",
            "goal",
            "saturated",
            "seconds",
            "classes",
            "nodes",
            "checks",
            "substitution",
            "graph_issue",
        ):
            setattr(row, field, d[field])
        row.paper = tuple(d["paper"]) if d.get("paper") is not None else None
        row.vs_ref = {side: Comparison(**comparison) for side, comparison in d["vs_ref"].items()}
        return row


def load_rows(path, merged):
    """The runs a record holds: the latest batch -- one invocation of this script --
    or, `merged`, the latest entry per workload and side across every batch, in the
    order they first appeared. Comparisons belong to their original observations."""
    records = []
    with path.open() as f:
        for line in f:
            if line.strip():
                records.append(json.loads(line))
    if not records:
        return [], None
    if not merged:
        batch = records[-1].get("batch")
        records = [d for d in records if d.get("batch") == batch]
    latest, order = {}, []
    for d in records:
        row = Row.from_dict(d)
        key = (*row.workload(), row.side)
        if key not in latest:
            order.append(key)
        latest[key] = row
    for row in latest.values():
        for side, comparison in row.vs_ref.items():
            reference = latest.get((*row.workload(), side))
            row.vs_ref[side] = replace(comparison, verdict=row.verdict(reference))
    return [latest[key] for key in order], (None if merged else records[-1].get("date"))


# ------------------------------------------------------------------ the reference
def oracle_env(side):
    """Choose the comparison's policy explicitly, overriding ambient XMULTI_SUBST."""
    return {
        **os.environ,
        "XMULTI_GROUP_SLOT_CAP": str(GROUP_CAP),
        "XMULTI_SUBST": "syntactic" if side == "ref-nested" else "snapshot",
    }


def run_reference(spec, row, timeout, counts):
    """One timed `xmulti` run, whose GOAL line is the criterion; with `counts`, a second,
    untimed run that also dumps the graph, since enumerating the symmetry groups for the
    dump can cost more than the run."""
    env = oracle_env(row.side)
    row.substitution = env["XMULTI_SUBST"]
    t0 = time.time()
    try:
        r = subprocess.run([str(XMULTI)], input=spec, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.time() - t0
        if counts:
            row.graph_issue = "reference timed run exceeded timeout"
        return
    row.seconds = time.time() - t0
    lines = r.stdout.splitlines()
    if r.returncode != 0 and "REFERENCE_LIMIT:" not in r.stderr:
        row.goal = "error: " + ((r.stderr.strip().splitlines() or ["?"])[-1])[:80]
        row.graph_issue = row.goal
        return
    row.goal = next((ln.split()[1] for ln in lines if ln.startswith("GOAL ")), "?")
    row.saturated = next((ln.split()[1] for ln in lines if ln.startswith("SATURATED ")), "?")
    row.checks = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG checks=")), None)
    reported_subst = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG substitution=")), None)
    if reported_subst != row.substitution:
        row.goal = "error: reference substitution policy missing or unexpected; rebuild xmulti"
        row.graph_issue = row.goal
        return
    if counts:
        try:
            r = subprocess.run(
                [str(XMULTI)], input=spec + "dump\n", capture_output=True, text=True, timeout=timeout, env=env
            )
        except subprocess.TimeoutExpired:
            row.graph_issue = "reference graph dump exceeded timeout"
            return
        if r.returncode != 0:
            row.graph_issue = "reference graph dump failed: " + (r.stderr.strip() or f"exit {r.returncode}")
            return
        try:
            g = ISO.parse_reference(r.stdout)
        except ValueError as exc:
            row.graph_issue = f"reference graph unreadable: {exc}"
            return
        if not g.ids():
            row.graph_issue = "reference graph dump is empty"
            return
        row.classes, row.nodes = g.summary()
        row.dump = r.stdout


def ctor_lines(lang):
    """`ctor <tag> <Name>` lines: what the encoding calls each of the oracle's constructors,
    so the oracle's substitution snapshot breaks ties by the same spelling."""
    out = []
    for op in {id(op): op for op in lang.ops.values()}.values():
        if op.ref:
            out.append(f"ctor {op.ref} {op.ctor}")
        else:
            out.append(f"ctor {'symbol' if 'String' in op.sig else 'number'} {op.ctor}")
    return sorted(out)


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


def one_more_round(program):
    """The program's last user-rule schedule, cut to one round.

    A step of the encoding is `(repeat n (seq (run) ...))` around the machinery's
    saturation; the same block with `n` set to 1 is one further step, which is how a
    run is asked whether it had settled. `None` when the program has no such step.
    """
    block, at = None, program.find("(run-schedule")
    while at >= 0:
        depth, end = 0, at
        for end in range(at, len(program)):
            depth += program[end] == "("
            depth -= program[end] == ")"
            if depth == 0:
                break
        if "(repeat " in program[at : end + 1]:
            block = program[at : end + 1]
        at = program.find("(run-schedule", end)
    return re.sub(r"\(repeat \d+ ", "(repeat 1 ", block, count=1) if block else None


def saturation_probe(program):
    """The program with one more round run under `push`/`pop`: the e-graph the run
    serializes is still the run's own, and the two `print-size` listings around the extra
    round say whether it changed anything -- the reference's own notion of having
    saturated, a round that applies nothing new."""
    extra = one_more_round(program)
    if extra is None:
        return program
    return program + "\n".join(["(print-size)", "(push)", extra, "(print-size)", "(pop)", ""])


def saturated(stdout):
    """Whether the two `print-size` listings agree, ignoring the rules' own match stores,
    which `slotted-apply` empties as it acts on them."""
    sizes = [(name, int(n)) for name, n in re.findall(r"\((\S+) (\d+)\)", stdout) if not name.startswith("_matched_")]
    if not sizes or len(sizes) % 2:
        return "?"
    half = len(sizes) // 2
    return "yes" if sizes[:half] == sizes[half:] else "no"


def encoding_counts(program, name, lang, row, timeout):
    """Classes and nodes of the encoding's final graph, read as the isomorphism checker
    reads it, whether one more round would have changed it, and the graph itself for
    `compare`."""
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{name}-{os.getpid()}-counts.egg"
    jpath = path.with_suffix(".json")
    path.write_text(saturation_probe(program))
    try:
        r = subprocess.run(
            [str(EGGLOG), "--to-json", *ISO.SERIALIZE_LIMITS, str(path)],
            capture_output=True,
            text=True,
            cwd=ROOT,
            timeout=timeout,
        )
        if r.returncode != 0:
            row.graph_issue = "encoding graph dump failed: " + (r.stderr.strip() or f"exit {r.returncode}")
            return
        if ISO.incomplete_serialization(r.stderr):
            row.graph_issue = "encoding graph serialization was truncated"
            return
        if not jpath.exists():
            row.graph_issue = "encoding graph dump was not written"
            return
        row.saturated = saturated(r.stdout)
        ISO.use_language(lang)
        g, issues = ISO.build_encoding_graph(json.loads(jpath.read_text()))
        if issues:
            row.graph_issue = "encoding graph unreadable: " + "; ".join(map(str, issues))
            return
        # the reference's node forms: a binder's bound slot as a slot literal
        var_class = next((c for c in g.ids() if any(n[0] == "var" for n in g.nodes[c])), None)
        g, unfaithful = ISO.to_reference_shape(g, var_class)
        if unfaithful:
            row.graph_issue = "encoding graph cannot be converted faithfully: " + str(unfaithful)
            return
        row.classes, row.nodes = g.summary()
        row.graph = g
    except subprocess.TimeoutExpired:
        row.graph_issue = "encoding graph dump exceeded timeout"
    except (json.JSONDecodeError, ISO.IsomorphismLimit) as exc:
        row.graph_issue = f"encoding graph unavailable: {exc}"
    finally:
        path.unlink(missing_ok=True)
        jpath.unlink(missing_ok=True)


def compare_counts(enc, ref):
    """A cheap check of the reported sizes, independent of witness search/verification."""
    missing = False
    for name in ("classes", "nodes"):
        a, b = getattr(enc, name), getattr(ref, name)
        if a is None or b is None:
            missing = True
        elif a != b:
            return f"different: {name} {a} vs {b} (encoding vs reference)"
    return "inconclusive: counts unavailable" if missing else "same counts"


def compare(rows):
    """Compare complete graphs, preserving differences and resource limits.

    Only a verified class/slot/group/node witness establishes graph equality.
    Probe partitions and row counts cannot replace that obligation.
    """
    enc = next((r for r in rows if r.side == "encoding"), None)
    if enc is None:
        return
    for ref_row in (r for r in rows if r.side != "encoding"):
        enc.vs_ref[ref_row.side] = Comparison(enc.observation, ref_row.observation, compare_graphs(enc, ref_row))


def compare_graphs(enc, reference):
    counts = compare_counts(enc, reference)
    if counts != "same counts":
        issues = [r.graph_issue for r in (enc, reference) if r.graph_issue]
        return counts + ("; " + "; ".join(issues) if issues else "")
    if enc.graph is None:
        return "inconclusive: no encoding graph"
    if reference.dump is None:
        return "inconclusive: no reference dump"
    try:
        ref = ISO.parse_reference(reference.dump)
    except ValueError as exc:
        return f"inconclusive: reference dump unreadable ({exc})"
    cap, ISO.SEARCH_CAP = ISO.SEARCH_CAP, min(ISO.SEARCH_CAP, 5_000)
    try:
        iso, why = ISO.find_isomorphism(ref, enc.graph)
        if iso is not None:
            bad = ISO.verify(ref, enc.graph, *iso)
            return "isomorphic" if bad is None else f"inconclusive: witness rejected ({bad})"
        if why and why.endswith("-- inconclusive"):
            return "inconclusive: " + why.removesuffix(" -- inconclusive")
        return f"different: {why}"
    except (ISO.IsomorphismLimit, RecursionError) as exc:
        return f"inconclusive: {exc}"
    finally:
        ISO.SEARCH_CAP = cap


# ------------------------------------------------------------------ the array study
def array_rows(params, rounds, sides, counts, timeout):
    for n in params:
        case = XA.goal_cases([n], rounds=rounds)[0]
        a, b = case.probes
        head = [f"rounds {rounds}", *ctor_lines(XA.LANG), f"term {XA.sexpr(a)}"]
        goal = [f"goal {XA.sexpr(b)}"]
        group, bare_program = [], None
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
                    bare_program = XA.egg_program(bare, mult=1).replace("(print-function SameClass 100000)", "")
                    encoding_counts(bare_program, case.name, XA.LANG, row, timeout)
            group.append(row)
        if counts and bare_program is not None:
            compare(group)
        yield from group


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
        head = [f"rounds {budget}", *ctor_lines(lang), f"term {start}"]
        goal = [f"goal {target}"]
        name = f"{kernel}_{phase}-{rules}rules"
        group, bare_program = [], None
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
                    bare_program = sdql_program(kernel, phase, rules, budget, False)
                    encoding_counts(bare_program, name, lang, row, timeout)
            group.append(row)
        if counts and bare_program is not None:
            compare(group)
        yield from group


# ------------------------------------------------------------------------- output
LONG_HEAD = (
    "study",
    "case",
    "side",
    "rounds",
    "rules",
    "goal",
    "saturated",
    "seconds",
    "classes",
    "nodes",
    "vs reference",
    "graph issue",
    "paper (iters, nodes, classes, sat.)",
)
SUMMARY_NOTE = (
    "Budget is the round limit; elapsed time includes unsuccessful runs. "
    "SDQL uses 44 rules unless noted. — means unavailable. "
    "Reference settings and correctness comparisons are in the full report."
)


def paper_cell(r):
    return "" if r.paper is None else f"{r.paper[0]}, {r.paper[1]:,}, {r.paper[2]:,}, {'yes' if r.paper[3] else 'no'}"


def long_cells(r):
    """One row's cells, as text, in `LONG_HEAD` order: the record of one run."""
    side = r.side + reference_label(r)
    counts = ["" if n is None else str(n) for n in (r.classes, r.nodes)]
    return [
        r.study,
        r.case,
        side,
        str(r.rounds),
        str(r.rules or ""),
        r.goal,
        r.saturated,
        seconds_cell(r),
        *counts,
        vs_cell(r),
        r.graph_issue or "",
        paper_cell(r),
    ]


def vs_cell(r):
    return "; ".join(f"{side}: {comparison.verdict}" for side, comparison in r.vs_ref.items())


def seconds_cell(r):
    return "" if r.seconds is None else f"{r.seconds:.1f}"


def graph_cell(r):
    """The final graph's size and saturation status, independent of goal outcome."""
    if r.classes is not None:
        return f"{r.classes}/{r.nodes}" + (f", sat. {r.saturated}" if r.saturated != "?" else "")
    return f"counts unavailable: {r.graph_issue}" if r.graph_issue else ""


def reference_label(*rows):
    labels = []
    for field, label in (("checks", "checks"), ("substitution", "subst")):
        values = {getattr(row, field) for row in rows}
        known = sorted(v for v in values if v is not None)
        if known:
            detail = "/".join(known)
            if None in values:
                detail += "/unknown"
            labels.append(f"{label} {detail}")
    return f" ({', '.join(labels)})" if labels else ""


def pivot(rows, sides):
    """One row per workload, with each side's goal, elapsed time, and graph separate."""
    columns = []
    for side in sides:
        label = reference_label(*(r for r in rows if r.side == side))
        columns.extend((f"{side} goal{label}", f"{side} elapsed (s)", f"{side} graph (classes/nodes, sat.)"))
    # the encoding's graph against each reference side it was compared with
    compared = [s for s in sides if any(s in r.vs_ref for r in rows)]
    head = [
        "study",
        "case",
        "rounds",
        "rules",
        *columns,
        *(f"vs {s}" for s in compared),
        "paper (iters, nodes, classes, sat.)",
    ]
    by_case, order = {}, []
    for r in rows:
        key = r.workload()
        if key not in by_case:
            by_case[key] = {"paper": paper_cell(r)}
            order.append(key)
        by_case[key][r.side] = [r.goal, seconds_cell(r), graph_cell(r)]
        for s, comparison in r.vs_ref.items():
            by_case[key][f"vs {s}"] = comparison.verdict
    table = []
    for study, case, rounds, rules in order:
        got = by_case[(study, case, rounds, rules)]
        cells = [cell for s in sides for cell in got.get(s, ["", "", ""])]
        cells += [got.get(f"vs {s}", "") for s in compared]
        table.append([study, case, str(rounds), str(rules or ""), *cells, got["paper"]])
    return head, table


def workload_label(study, case, rules):
    """Short paper names for known workloads, retaining custom workload identities."""
    if study == "sdql":
        for kernel, phase in pf.WORKLOADS:
            if case == f"{kernel}_{phase}-{rules}rules":
                name = "ΣMMM" if kernel == "mmm_sum" else kernel.upper()
                suffix = f", {rules} rules" if rules != 44 else ""
                return f"{name} ({phase}{suffix})"
    if study == "array" and (match := re.fullmatch(r"goal-2d-4f-N(\d+)", case)):
        return f"Array N={match[1]}"
    suffix = f" ({rules} rules)" if rules is not None else ""
    return f"{study}: {case}{suffix}"


def summary(rows, sides):
    """Table 1's grouped system rows, with independently measured goals and timings."""
    head = ("Workload", "System", "Budget", "Goal", "Elapsed (s)", "Nodes", "Classes", "Sat.")
    groups = {}
    for row in rows:
        groups.setdefault(row.workload(), {})[row.side] = row
    table = []
    for (study, case, rounds, rules), group in groups.items():
        label = workload_label(study, case, rules)
        for i, side in enumerate(sides):
            row = group.get(side)
            cells = [label if i == 0 else "", side, str(rounds)]
            if row is None:
                cells += ["missing", "—", "—", "—", "—"]
            else:
                goal = "error" if row.goal.startswith("error") else row.goal
                cells += [goal, seconds_cell(row) or "—"]
                cells += ["—" if n is None else f"{n:,}" for n in (row.nodes, row.classes)]
                cells += ["—" if row.saturated == "?" else row.saturated]
            table.append(cells)
    return head, table


def report_sections(rows, sides, long=False):
    full = (LONG_HEAD, [long_cells(r) for r in rows]) if long else pivot(rows, sides)
    return [("Summary", SUMMARY_NOTE, *summary(rows, sides)), ("Full report", "", *full)]


def markdown(head, table):
    """A Markdown table with its columns padded, so it also reads aligned in a terminal."""
    table = [list(head)] + table
    widths = [max(len(row[i]) for row in table) for i in range(len(head))]

    def line(cells):
        return "| " + " | ".join(c.ljust(w) for c, w in zip(cells, widths, strict=True)) + " |"

    rule = "|" + "|".join("-" * (w + 2) for w in widths) + "|"
    return "\n".join([line(table[0]), rule] + [line(c) for c in table[1:]])


def html(sections):
    """The summary and full table as a standalone page."""
    import html as h

    contents = []
    for title, note, head, table in sections:
        head_cells = "".join(f"<th>{h.escape(c)}</th>" for c in head)
        body = []
        for cells in table:
            row_class = ' class="group"' if cells[0] else ""
            body.append(f"<tr{row_class}>" + "".join(f"<td>{h.escape(c)}</td>" for c in cells) + "</tr>")
        contents.append(
            f"<section><h2>{h.escape(title)}</h2><div class=scroll>"
            f"<table><thead><tr>{head_cells}</tr></thead><tbody>\n"
            + "\n".join(body)
            + "\n</tbody></table></div>"
            + (f"<p>{h.escape(note)}</p>" if note else "")
            + "</section>"
        )
    return (
        "<!doctype html><meta charset=utf-8><meta name=viewport content='width=device-width, initial-scale=1'>"
        "<title>slotted eval</title>"
        "<style>body{font:14px system-ui,sans-serif;margin:2em}table{border-collapse:collapse}"
        "section{margin-bottom:2.5em}.scroll{overflow-x:auto}p{max-width:85ch;color:#555;line-height:1.5}"
        "th,td{border:1px solid #bbb;padding:4px 10px;text-align:left;white-space:nowrap}"
        "th{background:#eee}tr:nth-child(even){background:#f7f7f7}"
        "section:first-of-type th,section:first-of-type td{border:0;padding:6px 12px}"
        "section:first-of-type tr{background:none}"
        "section:first-of-type th{background:none;border-bottom:2px solid #777}"
        "section:first-of-type tr.group td{border-top:1px solid #ccc}"
        "section:first-of-type td:nth-child(n+3){text-align:right;font-variant-numeric:tabular-nums}"
        "</style>\n" + "\n".join(contents) + "\n"
    )


def main():
    global GROUP_CAP
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
    ap.add_argument(
        "--counts",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="count the final e-graphs' classes and nodes, whether the encoding had settled, and compare"
        " the encoding's graph with each reference side's (isomorphic, different, or inconclusive);"
        " require verified equality to ref-multi when both sides are selected",
    )
    ap.add_argument(
        "--group-cap",
        type=int,
        default=GROUP_CAP,
        help="live slots the oracle enumerates a symmetry group over when dumping; TTM's second phase"
        " needs 12, which takes the oracle minutes (default %(default)s)",
    )
    ap.add_argument("--timeout", type=int, default=300, help="seconds per run; the artifact's own budget")
    ap.add_argument(
        "--jsonl", type=Path, default=REPORT, help=f"record one JSON object per run here (default {REPORT.name})"
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
    ap.add_argument(
        "--merged", action="store_true", help="with --from: the latest entry per workload and side across every batch"
    )
    ap.add_argument("--no-build", action="store_true", help="skip `cargo build`; the binaries are known current")
    args = ap.parse_args()

    GROUP_CAP = args.group_cap
    sides = SIDES if args.side == "all" else tuple(s.strip() for s in args.side.split(","))
    bad = [s for s in sides if s not in SIDES]
    if bad:
        ap.error(f"unknown side {bad}; choose from {SIDES}")

    if args.report:
        # reporting alone: the rows come from an earlier run's record
        rows, when = load_rows(args.report, args.merged)
        rows = [r for r in rows if r.side in sides]
        shown = "every batch, latest entries" if args.merged else f"the batch of {when}"
        print(f"{args.report}: {shown}", file=sys.stderr)
        if args.study != "all":
            rows = [r for r in rows if r.study == args.study]
        if args.side == "all":
            sides = tuple(s for s in SIDES if any(r.side == s for r in rows))
    else:
        rows = collect(args, sides, ap)

    sections = report_sections(rows, sides, args.long)
    print(
        "\n\n".join(
            f"## {title}\n\n{markdown(head, table)}" + (f"\n\n{note}" if note else "")
            for title, note, head, table in sections
        )
    )
    if args.html:
        args.html.write_text(html(sections))
        print(f"wrote {args.html}", file=sys.stderr)
    if not args.report:
        # one id per invocation: the clock alone can name two quick runs alike
        batch = f"{datetime.datetime.now().isoformat(timespec='microseconds')}-{os.getpid()}"
        with args.jsonl.open("a") as f:
            for r in rows:
                f.write(json.dumps(r.as_dict(batch)) + "\n")
    return 0 if successful(rows, sides, args.counts) else 1


def successful(rows, sides, counts):
    """Goals must succeed; MultiPattern comparison needs equal counts and a certificate.

    The nested matcher is a diagnostic, not the correctness oracle. Explicit
    `--no-counts` runs check goals alone; missing verdicts or evidence about other
    observations do not satisfy a requested graph comparison.
    """
    if not rows or any(r.goal != "yes" for r in rows):
        return False
    if not counts or not {"encoding", "ref-multi"}.issubset(sides):
        return True
    groups = {}
    for row in rows:
        groups.setdefault(row.workload(), {})[row.side] = row
    return all(
        "encoding" in group
        and "ref-multi" in group
        and compare_counts(group["encoding"], group["ref-multi"]) == "same counts"
        and group["encoding"].verdict(group["ref-multi"]) == "isomorphic"
        for group in groups.values()
    )


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
