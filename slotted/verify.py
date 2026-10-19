"""Untimed correctness checks for the paper evaluations.

Export the input-only graph at the same rewrite budget, validate its raw sizes,
and independently verify the isomorphism witness. Missing or bounded-out evidence
stays inconclusive. The timed goal-checking processes live in runner.
"""

import json
import os
import subprocess
from dataclasses import dataclass

from slotted.runner import ROOT, SCRATCH, Config, Row, goal_errors, oracle_env, quiet_progress, slotted_flags
from slotted.treatments import EXACT_PAIRS, SIDES, TREATMENTS
from slotted.xdiff import isomorphism as ISO


@dataclass(frozen=True)
class Comparison:
    """Keep the actual compared rows together so a verdict cannot certify another run."""

    encoding: Row
    reference: Row
    verdict: str


def collect_graph(workload, row, timeout, progress=quiet_progress, *, config=None):
    """Collect a side's graph without including graph export in its measured time."""
    if TREATMENTS[row.side].engine == "reference":
        if row.graph_issue is None:
            reference_counts(workload.reference(row.side), row, timeout, progress, config=config)
    else:
        encoding_counts(workload.graph_program, workload.case, workload.lang, row, timeout, progress, config=config)


def reference_counts(spec, row, timeout, progress=quiet_progress, *, config=None):
    """Keep direct counts even if the reference cannot enumerate its symmetry groups."""
    config = config or Config()
    env = oracle_env(row.side, config.group_cap)
    progress(row, "counts + graph dump")
    try:
        r = subprocess.run(
            [str(config.xmulti)],
            input=spec + "sizes\ndump\n",
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
        )
    except subprocess.TimeoutExpired as exc:
        reference_sizes((exc.stdout or b"").decode(), row)
        row.graph_issue = "reference graph dump exceeded timeout"
        return
    reference_sizes(r.stdout, row)
    if r.returncode != 0:
        row.graph_issue = "reference graph dump failed: " + (r.stderr.strip() or f"exit {r.returncode}")
        return
    progress(row, "reading graph")
    try:
        g = ISO.parse_reference(r.stdout)
    except ValueError as exc:
        row.graph_issue = f"reference graph unreadable: {exc}"
        return
    if not g.ids():
        row.graph_issue = "reference graph dump is empty"
        return
    if (row.classes, row.nodes) != g.summary():
        row.graph_issue = "reference direct sizes disagree with graph dump"
        return
    row.graph = g


def reference_sizes(stdout, row):
    """Keep cheap direct counts even when enumerating symmetry groups fails."""
    for line in stdout.splitlines():
        if line.startswith("SIZES "):
            row.classes, row.nodes = map(int, line.split()[1:])
            return


def encoding_counts(program, name, lang, row, timeout, progress=quiet_progress, *, config=None, encoded=False):
    """Count and read the graph at the requested budget, without further user rounds.

    An extra round to probe saturation can explode even when this graph is cheap
    to collect. Equal row counts would not establish a fixed point either.
    """
    config = config or Config()
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{name}-{os.getpid()}-counts.egg"
    jpath = path.with_suffix(".json")
    jpath.unlink(missing_ok=True)
    path.write_text(program)
    progress(row, "counts + graph dump")
    try:
        r = subprocess.run(
            [
                str(config.egglog),
                *(["--slotted-encoded"] if encoded else slotted_flags(row)),
                "--to-json",
                *ISO.SERIALIZE_LIMITS,
                str(path),
            ],
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
        progress(row, "validating graph")
        doc = json.loads(jpath.read_text())
        constructors = {op.ctor for op in lang.ops.values()} | {lang.symbols_for(lang.default_sort).var}
        row.nodes = sum(n.get("op") in constructors for n in doc["nodes"].values())
        g, issues = ISO.build_encoding_graph(doc, lang)
        if issues:
            row.graph_issue = "encoding graph unreadable: " + "; ".join(map(str, issues))
            return
        # the reference's node forms: a binder's bound slot as a slot literal
        var_class = next((c for c in g.ids() if any(n[0] == "var" for n in g.nodes[c])), None)
        g, unfaithful = ISO.to_reference_shape(g, var_class, lang=lang)
        if unfaithful:
            row.graph_issue = "encoding graph cannot be converted faithfully: " + str(unfaithful)
            return
        row.classes, reconstructed_nodes = g.summary()
        if row.nodes != reconstructed_nodes:
            row.graph_issue = (
                f"encoding raw constructor count {row.nodes} disagrees with reconstructed graph {reconstructed_nodes}"
            )
            return
        row.graph = g
    except subprocess.TimeoutExpired:
        row.graph_issue = "encoding graph dump exceeded timeout"
    except json.JSONDecodeError as exc:
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


def compare(rows, progress=quiet_progress, *, search_cap=5_000, checker=None):
    """Compare complete graphs, preserving differences and resource limits.

    Only a verified class/slot/group/node witness establishes graph equality.
    Probe partitions and row counts cannot replace that obligation.
    """
    for enc in (r for r in rows if r.side in EXACT_PAIRS):
        for ref_row in (r for r in rows if TREATMENTS[r.side].engine == "reference"):
            progress(enc, f"isomorphism vs {ref_row.side}")
            enc.vs_ref[ref_row.side] = Comparison(
                enc, ref_row, compare_graphs(enc, ref_row, search_cap=search_cap, checker=checker)
            )
    progress(None, "idle")


def compare_graphs(enc, reference, *, search_cap=5_000, checker=None):
    counts = compare_counts(enc, reference)
    if counts != "same counts":
        issues = [r.graph_issue for r in (enc, reference) if r.graph_issue]
        return counts + ("; " + "; ".join(issues) if issues else "")
    if enc.graph is None:
        return "inconclusive: no encoding graph"
    if reference.graph is None:
        return "inconclusive: no reference graph" + (f"; {reference.graph_issue}" if reference.graph_issue else "")
    iso, why = ISO.find_isomorphism(reference.graph, enc.graph, search_cap=search_cap, checker=checker)
    if iso is not None:
        bad = ISO.verify(reference.graph, enc.graph, iso, checker=checker)
        return "isomorphic" if bad is None else f"inconclusive: witness rejected ({bad})"
    if why and why.endswith("-- inconclusive"):
        return "inconclusive: " + why.removesuffix(" -- inconclusive")
    if why and why.startswith("invalid graph:"):
        return "inconclusive: " + why
    return f"different: {why}"


def assess(rows, sides=SIDES):
    """Require goals and both exact pairs; keep other comparisons diagnostic.

    Reference timeouts are explicitly unverified. They cannot excuse unhealthy
    encoding evidence or any known mismatch, including counts emitted before a
    reference dump timed out.
    """
    if not rows:
        return [], ["No results."]
    by_side = {row.side: row for row in rows}
    unsupported = rows[0].unsupported
    errors = goal_errors(rows)
    for side in sides:
        if side not in unsupported and side not in by_side:
            errors.append(f"missing {side} observation")
    comparisons = []
    for encoding, required in EXACT_PAIRS.items():
        if encoding not in sides or encoding in unsupported or encoding not in by_side:
            continue
        enc = by_side[encoding]
        for side in sides:
            if side in unsupported or (side != required and side not in enc.vs_ref):
                continue
            ref = by_side.get(side)
            counts = compare_counts(enc, ref) if ref is not None else "same counts"
            verdict = counts if counts != "same counts" else enc.verdict(ref)
            if verdict == "isomorphic" and (enc.graph_issue or ref.graph_issue):
                verdict = "inconclusive: " + (enc.graph_issue or ref.graph_issue)
            reference_timeout = ref is not None and (
                ref.goal == "timeout" or ref.graph_issue == "reference graph dump exceeded timeout"
            )
            skipped = (
                reference_timeout
                and verdict.startswith("inconclusive:")
                and enc.graph_issue is None
                and enc.classes is not None
                and enc.nodes is not None
            )
            comparisons.append((encoding, side, "not compared: reference timeout" if skipped else verdict))
            if side == required and verdict != "isomorphic" and not skipped:
                errors.append(f"{encoding} vs {side}: {verdict}")
    return comparisons, errors
