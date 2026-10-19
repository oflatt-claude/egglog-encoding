"""Untimed correctness checks for the paper evaluations.

Export the input-only graph at the same rewrite budget, validate its raw sizes,
and independently verify the isomorphism witness. Missing or bounded-out evidence
stays inconclusive. The timed goal-checking processes live in eval_run.
"""

import json
import os
import subprocess

import isomorphism as ISO
from eval_observation import Comparison
from eval_run import ROOT, SCRATCH, Config, oracle_env, quiet_progress, slotted_flags

from benchmarking.reports.slotted import EXACT_PAIRS, count_issue


def collect_graph(workload, row, timeout, progress=quiet_progress, *, config=None):
    """Collect a side's graph without including graph export in its measured time."""
    if row.side.startswith("ref-"):
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
    except (json.JSONDecodeError, ISO.IsomorphismLimit) as exc:
        row.graph_issue = f"encoding graph unavailable: {exc}"
    finally:
        path.unlink(missing_ok=True)
        jpath.unlink(missing_ok=True)


def compare_counts(enc, ref):
    """A cheap check of the reported sizes, independent of witness search/verification."""
    return count_issue(enc.as_dict(""), ref.as_dict("")) or "same counts"


def compare(rows, progress=quiet_progress, *, search_cap=5_000):
    """Compare complete graphs, preserving differences and resource limits.

    Only a verified class/slot/group/node witness establishes graph equality.
    Probe partitions and row counts cannot replace that obligation.
    """
    for enc in (r for r in rows if r.side in EXACT_PAIRS):
        for ref_row in (r for r in rows if r.side.startswith("ref-")):
            progress(enc, f"isomorphism vs {ref_row.side}")
            enc.vs_ref[ref_row.side] = Comparison(
                enc.observation, ref_row.observation, compare_graphs(enc, ref_row, search_cap=search_cap)
            )
    progress(None, "idle")


def compare_graphs(enc, reference, *, search_cap=5_000):
    counts = compare_counts(enc, reference)
    if counts != "same counts":
        issues = [r.graph_issue for r in (enc, reference) if r.graph_issue]
        return counts + ("; " + "; ".join(issues) if issues else "")
    if enc.graph is None:
        return "inconclusive: no encoding graph"
    if reference.graph is None:
        return "inconclusive: no reference graph" + (f"; {reference.graph_issue}" if reference.graph_issue else "")
    try:
        iso, why = ISO.find_isomorphism(reference.graph, enc.graph, search_cap=search_cap)
        if iso is not None:
            bad = ISO.verify(reference.graph, enc.graph, *iso)
            return "isomorphic" if bad is None else f"inconclusive: witness rejected ({bad})"
        if why and why.endswith("-- inconclusive"):
            return "inconclusive: " + why.removesuffix(" -- inconclusive")
        return f"different: {why}"
    except (ISO.IsomorphismLimit, RecursionError) as exc:
        return f"inconclusive: {exc}"
