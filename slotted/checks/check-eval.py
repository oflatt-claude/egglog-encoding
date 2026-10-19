#!/usr/bin/env python3
"""Regressions for complete refinement and trustworthy evaluation verdicts."""

import argparse
import copy
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]
E = __import__("slotted-eval")
import eval_observation as R  # noqa: E402
import eval_run as run  # noqa: E402
import eval_verify as V  # noqa: E402
import eval_workloads as W  # noqa: E402
import xdiff as X  # noqa: E402

from benchmarking.reports.slotted import EXACT_PAIRS, SIDES, slotted_report  # noqa: E402

CHECK_CONFIG = E.Config(
    egglog=ROOT / "target" / "debug" / "egglog-experimental",
    xmulti=ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti",
)

ENCODED_CONFIG = E.Config(egglog=ROOT / "target" / "debug" / "egglog-experimental", xmulti=CHECK_CONFIG.xmulti)


def cached_record(row, batch):
    from eval_cache import ENDPOINTS, record

    from benchmarking.models import TargetRow
    from benchmarking.reports.store import CacheKey

    return record(
        row,
        batch,
        key=CacheKey("sha256:test-binary", "sha256:test-workload", ENDPOINTS[row.side], 60),
        provenance=TargetRow("test", str(ROOT), "HEAD", "test", False),
        counts=True,
    )


def successful(rows, sides, counts):
    return not slotted_report([cached_record(row, "test") for row in rows], sides=sides, counts=counts).errors


def graphs(name, program, spec, lang=X.LANG):
    enc, ref = (R.Row("regression", name, side, 1) for side in ("encoding", "ref-multi"))
    V.encoding_counts(program, name, lang, enc, 60, config=ENCODED_CONFIG, encoded=True)
    run.run_reference(spec, ref, 60, config=CHECK_CONFIG)
    V.reference_counts(spec, ref, 60, config=CHECK_CONFIG)
    assert enc.graph is not None and ref.graph is not None, (name, enc.as_dict("test"), ref.as_dict("test"))
    V.compare([enc, ref])
    return enc, ref


def source_graphs(name, rounds):
    """Compare a small SDQL fixture's start, unions, rewrites, and final goal."""
    path = ROOT / "slotted" / "tests" / f"{name}.egg"
    src = W.syntax.Source(path)
    lang = W.pf.reference_language()
    forms = W.syntax.parse(path.read_text())
    start = next(f[2] for f in forms if f[:2] == ["let", "start"])
    target = next(f[1][2] for f in forms if f[0] == "check")
    spec = (
        "\n".join(
            [
                f"rounds {rounds}",
                *W.ctor_lines(lang),
                f"term {lang.sexpr(src.term(start, ground=True))}",
                "term (var $0)",
                *(
                    "union " + " ".join(lang.sexpr(src.term(t, ground=True)) for t in f[1:])
                    for f in forms
                    if f[0] == "union"
                ),
                *W.rule_lines(lang, path, None, False),
                f"goal {lang.sexpr(src.term(target, ground=True))}",
            ]
        )
        + "\n"
    )
    return graphs(name, X.driver.compile_source(path.read_text()), spec, lang)


def substitution_refresh():
    enc, ref = source_graphs("subst-refresh", 2)
    assert ref.goal == "yes", ref.goal
    assert enc.graph.summary() == (5, 8) == (ref.classes, ref.nodes)
    assert enc.verdict(ref) == "isomorphic", enc.vs_ref


def coset_direction():
    enc, ref = source_graphs("coset-direction", 1)
    assert ref.goal == "yes", ref.goal
    assert enc.verdict(ref) == "isomorphic", enc.vs_ref


def symmetry_case(depth, swapped):
    left, right = ("var", 0), ("var", 1)
    term = ("f", left, right)
    chain = ("null",)
    for _ in range(depth):
        chain = ("g", ("null",), chain)
    terms = [term, chain]
    source = '(include "slotted/languages/toy.egg")\n'
    source += "\n".join(f"(let seed{i} {X.driver.term(X.LANG, t)})" for i, t in enumerate(terms))
    program = X.driver.compile_source(source + "\n(run 0)")
    spec = "\n".join(f"term {X.sexpr(t)}" for t in terms) + "\n"
    if swapped:
        spec += f"union {X.sexpr(term)} {X.sexpr(('f', right, left))}\n"
    return graphs(f"symmetry-{depth}-{swapped}", program, spec)


def complete_refinement():
    atoms = [("root", "null", [])]
    atoms += [(f"p{i}", "f", [("pv", f"a{i}"), ("pv", f"a{i}")]) for i in range(6)]
    rhs = ("pv", "a5")
    for i in reversed(range(5)):
        rhs = ("g", ("pv", f"a{i}"), rhs)
    source = '(include "slotted/languages/toy.egg")\n'
    source += X.driver.rewrite(X.LANG, atoms, "root", rhs, name="all-refinements")
    program = X.driver.compile_source(source + "\n(let n (Null))\n(let f (F $0 $0))\n(run 1)")
    root, lines = X.syntax.atom_lines(X.LANG, "root", atoms)
    spec = "\n".join(
        [
            "rounds 1",
            "term (null)",
            "term (f (var $0) (var $0))",
            "rule",
            *lines,
            f"rhs {root} {X.syntax.pat_sexpr(X.LANG, rhs)}",
            "",
        ]
    )
    enc, ref = graphs("all-refinements", program, spec)
    assert enc.verdict(ref) == "isomorphic", enc.vs_ref
    assert enc.graph.summary() == (77, 280) == (ref.classes, ref.nodes)


def count_round_budget():
    """Graph collection must not execute another user round to probe saturation."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "budget.egg"
        path.write_text(
            '(include "slotted/languages/toy.egg")\n(rewrite (Null) (F $0 $0))\n(let start (Null))\n(run 1)\n'
        )
        program = X.driver.compile_source(path.read_text())
    # Installed after the requested run: any additional user-rule step is an error.
    program += '\n(rule () ((panic "graph collection exceeded the round budget")))\n'
    row = R.Row("regression", "count-budget", "encoding", 1)
    V.encoding_counts(program, "count-budget", X.LANG, row, 60, config=ENCODED_CONFIG, encoded=True)
    assert row.graph is not None, row.graph_issue
    assert row.graph.summary() == (2, 3) == (row.classes, row.nodes)
    assert row.saturated == "?"


def raw_node_counts():
    """An unretired invocation must survive reading and fail the count check."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "rows.egg"
        path.write_text(
            '(include "slotted/languages/toy.egg")\n(let a (F $1 (Null)))\n(let b (F $2 (Null)))\n(run 0)\n'
        )
        program = X.driver.compile_source(path.read_text())
        path.write_text(program)
        subprocess.run(
            [str(CHECK_CONFIG.egglog), "--slotted-encoded", "--to-json", *V.ISO.SERIALIZE_LIMITS, str(path)],
            capture_output=True,
            text=True,
            check=True,
            timeout=60,
        )
        doc = json.loads(path.with_suffix(".json").read_text())
    nodes = doc["nodes"]

    def renaming_node(pairs):
        return next(
            key
            for key, node in nodes.items()
            if node["op"] == "map-of" and [nodes[c]["op"] for c in node["children"]] == pairs
        )

    original, issues = V.ISO.build_encoding_graph(doc, X.LANG)
    assert not issues and original.summary() == (3, 3), issues
    extra = copy.deepcopy(next(n for n in nodes.values() if n["op"] == "F"))
    # The retired invocation has a different raw key and frame: F($2, Null)
    # instead of F($1, Null). Both translate to the same slotted node.
    slots_two = nodes[renaming_node(["2", "2"])]["eclass"]
    follower = next(n for n in nodes.values() if n["op"] == X.SYM.class_slots and n["eclass"] == slots_two)
    extra["eclass"] = nodes[follower["children"][0]]["eclass"]
    extra["children"][0] = renaming_node(["0", "2"])
    nodes["unretired-F"] = extra
    duplicated, issues = V.ISO.build_encoding_graph(doc, X.LANG)
    assert not issues and duplicated.summary() == (3, 4), issues
    witness, _why = V.ISO.find_isomorphism(original, duplicated)
    assert witness is None

    def dump(cmd, **_kwargs):
        Path(cmd[-1]).with_suffix(".json").write_text(json.dumps(doc))
        return subprocess.CompletedProcess(cmd, 0, "", "")

    row = R.Row("regression", "raw-node-count", "encoding", 0)
    # A future reader regression must not defeat the independent raw count.
    with (
        patch.object(subprocess, "run", side_effect=dump),
        patch.object(V.ISO, "build_encoding_graph", return_value=(original, [])),
    ):
        V.encoding_counts(program, "raw-node-count", X.LANG, row, 60, config=ENCODED_CONFIG, encoded=True)
    assert row.nodes == 4 and row.graph is None
    assert "raw constructor count 4 disagrees" in row.graph_issue, row.graph_issue


def verdicts():
    # Same class/node counts on both sides; only the symmetry group differs.
    # Exercise both sides of the former 40-class cutoff.
    for depth in (0, 41):
        enc, ref = symmetry_case(depth, True)
        assert (enc.classes, enc.nodes) == (ref.classes, ref.nodes)
        assert enc.verdict(ref).startswith("different:"), enc.vs_ref

    enc, ref = symmetry_case(41, False)
    assert enc.classes > 40 and enc.verdict(ref) == "isomorphic", enc.vs_ref
    V.compare([enc, ref], search_cap=0)
    assert enc.verdict(ref).startswith("inconclusive:"), enc.vs_ref
    assert V.compare_counts(enc, ref) == "same counts"

    witness, why = V.ISO.find_isomorphism(ref.graph, enc.graph)
    assert witness is not None, why
    # Even a broken checker that always accepts must not override the simple counts.
    for side in (enc, ref):
        for name in ("classes", "nodes"):
            for value in (getattr(side, name) + 1, None):
                with (
                    patch.object(side, name, value),
                    patch.object(V.ISO, "find_isomorphism", return_value=(witness, None)) as search,
                    patch.object(V.ISO, "verify", return_value=None) as verify,
                ):
                    V.compare([enc, ref])
                    prefix = "inconclusive: counts unavailable" if value is None else f"different: {name} "
                    assert enc.verdict(ref).startswith(prefix), enc.vs_ref
                    search.assert_not_called()
                    verify.assert_not_called()
    with (
        patch.object(V.ISO, "find_isomorphism", return_value=(witness, None)),
        patch.object(V.ISO, "verify", return_value="deliberately invalid witness"),
    ):
        V.compare([enc, ref])
    assert enc.verdict(ref).startswith("inconclusive: witness rejected"), enc.vs_ref

    with patch.object(ref, "graph", None):
        V.compare([enc, ref])
        assert enc.verdict(ref) == "inconclusive: no reference graph"
    enc.graph = None
    V.compare([enc, ref])
    assert enc.verdict(ref) == "inconclusive: no encoding graph"
    return enc, ref


def goal_reporting():
    # A short budget actually misses the goal on all sides. Equal graphs
    # alone must not turn this into a successful benchmark.
    rows = E.collect_workload(
        W.array_workload(0, rounds=1),
        argparse.Namespace(counts=True, timeout=30, jobs=1),
        SIDES,
        CHECK_CONFIG,
        run.quiet_progress,
    )
    assert all(r.goal == "no" for r in rows), [r.as_dict("test") for r in rows]
    by_side = {r.side: r for r in rows}
    assert set(by_side) == set(SIDES)
    for encoding, reference in EXACT_PAIRS.items():
        assert by_side[encoding].verdict(by_side[reference]) == "isomorphic"
    assert not successful(rows, SIDES, True)


def substitution_policies():
    # The body was created as g, but f wins the snapshot's spelling tie-break.
    # Checking which substituted node actually appears catches using the wrong
    # policy even if the CONFIG line and report label claim the right one.
    head = """rounds 1
term (app (lam $0 (g (var $0) (null))) (null))
union (g (var $0) (null)) (f (var $0) (null))
rule
"""
    for side, lhs, policy, op in (
        ("ref-nested", "nested (app (lam $x ?body) ?t)", "syntactic", "g"),
        ("ref-nested-snapshot", "nested (app (lam $x ?body) ?t)", "snapshot", "f"),
        ("ref-multi", "atom root app lam t\natom lam lam $x body", "snapshot", "f"),
    ):
        spec = head + lhs + f"\nrhs root ?body[(var $x) := ?t]\ngoal ({op} (null) (null))\n"
        row = R.Row("regression", "substitution-policy", side, 1)
        with patch.dict(os.environ, {"XMULTI_SUBST": "invalid-ambient-policy"}):
            run.run_reference(spec, row, 30, config=CHECK_CONFIG)
            V.reference_counts(spec, row, 30, config=CHECK_CONFIG)
        assert row.goal == "yes", row.as_dict("test")
        assert row.substitution == policy
        graph = row.graph
        assert graph is not None, row.graph_issue
        assert (row.classes, row.nodes) == graph.summary()
        # Both the timed and counting runs chose the intended substituted node.
        other = "f" if op == "g" else "g"
        null = next(cid for cid, nodes in graph.nodes.items() if any(tag == "null" for tag, _ in nodes))
        substituted = {
            tag
            for nodes in graph.nodes.values()
            for tag, elems in nodes
            if elems == (("child", null, ()), ("child", null, ()))
        }
        assert op in substituted and other not in substituted, graph.nodes


def graph_failure_reasons():
    def row():
        return R.Row("regression", "diagnostics", "encoding", 1)

    with tempfile.TemporaryDirectory(prefix="slotted-eval-errors-") as tmp, patch.object(V, "SCRATCH", Path(tmp)):
        failed = row()
        with patch.object(subprocess, "run", side_effect=subprocess.TimeoutExpired("egglog", 1)):
            V.encoding_counts("", "timeout", X.LANG, failed, 1)
        assert "exceeded timeout" in failed.graph_issue
        assert failed.as_dict("test")["graph_issue"] == failed.graph_issue

        def dump(args, **_kwargs):
            Path(args[-1]).with_suffix(".json").write_text('{"nodes": {}}')
            return subprocess.CompletedProcess(args, 0, "", "")

        with (
            patch.object(subprocess, "run", side_effect=dump),
            patch.object(V.ISO, "build_encoding_graph", side_effect=RuntimeError("reader bug")),
        ):
            try:
                V.encoding_counts("", "bug", X.LANG, row(), 1)
            except RuntimeError as exc:
                assert str(exc) == "reader bug"
            else:
                raise AssertionError("a programming error was silently swallowed")
        assert not list(Path(tmp).iterdir())

    timed = subprocess.CompletedProcess([], 0, "GOAL yes\nCONFIG substitution=snapshot\n", "")
    for code, stdout, stderr, reason in (
        (1, "", "REFERENCE_LIMIT: symmetry enumeration is capped", "symmetry enumeration"),
        (0, "CLASS c SLOTS x\nGROUP c ?\n", "", "reference graph unreadable"),
        (0, "", "", "reference graph dump is empty"),
    ):
        reference = R.Row("regression", "diagnostics", "ref-multi", 1)
        dump = subprocess.CompletedProcess([], code, stdout, stderr)
        with patch.object(subprocess, "run", side_effect=[timed, dump]):
            run.run_reference("", reference, 1)
            V.reference_counts("", reference, 1)
        assert reference.goal == "yes" and reason in reference.graph_issue
        assert reference.graph is None and reference.classes is None and reference.nodes is None
        failed = row()
        V.compare([failed, reference])
        assert reason in failed.verdict(reference)

    # Direct sizes survive the dump's symmetry cap or a timeout after SIZES.
    for dump in (
        subprocess.CompletedProcess([], 2, "SIZES 10 20\n", "REFERENCE_LIMIT: symmetry cap"),
        subprocess.TimeoutExpired("xmulti", 1, output=b"SIZES 10 20\n"),
    ):
        reference = R.Row("regression", "diagnostics", "ref-nested-snapshot", 1)
        with patch.object(subprocess, "run", side_effect=[timed, dump]):
            run.run_reference("", reference, 1)
            V.reference_counts("", reference, 1)
        assert (reference.classes, reference.nodes) == (10, 20)
        assert reference.graph is None and reference.graph_issue
        failed = row()
        failed.classes, failed.nodes = 10, 20
        failed.graph = object()
        V.compare([failed, reference])
        assert failed.verdict(reference).startswith("inconclusive: no reference graph")


def combined_comparisons():
    rows = E.collect_workload(
        W.sdql_workload("mmm_sum", "1st"),
        argparse.Namespace(counts=True, timeout=30, jobs=1),
        SIDES,
        CHECK_CONFIG,
        run.quiet_progress,
    )
    assert successful(rows, SIDES, True), [r.as_dict("test") for r in rows]
    by_side = {r.side: r for r in rows}
    for encoding, reference in EXACT_PAIRS.items():
        assert by_side[encoding].verdict(by_side[reference]) == "isomorphic"


def logic_case_studies():
    """Use the public collector for source-derived logic rules and exact evidence."""
    paths = sorted(W.LOGIC_FIXTURES.glob("first-order-logic*.egg"))
    assert len(paths) >= 2, "missing first-order logic fixtures"
    for path in paths:
        workload = W.logic_workload(path)
        rows = E.collect_workload(
            workload,
            argparse.Namespace(counts=True, timeout=60, jobs=1),
            SIDES,
            CHECK_CONFIG,
            run.quiet_progress,
        )
        assert [row.side for row in rows] == ["encoding", "ref-multi"]
        assert set(workload.unsupported) == {"encoding-no-aliasing", "ref-nested-snapshot", "ref-nested"}
        assert successful(rows, SIDES, True), [row.as_dict("test") for row in rows]
        enc, ref = rows
        assert V.compare_counts(enc, ref) == "same counts"
        assert enc.verdict(ref) == "isomorphic"


def zero_round_budget():
    """An explicit zero must not silently run the paper's default budget."""
    args = argparse.Namespace(
        no_build=True,
        study="all",
        case=None,
        params=[0],
        kernel=["mmm"],
        phase=["1st"],
        rules=44,
        rounds=0,
        counts=False,
        timeout=30,
        jobs=1,
    )
    with tempfile.TemporaryDirectory(prefix="slotted-zero-rounds-") as tmp:
        args.jsonl = Path(tmp) / "report.jsonl"
        records = E.collect(args, ("ref-multi",), argparse.ArgumentParser(), config=CHECK_CONFIG)
    assert len(records) == 4
    assert all(r["slotted"]["rounds"] == 0 and r["slotted"]["goal"] == "no" for r in records), records


def parallel_collection():
    """Spawned workers preserve both languages' counts, verdicts, and configuration."""
    args = argparse.Namespace(
        no_build=True,
        study="all",
        case=None,
        params=[0],
        kernel=["mmm_sum"],
        phase=["1st"],
        rules=44,
        rounds=2,
        counts=True,
        timeout=60,
        jobs=1,
    )

    def evidence(records):
        return [
            {
                **{k: v for k, v in r["slotted"].items() if k not in ("observation", "batch", "jobs", "vs_ref")},
                "vs_ref": {side: c["verdict"] for side, c in r["slotted"]["vs_ref"].items()},
            }
            for r in records
        ]

    with tempfile.TemporaryDirectory(prefix="slotted-parallel-") as tmp:
        args.jsonl = Path(tmp) / "report.jsonl"
        serial = E.collect(args, SIDES, argparse.ArgumentParser(), config=CHECK_CONFIG)
        args.jobs = 2
        parallel = E.collect(args, SIDES, argparse.ArgumentParser(), config=CHECK_CONFIG)
        # The small round budget misses the array goal, even though its graphs agree.
        assert slotted_report(serial).errors and slotted_report(parallel).errors
        assert evidence(serial) == evidence(parallel)
        assert all(r["slotted"]["jobs"] == 2 for r in parallel)
        assert all("graph" not in r["slotted"] for r in parallel)

        # Spawned workers must receive CLI configuration, not fresh defaults.
        args.study = "array"
        sides = ("encoding-no-aliasing", "ref-nested-snapshot")
        limited = E.collect(
            args,
            sides,
            argparse.ArgumentParser(),
            config=E.Config(CHECK_CONFIG.egglog, CHECK_CONFIG.xmulti, group_cap=0),
        )
        enc, ref = (r["slotted"] for r in limited)
        assert enc["goal"] == ref["goal"] == "no"
        assert (enc["classes"], enc["nodes"]) == (ref["classes"], ref["nodes"])
        assert "REFERENCE_LIMIT" in ref["graph_issue"]
        assert enc["vs_ref"][ref["side"]]["verdict"].startswith("inconclusive:")
        assert slotted_report(limited, sides=sides).errors


def import_without_compilation():
    """Workload definitions and reporting must not compile the test programs."""
    code = """
import importlib
import sys
from unittest.mock import patch
sys.path[:0] = ["slotted", "slotted/xdiff"]
compiler = importlib.import_module("test_program")
with patch.object(compiler, "compile_source", side_effect=AssertionError("compiled during import")):
    importlib.import_module("slotted-eval")
    importlib.import_module("xsdql")
"""
    result = subprocess.run([sys.executable, "-c", code], cwd=ROOT, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stdout + result.stderr


def separate_timing_and_graph_runs():
    """Failed goals still get untimed evidence; failed processes never certify a graph."""
    workload = W.array_workload(0, rounds=0)
    sides = ("ref-multi",)
    timed = subprocess.CompletedProcess([], 0, "GOAL no\nCONFIG substitution=snapshot\n", "")
    dump = subprocess.CompletedProcess([], 2, "SIZES 10 20\n", "REFERENCE_LIMIT: symmetry cap")
    for counts in (False, True):
        args = argparse.Namespace(counts=counts, timeout=30, jobs=1)
        with patch.object(subprocess, "run", side_effect=[timed, dump]) as process:
            (row,) = E.collect_workload(workload, args, sides, CHECK_CONFIG, run.quiet_progress)
        assert process.call_count == (2 if counts else 1)
        assert row.goal == "no" and row.seconds is not None
        assert (row.classes, row.nodes) == ((10, 20) if counts else (None, None))
        assert not successful([row], sides, counts)

    args.counts = True
    for failed in (
        subprocess.TimeoutExpired("xmulti", 30),
        subprocess.CompletedProcess([], 1, "", "reference error"),
        subprocess.CompletedProcess([], 0, "GOAL yes\nCONFIG substitution=syntactic\n", ""),
    ):
        with patch.object(subprocess, "run", side_effect=[failed]) as process:
            (row,) = E.collect_workload(workload, args, sides, CHECK_CONFIG, run.quiet_progress)
        assert process.call_count == 1
        assert row.graph_issue and row.classes is None and row.nodes is None
        assert successful([row], sides, True) == isinstance(failed, subprocess.TimeoutExpired)


def main():
    import_without_compilation()
    separate_timing_and_graph_runs()
    substitution_policies()
    combined_comparisons()
    logic_case_studies()
    graph_failure_reasons()
    goal_reporting()
    zero_round_budget()
    parallel_collection()
    substitution_refresh()
    coset_direction()
    complete_refinement()
    count_round_budget()
    raw_node_counts()
    verdicts()
    print("OK: complete refinement, separate count checks, exact graph verdicts, and evaluation exit statuses")


if __name__ == "__main__":
    main()
