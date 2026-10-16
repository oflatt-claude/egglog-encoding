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
import eval_report as R  # noqa: E402
import eval_run as run  # noqa: E402
import eval_verify as V  # noqa: E402
import eval_workloads as W  # noqa: E402
import xdiff as X  # noqa: E402

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
    src = W.sc.Source(path)
    lang = W.pf.reference_language()
    forms = W.sc.parse(path.read_text())
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
    return graphs(name, W.sc.compile_source(src), spec, lang)


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
    program = X.machinery("toy") + "\n"
    program += "\n".join(f"(let seed{i} {X.enc(t)})" for i, t in enumerate(terms))
    program += f"\n(run-schedule {X.slotenc.MACHINERY_SCHEDULE})\n"
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
    program = X.machinery("toy") + "\n"
    program += X.slotenc.compile_rule(X.LANG, atoms, ("build", "root", rhs), name="all-refinements")
    program += f"\n(Null)\n{X.enc(('f', ('var', 0), ('var', 0)))}\n" + X.schedule(1)
    root, lines = X.slotenc.atom_lines(X.LANG, "root", atoms)
    spec = "\n".join(
        [
            "rounds 1",
            "term (null)",
            "term (f (var $0) (var $0))",
            "rule",
            *lines,
            f"rhs {root} {X.slotenc.pat_sexpr(X.LANG, rhs)}",
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
        program = W.sc.compile_source(W.sc.Source(path))
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
        program = W.sc.compile_source(W.sc.Source(path))
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

    original, issues = V.ISO.build_encoding_graph(doc)
    assert not issues and original.summary() == (3, 3), issues
    extra = copy.deepcopy(next(n for n in nodes.values() if n["op"] == "F"))
    # The retired invocation has a different raw key and frame: F($2, Null)
    # instead of F($1, Null). Both translate to the same slotted node.
    slots_two = nodes[renaming_node(["2", "2"])]["eclass"]
    follower = next(n for n in nodes.values() if n["op"] == V.ISO.SYM.class_slots and n["eclass"] == slots_two)
    extra["eclass"] = nodes[follower["children"][0]]["eclass"]
    extra["children"][0] = renaming_node(["0", "2"])
    nodes["unretired-F"] = extra
    duplicated, issues = V.ISO.build_encoding_graph(doc)
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
    assert f"{enc.classes}/{enc.nodes}" in R.graph_cell(enc)

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


def exit_status(enc, ref):
    enc.goal = ref.goal = "yes"
    sides = ("encoding", "ref-multi")
    assert not V.successful([], sides, True)
    assert not V.successful([enc], sides, True)
    with tempfile.TemporaryDirectory(prefix="slotted-eval-check-") as tmp:
        path = Path(tmp) / "report.jsonl"
        for verdict in ("isomorphic", "different: symmetry group", "inconclusive: search cap", "same rows", None):
            enc.vs_ref = (
                {} if verdict is None else {"ref-multi": R.Comparison(enc.observation, ref.observation, verdict)}
            )
            assert V.successful([enc, ref], sides, True) == (verdict == "isomorphic")
            assert V.successful([enc, ref], sides, False)  # explicitly goal-only
            path.write_text("".join(json.dumps(cached_record(row, "regression")) + "\n" for row in (enc, ref)))
            result = subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "slotted" / "slotted-eval.py"),
                    "--from",
                    str(path),
                    "--side",
                    ",".join(sides),
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )
            assert result.returncode == (0 if verdict == "isomorphic" else 1), (verdict, result.stderr)
            assert (R.ERROR_TITLE in result.stdout) == (verdict != "isomorphic")
            if verdict != "isomorphic":
                assert "encoding vs ref-multi" in result.stdout.split(R.ERROR_TITLE)[1]
        # Loading a report also checks counts, even if its stored verdict is positive.
        enc.vs_ref = {"ref-multi": R.Comparison(enc.observation, ref.observation, "isomorphic")}
        for side in (enc, ref):
            for name in ("classes", "nodes"):
                for value in (getattr(side, name) + 1, None):
                    with patch.object(side, name, value):
                        assert not V.successful([enc, ref], sides, True)
                        assert V.successful([enc, ref], sides, False)
                        path.write_text(
                            "".join(json.dumps(cached_record(row, "regression")) + "\n" for row in (enc, ref))
                        )
                        result = subprocess.run(
                            [
                                sys.executable,
                                str(ROOT / "slotted" / "slotted-eval.py"),
                                "--from",
                                str(path),
                                "--side",
                                ",".join(sides),
                            ],
                            capture_output=True,
                            text=True,
                            timeout=30,
                        )
                        assert result.returncode == 1, (name, value, result.stdout, result.stderr)
                        banner = result.stdout.split(R.ERROR_TITLE)[1].split("## Full report")[0]
                        assert ("counts unavailable" if value is None else f"different: {name}") in banner
    enc.vs_ref = {"ref-multi": R.Comparison(enc.observation, ref.observation, "isomorphic")}
    for enc_goal, ref_goal in (("yes", "no"), ("no", "yes"), ("no", "no")):
        enc.goal, ref.goal = enc_goal, ref_goal
        for counts in (True, False):
            assert not V.successful([enc, ref], sides, counts)


def goal_reporting():
    # A short budget actually misses the goal on all sides. Equal graphs
    # alone must not turn this into a successful benchmark.
    rows = E.collect_workload(
        W.array_workload(0, rounds=1),
        argparse.Namespace(counts=True, timeout=30, jobs=1),
        R.SIDES,
        CHECK_CONFIG,
        R.quiet_progress,
    )
    assert all(r.goal == "no" for r in rows), [r.as_dict("test") for r in rows]
    by_side = {r.side: r for r in rows}
    assert set(by_side) == set(R.SIDES)
    for encoding, reference in R.EXACT_PAIRS.items():
        assert by_side[encoding].verdict(by_side[reference]) == "isomorphic"
    assert not V.successful(rows, R.SIDES, True)

    # Report outcomes independently: nested may miss a goal encoding reaches.
    # A timed failed run must never put "no (1.2)" in its elapsed-time column.
    enc, nested = by_side["encoding"], by_side["ref-nested"]
    enc.goal, enc.seconds = "yes", 2.3
    nested.seconds = 1.2
    for outcome in ("no", "timeout", "error"):
        nested.goal = outcome
        head, table = R.pivot([enc, nested], R.SIDES)
        cells = dict(zip(head, table[0], strict=True))
        enc_goal = next(k for k in head if k.startswith("egglog goal"))
        nested_goal = next(k for k in head if k.startswith("ref-nested goal"))
        assert cells[enc_goal] == "yes" and cells[nested_goal] == outcome
        assert cells["egglog elapsed (s)"] == "2.3"
        assert cells["ref-nested elapsed (s)"] == ("timeout" if outcome == "timeout" else "1.2")
        assert cells["ref-multi goal"] == cells["ref-multi elapsed (s)"] == ""
        assert R.graph_cell(nested) in table[0]
        assert not V.successful([enc, nested], ("encoding", "ref-nested"), True)
        for rendered in (R.markdown(head, table), R.html([("Full report", "", head, table)])):
            assert "elapsed (s)" in rendered and "no (1.2)" not in rendered
        long = dict(zip(R.LONG_HEAD, R.long_cells(nested), strict=True))
        assert long["goal"] == outcome and long["seconds"] == ("timeout" if outcome == "timeout" else "1.2")


def summary_reporting():
    enc = R.Row("sdql", "mmm_1st-44rules", "encoding", 30, 44)
    enc.goal, enc.seconds, enc.nodes, enc.classes, enc.saturated = "yes", 1.2, 1_234, 56, "yes"
    nested = R.Row("sdql", enc.case, "ref-nested", 30, 44)
    nested.goal, nested.seconds = "no", 0.5
    snapshot = R.Row("sdql", enc.case, "ref-nested-snapshot", 30, 44)
    snapshot.goal, snapshot.seconds = "yes", 9.9
    head, table = R.summary([nested, enc, snapshot], ("encoding", "ref-multi"))
    assert head == ("Benchmark", "egglog", "ref-multi")
    assert table == [["MMM (1st)", "1.2", "—"]]
    head, table = R.summary([nested, enc, snapshot], ("encoding-no-aliasing", "ref-nested"))
    assert head == ("Benchmark", "egglog-no-aliasing", "ref-nested")
    assert table == [["MMM (1st)", "—", "0.5"]]
    # The snapshot timing must never be relabelled as the syntactic baseline.
    assert R.summary([snapshot], R.SIDES)[1][0][-1] == "—"

    # Missing/failed measurements stay explicit, including in a timing-only run.
    for goal in ("timeout", "error: detailed diagnostic", "?"):
        nested.goal = goal
        nested.seconds, nested.nodes, nested.classes = None, None, 0
        head, table = R.summary([nested], ("ref-nested",))
        assert table == [["MMM (1st)", "timeout" if goal == "timeout" else "—"]]
        errors = V.failures([nested], ("ref-nested",), False)
        assert len(errors) == 1 and f"goal not reached ({goal})" in errors[0]

    # Different round budgets and rule subsets cannot collapse into one group.
    small = R.Row("sdql", "batax_2nd-12rules", "encoding", 12, 12)
    full = R.Row("sdql", "batax_2nd-44rules", "encoding", 12, 44)
    longer = R.Row("sdql", full.case, "encoding", 30, 44)
    array = R.Row("array", "goal-2d-4f-N3", "encoding", 6)
    custom = R.Row("custom", "<case&>", "encoding", 1, 7)
    rows = [enc, nested, snapshot, small, full, longer, array, custom]
    head, table = R.summary(rows, ("encoding",))
    labels = [row[0] for row in table]
    assert labels == [
        "MMM (1st)",
        "BATAX (2nd, 12 rules)",
        "BATAX (2nd) [12 rounds]",
        "BATAX (2nd) [30 rounds]",
        "Array N=3",
        "custom: <case&> (7 rules)",
    ]
    assert all(len(row) == 2 for row in table)

    with tempfile.TemporaryDirectory(prefix="slotted-eval-summary-") as tmp:
        path, page = Path(tmp) / "report.jsonl", Path(tmp) / "report.html"
        record = "".join(json.dumps(cached_record(row, "summary")) + "\n" for row in rows)
        path.write_text(record)
        summary = R.markdown(*R.summary(rows, ("encoding", "ref-multi")), right_align=True)
        nested_summary = R.markdown(*R.summary(rows, ("encoding-no-aliasing", "ref-nested")), right_align=True)
        for long in (False, True):
            result = subprocess.run(
                [
                    sys.executable,
                    E.__file__,
                    "--from",
                    path,
                    "--side",
                    ",".join(R.SIDES),
                    "--html",
                    page,
                    *(["--long"] if long else []),
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )
            assert result.returncode == 1, result.stderr
            assert result.stdout.startswith("## Multipattern matching\n\n" + summary)
            assert "## Nested matching\n\n" + nested_summary in result.stdout
            assert result.stdout.count("## Full report") == 1
            assert result.stdout.count(R.ERROR_TITLE) == 1
            assert result.stdout.index("## Nested matching") < result.stdout.index(R.ERROR_TITLE)
            assert result.stdout.index(R.ERROR_TITLE) < result.stdout.index("## Full report")
            assert "goal not reached" in result.stdout.split(R.ERROR_TITLE)[1]
            full_table = (R.LONG_HEAD, [R.long_cells(r) for r in rows]) if long else R.pivot(rows, R.SIDES)
            assert R.markdown(*full_table) in result.stdout
            markup = page.read_text()
            assert markup.count("<table>") == 3
            assert markup.count('class="summary"') == 2
            assert "<h2>Nested matching</h2>" in markup and "<h2>Full report</h2>" in markup
            assert 'role="alert"' in markup and f"<h2>{R.ERROR_TITLE}</h2>" in markup
            assert markup.index('role="alert"') < markup.index("<h2>Full report</h2>")
            assert "&lt;case&amp;&gt;" in markup and "<case&>" not in markup
            assert path.read_text() == record

        # An explicit timing-only report says that checks were disabled and succeeds
        # without a certificate. The same cached rows fail under default checking.
        for row in (enc, snapshot):
            row.goal = "yes"
        enc.side = "encoding-no-aliasing"
        path.write_text("".join(json.dumps(cached_record(row, "unchecked")) + "\n" for row in (enc, snapshot)))
        result = subprocess.run(
            [sys.executable, E.__file__, "--from", path, "--no-counts"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode == 0, result.stderr
        assert "checks are disabled (--no-counts)" in result.stdout and R.ERROR_TITLE not in result.stdout


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
        loaded = R.Row.from_dict(row.as_dict("test"))
        assert loaded.substitution == policy
        assert f"subst {policy}" in R.long_cells(loaded)[2]
        assert f"subst {policy}" in R.pivot([loaded], (side,))[0][4]


def merged_observations():
    enc, reference = symmetry_case(0, False)
    different, newer = symmetry_case(0, True)
    assert enc.verdict(reference) == "isomorphic"
    assert different.verdict(newer).startswith("different:")
    assert (enc.classes, enc.nodes) == (newer.classes, newer.nodes)
    for row in (enc, reference, newer):
        row.goal = "yes"
        row.case = "provenance"
    sides = ("encoding", "ref-multi")
    with tempfile.TemporaryDirectory(prefix="slotted-eval-merge-") as tmp:
        path = Path(tmp) / "report.jsonl"
        original = [cached_record(enc, "first"), cached_record(reference, "first")]
        for records, valid in (
            (original, True),
            ([cached_record(enc, "first"), cached_record(reference, "copied-observation")], True),
            (original + [cached_record(newer, "reference-only")], False),
            ([cached_record(enc, "first")], False),
        ):
            path.write_text("".join(json.dumps(row) + "\n" for row in records))
            rows, _ = E.load_rows(path, merged=True)
            assert V.successful(rows, sides, True) == valid
            for extra in ([], ["--long"]):
                result = subprocess.run(
                    [sys.executable, E.__file__, "--from", path, "--merged", "--side", ",".join(sides), *extra],
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
                assert result.returncode == (0 if valid else 1), result.stderr
                assert ("isomorphic" in result.stdout) == valid, result.stdout
        replaced_encoding = R.Row.from_dict(enc.as_dict("test"))
        replaced_encoding.observation = "another-observation"
        assert not V.successful([replaced_encoding, reference], sides, True)
        old = cached_record(enc, "old-schema")
        del old["report_schema_version"]
        path.write_text(json.dumps(old) + "\n")
        result = subprocess.run(
            [sys.executable, E.__file__, "--from", path],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode != 0 and "recompute" in result.stderr

    small = R.Row("sdql", "batax", "ref-multi", 12, 12)
    full = R.Row("sdql", "batax", "ref-multi", 12, 44)
    small.checks, full.checks = "off", None
    small.substitution = full.substitution = "snapshot"
    head, table = R.pivot([small, full], ("ref-multi",))
    assert len(table) == 2 and {row[3] for row in table} == {"12", "44"}
    assert "subst snapshot" in head[4] and "checks off/unknown" in head[4]


def graph_failure_reasons():
    def row():
        return R.Row("regression", "diagnostics", "encoding", 1)

    with tempfile.TemporaryDirectory(prefix="slotted-eval-errors-") as tmp, patch.object(V, "SCRATCH", Path(tmp)):
        failed = row()
        with patch.object(subprocess, "run", side_effect=subprocess.TimeoutExpired("egglog", 1)):
            V.encoding_counts("", "timeout", X.LANG, failed, 1)
        assert "exceeded timeout" in failed.graph_issue
        assert R.Row.from_dict(failed.as_dict("test")).graph_issue == failed.graph_issue
        assert failed.graph_issue in R.graph_cell(failed)

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


def nested_comparison_policy():
    enc, ref = (
        R.Row("regression", "nested-policy", side, 1) for side in ("encoding-no-aliasing", "ref-nested-snapshot")
    )
    for row in (enc, ref):
        row.goal, row.classes, row.nodes = "yes", 1, 1
    sides = (enc.side, ref.side)
    with tempfile.TemporaryDirectory(prefix="slotted-nested-gate-") as tmp:
        path = Path(tmp) / "rows.jsonl"
        for verdict in ("isomorphic", "different: node sets", "inconclusive: cap", None):
            enc.vs_ref = {} if verdict is None else {ref.side: R.Comparison(enc.observation, ref.observation, verdict)}
            assert V.successful([enc, ref], sides, True) == (verdict == "isomorphic")
            assert V.successful([enc, ref], sides, False)
            path.write_text("".join(json.dumps(cached_record(r, "test")) + "\n" for r in (enc, ref)))
            result = subprocess.run(
                [sys.executable, E.__file__, "--from", path, "--side", ",".join(sides)],
                capture_output=True,
                text=True,
                timeout=30,
            )
            assert result.returncode == (0 if verdict == "isomorphic" else 1), result.stderr
            assert (R.ERROR_TITLE in result.stdout) == (verdict != "isomorphic")
            if verdict != "isomorphic":
                assert "encoding-no-aliasing vs ref-nested-snapshot" in result.stdout.split(R.ERROR_TITLE)[1]
    enc.vs_ref = {ref.side: R.Comparison(enc.observation, ref.observation, "isomorphic")}
    assert not V.successful([enc], sides, True)
    with patch.object(ref, "nodes", 2):
        assert not V.successful([enc, ref], sides, True)

    # Both encodings share one workload but have distinct observation identities.
    full = R.Row("regression", enc.case, "encoding", 1)
    with tempfile.TemporaryDirectory(prefix="slotted-nested-report-") as tmp:
        path = Path(tmp) / "rows.jsonl"
        path.write_text("".join(json.dumps(cached_record(r, "test")) + "\n" for r in (enc, ref, full)))
        loaded, _ = E.load_rows(path, merged=True)
        assert len(loaded) == 3 and loaded[0].verdict(loaded[1]) == "isomorphic"
        for long in (False, True):
            sections = R.report_sections(loaded, R.SIDES, long)
            assert sections[0][2] == ("Benchmark", "egglog", "ref-multi")
            assert sections[1][2] == ("Benchmark", "egglog-no-aliasing", "ref-nested")
            assert "egglog-no-aliasing" in R.markdown(*sections[-1][2:])
            assert "encoding" not in R.markdown(*sections[-1][2:])
        head, table = R.pivot(loaded, R.SIDES)
        assert len(table) == 1
        cells = dict(zip(head, table[0], strict=True))
        assert cells["egglog-no-aliasing vs ref-nested-snapshot"] == "isomorphic"
        assert len(R.summary(loaded, R.SIDES)[1]) == 1


def combined_comparisons():
    rows = E.collect_workload(
        W.sdql_workload("mmm_sum", "1st"),
        argparse.Namespace(counts=True, timeout=30, jobs=1),
        R.SIDES,
        CHECK_CONFIG,
        R.quiet_progress,
    )
    assert V.successful(rows, R.SIDES, True), [r.as_dict("test") for r in rows]
    by_side = {r.side: r for r in rows}
    for missing in R.SIDES:
        partial = [r for r in rows if r.side != missing]
        for counts in (False, True):
            assert not V.successful(partial, R.SIDES, counts)
    head, table = R.pivot(rows, R.SIDES)
    assert len(table) == 1
    cells = dict(zip(head, table[0], strict=True))
    for encoding, reference in R.EXACT_PAIRS.items():
        enc, ref = by_side[encoding], by_side[reference]
        assert cells[f"{R.side_label(encoding)} vs {reference}"] == "isomorphic"
        # The other encoding's successful comparison cannot mask this one's failure.
        for verdict in ("different: node sets", "inconclusive: cap"):
            comparison = R.Comparison(enc.observation, ref.observation, verdict)
            with patch.dict(enc.vs_ref, {reference: comparison}):
                assert not V.successful(rows, R.SIDES, True)
                assert V.successful(rows, R.SIDES, False)
                assert V.failures(rows, R.SIDES, True) == [
                    f"ΣMMM (1st) [{enc.rounds} rounds]: {encoding} vs {reference}: {verdict}"
                ]
                head, table = R.pivot(rows, R.SIDES)
                assert dict(zip(head, table[0], strict=True))[f"{R.side_label(encoding)} vs {reference}"] == verdict
        with patch.object(enc, "observation", "new-run"):
            assert not V.successful(rows, R.SIDES, True)
            assert "selected observations have not been compared" in V.failures(rows, R.SIDES, True)[0]

    # Syntactic nested graphs remain diagnostic; their differences do not fail an
    # otherwise valid report or masquerade as failure of the required snapshot pair.
    enc, ref = by_side["encoding-no-aliasing"], by_side["ref-nested"]
    with patch.dict(enc.vs_ref, {ref.side: R.Comparison(enc.observation, ref.observation, "different: node sets")}):
        assert not V.failures(rows, R.SIDES, True)

    with tempfile.TemporaryDirectory(prefix="slotted-combined-report-") as tmp:
        path = Path(tmp) / "rows.jsonl"
        path.write_text("".join(json.dumps(cached_record(r, "combined")) + "\n" for r in rows))
        # Preserve both certificates across loading, and keep the old flag usable.
        for extra in ([], ["--nested-compat", "--side", "encoding,ref-nested"]):
            result = subprocess.run(
                [sys.executable, E.__file__, "--from", path, *extra],
                capture_output=True,
                text=True,
                timeout=30,
            )
            assert result.returncode == 0, (result.stdout, result.stderr)
            assert "egglog-no-aliasing" in result.stdout and "ref-nested-snapshot" in result.stdout

        newer = R.Row.from_dict(by_side["encoding"].as_dict("newer"))
        newer.observation = "different-encoding-run"
        with path.open("a") as f:
            f.write(json.dumps(cached_record(newer, "newer")) + "\n")
        loaded, _ = E.load_rows(path, merged=True)
        assert len(loaded) == len(R.SIDES)
        group = {r.side: r for r in loaded}
        assert group["encoding-no-aliasing"].verdict(group["ref-nested-snapshot"]) == "isomorphic"
        assert group["encoding"].verdict(group["ref-multi"]).startswith("inconclusive:")
        assert not V.successful(loaded, R.SIDES, True)


def zero_round_budget():
    """An explicit zero must not silently run the paper's default budget."""
    args = argparse.Namespace(
        no_build=True,
        study="all",
        params=[0],
        kernel=["mmm"],
        phase=["1st"],
        rules=44,
        rounds=0,
        counts=False,
        timeout=30,
        jobs=1,
    )
    rows = E.collect(args, ("ref-multi",), argparse.ArgumentParser(), config=CHECK_CONFIG)
    assert len(rows) == 2
    assert all(row.rounds == 0 and row.goal == "no" for row in rows), [vars(row) for row in rows]


def parallel_collection():
    """Spawned workers preserve both languages' counts, verdicts, and configuration."""
    args = argparse.Namespace(
        no_build=True,
        study="all",
        params=[0],
        kernel=["mmm_sum"],
        phase=["1st"],
        rules=44,
        rounds=2,
        counts=True,
        timeout=60,
        jobs=1,
    )

    def evidence(rows):
        return [
            (
                r.workload(),
                r.side,
                r.goal,
                r.classes,
                r.nodes,
                r.saturated,
                r.substitution,
                r.graph_issue,
                [(side, c.verdict) for side, c in r.vs_ref.items()],
            )
            for r in rows
        ]

    serial = E.collect(args, R.SIDES, argparse.ArgumentParser(), config=CHECK_CONFIG)
    args.jobs = 2
    parallel = E.collect(args, R.SIDES, argparse.ArgumentParser(), config=CHECK_CONFIG)
    # The small round budget misses the array goal, even though its graphs agree.
    assert not V.successful(serial, R.SIDES, True) and not V.successful(parallel, R.SIDES, True)
    assert evidence(serial) == evidence(parallel)
    assert all(r.graph is None for r in parallel)
    loaded = [R.Row.from_dict(r.as_dict("parallel")) for r in parallel]
    assert all(r.jobs == 2 for r in loaded)
    assert not V.successful(loaded, R.SIDES, True)
    sections = R.report_sections(loaded, R.SIDES)
    notes = " ".join(note for _, note, _, _ in sections)
    assert "contention" in notes and "worker limits are in the full report" in notes
    for _, _, head, table in sections[:2]:
        assert len(head) == 3 and len(table) == 2 and all(len(row) == 3 for row in table)

    # The child must receive CLI configuration, not its freshly imported defaults.
    args.study = "array"
    sides = ("encoding-no-aliasing", "ref-nested-snapshot")
    limited = E.collect(
        args, sides, argparse.ArgumentParser(), config=E.Config(CHECK_CONFIG.egglog, CHECK_CONFIG.xmulti, group_cap=0)
    )
    enc, ref = limited
    assert enc.goal == ref.goal == "no"
    assert V.compare_counts(enc, ref) == "same counts"
    assert ref.graph_issue and "REFERENCE_LIMIT" in ref.graph_issue
    assert enc.verdict(ref).startswith("inconclusive:")
    assert not V.successful(limited, sides, True)


def import_without_compilation():
    """Workload definitions and reporting must not compile the unused Python encoding."""
    code = """
import importlib
import sys
from unittest.mock import patch
sys.path[:0] = ["slotted", "slotted/xdiff"]
compiler = importlib.import_module("slotted-egglog")
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
            (row,) = E.collect_workload(workload, args, sides, CHECK_CONFIG, R.quiet_progress)
        assert process.call_count == (2 if counts else 1)
        assert row.goal == "no" and row.seconds is not None
        assert (row.classes, row.nodes) == ((10, 20) if counts else (None, None))
        assert not V.successful([row], sides, counts)

    args.counts = True
    for failed in (
        subprocess.TimeoutExpired("xmulti", 30),
        subprocess.CompletedProcess([], 1, "", "reference error"),
        subprocess.CompletedProcess([], 0, "GOAL yes\nCONFIG substitution=syntactic\n", ""),
    ):
        with patch.object(subprocess, "run", side_effect=[failed]) as process:
            (row,) = E.collect_workload(workload, args, sides, CHECK_CONFIG, R.quiet_progress)
        assert process.call_count == 1
        assert row.graph_issue and row.classes is None and row.nodes is None
        assert not V.successful([row], sides, True)


def main():
    import_without_compilation()
    separate_timing_and_graph_runs()
    substitution_policies()
    nested_comparison_policy()
    combined_comparisons()
    merged_observations()
    graph_failure_reasons()
    goal_reporting()
    summary_reporting()
    zero_round_budget()
    parallel_collection()
    substitution_refresh()
    coset_direction()
    complete_refinement()
    count_round_budget()
    raw_node_counts()
    exit_status(*verdicts())
    print("OK: complete refinement, separate count checks, exact graph verdicts, and evaluation exit statuses")


if __name__ == "__main__":
    main()
