#!/usr/bin/env python3
"""Regressions for complete refinement and trustworthy evaluation verdicts."""

import json
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]
import eval as E  # noqa: E402
import partition as PT  # noqa: E402
import xdiff as X  # noqa: E402


def graphs(name, program, spec):
    enc, ref = (E.Row("regression", name, side, 1) for side in ("encoding", "ref-multi"))
    E.encoding_counts(program, name, X.LANG, enc, 60)
    E.run_reference(spec, ref, 60, True)
    assert enc.graph is not None and ref.dump is not None, (name, enc.as_dict("test"), ref.as_dict("test"))
    E.compare([enc, ref])
    return enc, ref


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
    assert enc.vs_ref["ref-multi"] == "isomorphic", enc.vs_ref
    assert enc.graph.summary() == (77, 280) == (ref.classes, ref.nodes)


def verdicts():
    # Same class/node counts on both sides; only the symmetry group differs.
    # Exercise both sides of the former 40-class cutoff.
    for depth in (0, 41):
        enc, ref = symmetry_case(depth, True)
        assert (enc.classes, enc.nodes) == (ref.classes, ref.nodes)
        assert enc.vs_ref["ref-multi"].startswith("different:"), enc.vs_ref

    enc, ref = symmetry_case(41, False)
    assert enc.classes > 40 and enc.vs_ref["ref-multi"] == "isomorphic", enc.vs_ref
    with patch.object(E.ISO, "SEARCH_CAP", 0):
        E.compare([enc, ref])
    assert enc.vs_ref["ref-multi"].startswith("inconclusive:"), enc.vs_ref
    assert E.compare_counts(enc, ref) == "same counts"
    assert f"[{enc.classes}/{enc.nodes}" in E.timing_cell(enc)

    witness, why = E.ISO.find_isomorphism(E.ISO.parse_reference(ref.dump), enc.graph)
    assert witness is not None, why
    # Even a broken checker that always accepts must not override the simple counts.
    for side in (enc, ref):
        for name in ("classes", "nodes"):
            for value in (getattr(side, name) + 1, None):
                with (
                    patch.object(side, name, value),
                    patch.object(E.ISO, "find_isomorphism", return_value=(witness, None)) as search,
                    patch.object(E.ISO, "verify", return_value=None) as verify,
                ):
                    E.compare([enc, ref])
                    prefix = "inconclusive: counts unavailable" if value is None else f"different: {name} "
                    assert enc.vs_ref["ref-multi"].startswith(prefix), enc.vs_ref
                    search.assert_not_called()
                    verify.assert_not_called()
    with (
        patch.object(E.ISO, "find_isomorphism", return_value=(witness, None)),
        patch.object(E.ISO, "verify", return_value="deliberately invalid witness"),
    ):
        E.compare([enc, ref])
    assert enc.vs_ref["ref-multi"].startswith("inconclusive: witness rejected"), enc.vs_ref

    saved = ref.dump
    for unavailable in (None, "CLASS c SLOTS x\nGROUP c ?\n"):
        ref.dump = unavailable
        E.compare([enc, ref])
        assert enc.vs_ref["ref-multi"].startswith("inconclusive:"), enc.vs_ref
    ref.dump, enc.graph = saved, None
    E.compare([enc, ref])
    assert enc.vs_ref["ref-multi"] == "inconclusive: no encoding graph"
    assert PT.verdict({"split": {}, "merged": {}}, 0, True) == "same partition (graph equality unverified)"
    return enc, ref


def exit_status(enc, ref):
    enc.goal = ref.goal = "yes"
    sides = ("encoding", "ref-multi")
    assert not E.successful([], sides, True)
    assert not E.successful([enc], sides, True)
    with tempfile.TemporaryDirectory(prefix="slotted-eval-check-") as tmp:
        path = Path(tmp) / "report.jsonl"
        for verdict in ("isomorphic", "different: symmetry group", "inconclusive: search cap", "same rows", None):
            enc.vs_ref = {} if verdict is None else {"ref-multi": verdict}
            assert E.successful([enc, ref], sides, True) == (verdict == "isomorphic")
            assert E.successful([enc, ref], sides, False)  # explicitly goal-only
            path.write_text("".join(json.dumps(row.as_dict("regression")) + "\n" for row in (enc, ref)))
            result = subprocess.run(
                [sys.executable, str(ROOT / "slotted" / "eval.py"), "--from", str(path), "--side", ",".join(sides)],
                capture_output=True,
                text=True,
                timeout=30,
            )
            assert result.returncode == (0 if verdict == "isomorphic" else 1), (verdict, result.stderr)
            if verdict == "same rows":
                assert "inconclusive: legacy same rows (no witness)" in result.stdout
        # Loading a report also checks counts, even if its stored verdict is positive.
        enc.vs_ref = {"ref-multi": "isomorphic"}
        for side in (enc, ref):
            for name in ("classes", "nodes"):
                for value in (getattr(side, name) + 1, None):
                    with patch.object(side, name, value):
                        assert not E.successful([enc, ref], sides, True)
                        assert E.successful([enc, ref], sides, False)
                        path.write_text("".join(json.dumps(row.as_dict("regression")) + "\n" for row in (enc, ref)))
                        result = subprocess.run(
                            [
                                sys.executable,
                                str(ROOT / "slotted" / "eval.py"),
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
    enc.vs_ref = {"ref-multi": "isomorphic"}
    ref.goal = "no"
    assert not E.successful([enc, ref], sides, True)


def main():
    # The suite builds these checked debug binaries; performance eval uses release.
    E.EGGLOG = ROOT / "target" / "debug" / "egglog"
    E.XMULTI = ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti"
    complete_refinement()
    exit_status(*verdicts())
    print("OK: complete refinement, separate count checks, exact graph verdicts, and evaluation exit statuses")


if __name__ == "__main__":
    main()
