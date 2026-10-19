"""Regression checks for leader migration, cache freshness, and substitution."""

import argparse
import itertools
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import reference as syntax  # noqa: E402
from slotted import test_program as driver  # noqa: E402
from slotted.benchmarks import sdql as pf  # noqa: E402
from slotted.xdiff import isomorphism as ISO  # noqa: E402


def leader_program(constructors, reverse_union, symmetric):
    maintenance = driver.maintenance()
    # Values start in order a < b < c. First c follows b under a swap. Unioning
    # c into a then leaves the obsolete edge a -> b, while a is the new leader.
    # Clearing followers in that same rule batch used to delete a's identity and
    # group. Unchanged ClassSlots/Equated rows do not re-fire to restore them.
    lines = [driver.machinery("toy"), "(let $v (SlottedVar_0 0))"]
    lines += [
        f"(let ${name} ({ctor} (map-of 0 0) $v (map-of 0 1) $v))"
        for name, ctor in zip("abc", constructors, strict=True)
    ]
    lines += [maintenance, "(Equated_0 $c (map-of 0 1 1 0) $b)", maintenance]
    if symmetric:
        lines += ["(Equated_0 $a (map-of 0 1 1 0) $a)", maintenance]
    lines += [
        "(union $c $a)" if reverse_union else "(union $a $c)",
        maintenance,
        "(check (RenamesToLeader_0 $a (map-of 0 0 1 1) $a))",
        "(check (= g (EclassGroup_0 $a)) (set-contains g (map-of 0 0 1 1)))",
    ]
    if symmetric:
        lines.append("(check (= g (EclassGroup_0 $a)) (set-contains g (map-of 0 1 1 0)))")
    return "\n".join(lines)


def leaders():
    """Leader reversals must retain identity renamings and known symmetries."""
    cases = 0
    with tempfile.TemporaryDirectory(prefix="slotted-leader-maintenance-") as scratch:
        path = Path(scratch) / "case.egg"
        for args in itertools.product(itertools.permutations("FGH"), (False, True), (False, True)):
            path.write_text(leader_program(*args))
            result = subprocess.run(
                [str(driver.EGGLOG), "--slotted-encoded", str(path)],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=ROOT,
            )
            assert result.returncode == 0, (args, result.stderr)
            cases += 1
    print(f"OK: {cases} leader reversals preserve identities and symmetries")


def shape_program(reverse, order):
    maintenance = driver.maintenance()
    children = [
        "(let $a (F (map-of 0 0) $v (map-of 0 1) $v))",
        "(let $b (G (map-of 0 0) $v (map-of 0 1) $v))",
    ]
    if reverse:
        children.reverse()
    parents = [
        "(H (map-of 0 1 1 0) $a (map-of 0 0) $v)",
        "(H (map-of 0 0 1 1) $b (map-of 0 0) $v)",
        "(H (map-of 0 1 1 0) $b (map-of 0 0) $v)",
    ]
    # Cache shapes for two different children, only one of which has a swap.
    # The native union makes the old row-based cache keys collide. In the failing
    # order an obsolete shape overwrote a fresh one after its producer had run.
    lines = [
        driver.machinery("toy"),
        "(let $v (SlottedVar_0 0))",
        *children,
        maintenance,
        "(Equated_0 $b (map-of 0 1 1 0) $b)",
        maintenance,
        *(parents[i] for i in order),
        maintenance,
        "(union $a $b)",
        maintenance,
        # Reinsert an equivalent parent. Stale shapes used to leave two H rows.
        parents[1].replace("$b", "$a"),
        maintenance,
        "(print-size H)",
    ]
    cached = "(_shapeof_H m1 g1 m2 g2)"
    lines.append(f"""
(ruleset observe)
(relation Fresh ())
(relation ObservedReadings ())
(relation StaleReadings ())
(rule ((= c (H m1 c1 m2 c2))
       (= g1 (EclassGroup_0 c1)) (= g2 (EclassGroup_0 c2))
       (= direct (node-shape (vec-of m1 m2) (vec-of g1 g2)))
       (= (values s1 s2 back syms) {cached})
       (= s1 (vec-get direct 0)) (= s2 (vec-get direct 1))
       (= back (vec-get direct 2)) (= syms (symmetries-of direct 3)))
      ((Fresh)) :ruleset observe)
(rule ((= stored (CosetReps_0 c pinned))) ((ObservedReadings)) :ruleset observe)
(rule ((= stored (CosetReps_0 c pinned)) (= grp (EclassGroup_0 c))
       (!= stored (group-coset-reps grp pinned)))
      ((StaleReadings)) :ruleset observe)
(run observe 1)
(check (Fresh))
(check (ObservedReadings))
(print-size StaleReadings)
""")
    return "\n".join(lines)


def shapes():
    """Union order and cache-key collisions must not leave duplicate node shapes."""
    cases = 0
    with tempfile.TemporaryDirectory(prefix="slotted-shape-cache-") as scratch:
        path = Path(scratch) / "case.egg"
        for reverse, order in itertools.product((False, True), itertools.permutations(range(3))):
            path.write_text(shape_program(reverse, order))
            result = subprocess.run(
                [str(driver.EGGLOG), "--slotted-encoded", str(path)],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=ROOT,
            )
            assert result.returncode == 0, (reverse, order, result.stderr)
            assert result.stdout.split() == ["1", "0"], (reverse, order, result.stdout)
            cases += 1
    print(f"OK: {cases} child-union orders preserve fresh shapes and leave one parent node")


EGGLOG = ROOT / "target" / "debug" / "egglog-experimental"
TEST = ROOT / "slotted" / "tests" / "sdql-paper-mmm.egg"
SCRATCH = ROOT / "target" / "slotted"
RUNS = 4
ROUNDS = (4, 12)


def substitution_program(rounds):
    """The MMM subset test's rules and input, run for `rounds`, with the target added after."""
    forms = syntax.parse(TEST.read_text())
    keep = [f for f in forms if isinstance(f, list) and f[0] in ("include", "rewrite")]
    inp, tgt = pf.workload("mmm", "2nd")
    keep += [["let", "paper-input", inp], ["run", str(rounds)], ["let", "paper-target", tgt], ["run", "0"]]
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"subst-determinism-{rounds}.egg"
    path.write_text("\n".join(syntax.render(f) for f in keep) + "\n")
    return path


def compare_graphs(first, graph, issues):
    """Reject unreadable graphs, unequal counts, and missing/invalid witnesses."""
    if issues:
        return f"unreadable graph: {issues[:2]}"
    if first is None:
        return None
    if first.summary() != graph.summary():
        return f"class/node counts differ: {first.summary()} vs {graph.summary()}"
    try:
        witness, why = ISO.find_isomorphism(first, graph)
        if witness is None:
            return f"no isomorphism: {why}"
        bad = ISO.verify(first, graph, *witness)
        return f"invalid isomorphism: {bad}" if bad is not None else None
    except ISO.IsomorphismLimit as exc:
        return f"isomorphism inconclusive: {exc}"


def substitution_selftest():
    """The determinism gate must fail closed, even when counts agree."""
    from unittest.mock import patch

    def graph(op, cid):
        g = ISO.Graph()
        g.add_class(cid, [])
        g.nodes[cid] = [(op, ())]
        g.close_groups()
        return g

    first, renamed, different = graph("left", "a"), graph("left", "b"), graph("right", "b")
    assert compare_graphs(None, first, ["reader error"]) is not None
    assert compare_graphs(first, first, ["reader error"]) is not None
    assert compare_graphs(first, different, []) is not None
    assert compare_graphs(first, renamed, []) is None
    with patch.object(ISO, "find_isomorphism", side_effect=ISO.IsomorphismLimit("test bound")):
        assert compare_graphs(first, renamed, []) is not None
    with patch.object(ISO, "verify", return_value="test invalid witness"):
        assert compare_graphs(first, renamed, []) is not None


def substitution():
    """Repeated fresh processes must produce isomorphic substitution results."""
    substitution_selftest()
    if not EGGLOG.is_file():
        print(f"FAIL: {EGGLOG.relative_to(ROOT)} not built")
        return 1
    decls = pf.RULES.with_name("sdql.egg")
    lang = syntax.language(decls, decls.with_suffix(".ref"))
    bad = []
    for rounds in ROUNDS:
        compiled = substitution_program(rounds)
        json_path = compiled.with_suffix(".json")
        first = None
        for _ in range(RUNS):
            json_path.unlink(missing_ok=True)
            run = subprocess.run(
                [str(EGGLOG), "--slotted", "--to-json", *ISO.SERIALIZE_LIMITS, str(compiled)],
                capture_output=True,
                text=True,
                cwd=ROOT,
                timeout=900,
            )
            if run.returncode or not json_path.exists():
                detail = (run.stderr.strip().splitlines() or [f"exit {run.returncode}"])[-1]
                bad.append(f"{rounds} rounds: run failed: {detail[:120]}")
                break
            graph, issues = ISO.build_encoding_graph(json.loads(json_path.read_text()), lang)
            issue = compare_graphs(first, graph, issues)
            if issue is not None:
                bad.append(f"{rounds} rounds: {issue}")
                break
            if first is None:
                first = graph
        compiled.unlink(missing_ok=True)
        json_path.unlink(missing_ok=True)
    if bad:
        for line in bad:
            print("FAIL:", line)
        return 1
    print(f"OK: {len(ROUNDS)}/{len(ROUNDS)} round counts match counts and verified isomorphism over {RUNS} runs each")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("leaders", "shapes", "substitution"))
    args = parser.parse_args()
    checks = {"leaders": leaders, "shapes": shapes, "substitution": substitution}
    return checks[args.check]()


if __name__ == "__main__":
    sys.exit(main())
