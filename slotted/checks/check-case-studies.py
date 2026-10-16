#!/usr/bin/env python3
"""Run Rudi's first-order logic fixtures against ref-multi, including exact graphs.

The fixtures are the source of the declarations, rules, initial equations, round
budget, and goal. This adapter accepts one initialization phase, one run, and one
final equality check; other command sequences fail explicitly. Ref-nested cannot
express their multipattern side conditions and is reported as unsupported.

    python3 slotted/checks/check-case-studies.py
"""

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT), str(ROOT / "slotted"), str(ROOT / "slotted/xdiff")]
import eval_observation as observation  # noqa: E402
import eval_run as run  # noqa: E402
import eval_verify as verify  # noqa: E402
import reference as syntax  # noqa: E402

CONFIG = run.Config(
    egglog=ROOT / "target/debug/egglog-experimental",
    xmulti=ROOT / "slotted/xmulti/target/debug/xmulti",
)


def fixture(path):
    src = syntax.Source(path)
    if len(src.sorts) != 1:
        raise ValueError(f"{path.name}: reference case studies require one equality sort")
    # These constructors have identical names and column order in xmulti's L.
    for op in src.lang.ops.values():
        op.ref = op.ctor

    rules, unions, goal, rounds = [], [], None, None
    for form, _ in src.body:
        match form:
            case ["sort", _] if rounds is None:
                pass
            case ["rewrite", *_] if rounds is None:
                rules.append(form)
            case ["union", a, b] if rounds is None:
                unions.append((a, b))
            case ["run", n] if rounds is None:
                rounds = int(n)
            case ["check", ["=", a, b]] if rounds is not None and goal is None:
                goal = a, b
            case _:
                raise ValueError(f"{path.name}: unsupported reference fixture command: {syntax.render(form)}")
    if rounds is None or goal is None or not rules:
        raise ValueError(f"{path.name}: expected rewrites, one run, and one final equality check")
    # The oracle's goal compares to its first seed. Require that seed to be an
    # existing input, so observing the goal cannot add its answer before rewriting.
    if not any(goal[0] == term for pair in unions for term in pair):
        raise ValueError(f"{path.name}: the goal's left side must be an initial union term")

    def term(form):
        return src.lang.sexpr(src.term(form, ground=True))

    spec = [f"rounds {rounds}", f"term {term(goal[0])}", "term (var $0)"]
    # Rust initializes one variable class even for a closed program.
    spec.extend(f"union {term(a)} {term(b)}" for a, b in unions)
    for rule in rules:
        spec.extend(syntax.rule_lines(src, src.lang, rule))
    spec.append(f"goal {term(goal[1])}")
    try:
        for rule in rules:
            syntax.rule_lines(src, src.lang, rule, nested=True)
    except syntax.NestedPatternUnsupported as exc:
        unsupported = str(exc)
    else:
        raise ValueError(f"{path.name}: expected a multipattern case study unsupported by ref-nested")
    # Checks may materialize their terms. Compare the graph before observing the
    # goal, at exactly the fixture's rewrite budget, without seeding the answer.
    graph_program = (
        "\n".join(syntax.render(form) for form in syntax.parse(path.read_text()) if form[0] != "check") + "\n"
    )
    return src.lang, rounds, "\n".join(spec) + "\n", graph_program, unsupported


def check(path):
    lang, rounds, spec, graph_program, unsupported = fixture(path)
    enc, ref = (observation.Row("logic", path.stem, side, rounds) for side in ("encoding", "ref-multi"))
    run.run_egglog(path.read_text(), path.stem, enc, 60, config=CONFIG)
    run.run_reference(spec, ref, 60, config=CONFIG)
    assert enc.goal == ref.goal == "yes", (path.name, enc.goal, ref.goal, ref.graph_issue)
    verify.encoding_counts(graph_program, path.stem, lang, enc, 60, config=CONFIG)
    verify.reference_counts(spec, ref, 60, config=CONFIG)
    verify.compare([enc, ref])
    assert verify.compare_counts(enc, ref) == "same counts", (path.name, enc.as_dict(""), ref.as_dict(""))
    assert enc.verdict(ref) == "isomorphic", (path.name, enc.verdict(ref), enc.graph_issue, ref.graph_issue)
    print(
        f"  ok   {path.name}: goal proved on both; {enc.classes} classes, {enc.nodes} nodes; isomorphic\n"
        f"       ref-nested: unsupported ({unsupported})",
        flush=True,
    )


def main():
    paths = sorted((ROOT / "slotted/tests/rudi").glob("first-order-logic*.egg"))
    assert paths, "no first-order logic case studies found"
    for path in paths:
        check(path)
    print(f"OK: {len(paths)}/{len(paths)} case studies match ref-multi; ref-nested unsupported")


if __name__ == "__main__":
    main()
