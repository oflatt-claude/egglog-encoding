#!/usr/bin/env python3
"""Compare the Rust source pass with the independent Python implementation.

Run every source fixture, then compare raw constructor counts and a verified
class/slot/group/node isomorphism for each carrier. The Python implementation is
retained as a migration oracle; the public CLI and paper evaluation use Rust.
"""

import argparse
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]
import isomorphism as ISO  # noqa: E402
import surface  # noqa: E402

sc = __import__("slotted-egglog")
enc = __import__("slotted-encoder")
runner = __import__("run-slotted-tests")
refusals = __import__("check-refusals")


def dump(binary, text, path, flags=()):
    path.write_text(text)
    result = subprocess.run(
        [str(ROOT / "target" / "debug" / binary), *flags, "--to-json", *ISO.SERIALIZE_LIMITS, str(path)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )
    assert result.returncode == 0, (path, result.stderr)
    assert not ISO.incomplete_serialization(result.stderr), result.stderr
    return json.loads(path.with_suffix(".json").read_text())


def carrier_graph(doc, source, sort):
    """Select one independent carrier for the single-carrier graph checker."""
    symbols = source.carriers[sort]
    ops = {name: op for name, op in source.lang.ops.items() if op.sort == sort}
    lang = enc.TermLang(ops)
    names = {op.ctor for op in ops.values()} | {symbols.var}
    raw = sum(n["op"] in names for n in doc["nodes"].values())
    rename = {}
    for other_sort, other in source.carriers.items():
        for field in ("var", "renames", "class_slots", "group"):
            rename[getattr(other, field)] = getattr(ISO.SYM, field) if other_sort == sort else "<other carrier>"
    for op in source.lang.ops.values():
        if op.sort != sort:
            rename[op.ctor] = "<other carrier>"
    selected = {**doc, "nodes": {k: {**n, "op": rename.get(n["op"], n["op"])} for k, n in doc["nodes"].items()}}
    graph, issues = ISO.build_encoding_graph(selected, lang)
    assert not issues, issues
    assert graph.summary()[1] == raw, (graph.summary(), raw)
    return graph


def compare_file(path, tmp, nested=False):
    source = sc.Source(path)
    # Maintenance only; this does not execute another user rewrite round.
    old = sc.compile_source(source, nested_compat=nested) + sc.schedule(0, 0)
    legacy = dump("egglog", old, Path(tmp) / "legacy.egg")
    flags = ["--slotted", *(["--slotted-no-aliasing"] if nested else [])]
    native = dump("egglog-experimental", path.read_text() + "\n(run 0)\n", Path(tmp) / "native.egg", flags)
    for sort in source.carriers:
        a, b = (carrier_graph(d, source, sort) for d in (legacy, native))
        assert a.summary() == b.summary(), (path, sort, a.summary(), b.summary())
        witness, why = ISO.find_isomorphism(a, b)
        assert witness is not None, (path, sort, why)
        assert not ISO.verify(a, b, *witness), (path, sort, "invalid witness")
    return len(source.carriers)


def fuzz(tmp, count):
    rng = random.Random(0)
    compared = skipped = multi = 0
    path = Path(tmp) / "fuzz.egg"

    def term(t):
        if t[0] == "var":
            return f"${t[1]}"
        op = surface.X.LANG.ops[t[0]]
        args = []
        for kind, arg in zip(op.arg_kinds(), t[1:], strict=True):
            if kind is enc.CHILD:
                args.append(term(arg))
            elif kind is enc.BINDER:
                args.append(f"${surface.X.LANG.slot(arg)}")
            else:
                args.append(json.dumps(arg))
        return "(" + " ".join([op.ctor, *args]) + ")"

    for i in range(count * 4):
        if compared == count:
            break
        case = surface.X.rand_case(rng, i)
        try:
            rules = list(dict.fromkeys(surface.render(a, act, c) for a, act, c in case.rules if a))
        except surface.Unexpressible:
            skipped += 1
            continue
        if not rules:
            skipped += 1
            continue
        text = ['(include "slotted/languages/toy.egg")', *rules]
        text += [f"(let seed{j} {term(t)})" for j, t in enumerate(case.terms + case.probes)]
        text += [f"(union {term(a)} {term(b)})" for a, b in case.unions]
        text.append(f"(run {case.rounds})")
        path.write_text("\n".join(text))
        compare_file(path, tmp)
        compared += 1
        multi += any(len(a) > 1 for a, _, _ in case.rules)
    assert compared == count and multi >= count // 2, (compared, skipped, multi)
    print(f"OK: {compared} generated programs agree, including {multi} multipatterns; {skipped} unexpressible")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fuzz", type=int, default=0)
    args = parser.parse_args()
    paths = runner.slotted_sources()
    assert len(paths) >= 42, "source corpus shrank"
    carriers = 0
    with tempfile.TemporaryDirectory(prefix="slotted-rust-") as tmp:
        if args.fuzz:
            fuzz(tmp, args.fuzz)
            return
        for path in paths:
            carriers += compare_file(path, tmp, runner.NESTED in path.parents)
            print(f"  ok {path.relative_to(ROOT)}", file=sys.stderr, flush=True)
        for name, text, _phrase in refusals.CASES:
            path = Path(tmp) / "refusal.egg"
            path.write_text(text)
            result = subprocess.run(
                [str(ROOT / "target" / "debug" / "egglog-experimental"), "--slotted", str(path)],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=30,
            )
            assert result.returncode != 0, (name, "accepted")
            assert "panicked" not in result.stderr and "Traceback" not in result.stderr, (name, result.stderr)
            assert "ERROR" in result.stderr, (name, result.stderr)
    print(
        f"OK: Rust and Python agree on {len(paths)} source fixtures, {carriers} carrier graphs; "
        f"{len(refusals.CASES)} refusals hold"
    )


if __name__ == "__main__":
    main()
