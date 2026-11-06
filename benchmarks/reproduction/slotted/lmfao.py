"""Explicit reproduction of the LMFAO batch inputs; never run by collection."""

import json

from benchmarking.lmfao import model as lmfao

from . import ROOT, sdql
from . import reference as syntax
from .workloads import Workload, ctor_lines

RULES = ROOT / "benchmarks/lmfao/batch.egg"


def symbol(name):
    return ["Symbol", json.dumps(name)]


def balanced(op, terms):
    assert terms
    while len(terms) > 1:
        terms = [[op, *terms[i : i + 2]] if i + 1 < len(terms) else terms[i] for i in range(0, len(terms), 2)]
    return terms[0]


def join_term():
    """Return a natural bag join preserving fields and product multiplicities."""
    attrs, relations, _ = lmfao.schema()
    owners = {}
    stages = []
    for name, columns in relations.items():
        row, count = f"${name}_row", f"${name}_count"
        conditions = []
        for col in columns:
            if col in owners:
                conditions.append(["Equality", ["Get", row, symbol(col)], ["Get", owners[col], symbol(col)]])
            else:
                owners[col] = row
        stages.append((name, row, count, conditions))
    record = balanced("Add", [["Sing", symbol(col), ["Get", owners[col], symbol(col)]] for col, _ in attrs])
    weight = balanced("Mult", [count for _, _, count, _ in stages])
    result = ["Sing", record, weight]
    for name, row, count, conditions in reversed(stages):
        for condition in reversed(conditions):
            result = ["IfThen", condition, result]
        result = ["Sum", symbol(name), row, count, result]
    return result


def aggregate(query, domain, index):
    row, count = f"$q{index}_row", f"$q{index}_count"
    weight = balanced("Mult", [count, *[["Get", row, symbol(f)] for f in query.factors]])
    if query.groups:
        key = balanced("Pair", [["Get", row, symbol(f)] for f in query.groups])
        weight = ["Sing", key, weight]
    return ["Sum", domain, row, count, weight]


def source():
    src = syntax.Source(RULES)
    base = sdql.reference_language()
    for name, op in src.lang.ops.items():
        op.ref = base.ops[name].ref if name in base.ops else name
        op.ref_prefix = base.ops[name].ref_prefix if name in base.ops else None
    return src


def input_term(qs=None, domain=None):
    qs = lmfao.queries() if qs is None else qs
    domain = join_term() if domain is None else domain
    return balanced("Pair", [["Output", symbol(f"q{i}"), aggregate(q, domain, i)] for i, q in enumerate(qs)])


class BatchWorkload(Workload):
    @property
    def lang(self):
        return source().lang


def workload(*, rounds=10, mode="grouping", inp=None, goal=None):
    if rounds < 0 or mode not in ("independent", "pack", "fuse", "grouping"):
        raise ValueError("invalid batching mode or rewrite budget")
    src = source()
    enabled = {
        "independent": set(),
        "pack": {"batch-seed", "batch-merge"},
        "fuse": {"batch-seed", "batch-merge", "batch-fuse"},
        "grouping": {"batch-seed", "batch-merge", "batch-fuse", "batch-grouping-sets"},
    }[mode]
    rules = [f for f, _ in src.body if f[0] == "rewrite" and f[f.index(":name") + 1].strip('"') in enabled]
    inp = input_term() if inp is None else inp
    forms = [["sort", "U"], *src._ctors, *rules, ["let", "input", inp], ["run", str(rounds)]]
    graph_program = "\n".join(syntax.render(f) for f in forms) + "\n"
    spec = [f"rounds {rounds}", *ctor_lines(src.lang), "term " + src.lang.sexpr(src.term(inp, ground=True))]
    spec += [line for rule in rules for line in syntax.rule_lines(src, src.lang, rule)]
    program = graph_program
    if goal is not None:
        program += f"(let target {syntax.render(goal)})\n(run 0)\n(check (= input target))\n"
        spec.append("goal " + src.lang.sexpr(src.term(goal, ground=True)))
    return BatchWorkload(
        study="lmfao-batch",
        case="favorita-covariance-" + mode,
        rounds=rounds,
        rules=len(rules),
        program=program,
        graph_program=graph_program,
        multi="\n".join(spec) + "\n",
        nested=None,
        unsupported_reason="multi-root batch rules require the multipattern matcher",
    )


def frozen_inputs():
    result, manifest = {}, []
    for mode in ("independent", "fuse", "grouping"):
        w = workload(rounds=0 if mode == "independent" else 12, mode=mode)
        result[f"{mode}.egg"] = w.program
        result[f"{mode}.ref"] = (
            json.dumps({"multi": w.multi, "nested": None, "unsupported_reason": w.unsupported_reason}, indent=2) + "\n"
        )
        manifest.append({"name": mode, "file": f"{mode}.egg", "rewrite_round_budget": w.rounds})
    names = []
    for op in source().lang.ops.values():
        fields = [json.dumps(op.ref or ("=payload" if op.pays else op.ctor))]
        if op.ref_prefix:
            fields.append(json.dumps(op.ref_prefix))
        names.append(f"({op.ctor} {' '.join(fields)})")
    result["manifest.json"] = json.dumps({"variants": manifest, "export_names": " ".join(names)}, indent=2) + "\n"
    return result


def main():
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--graphs", action="store_true", help="refresh small SQL test exports using built release binaries"
    )
    args = parser.parse_args()
    destination = ROOT / "benchmarks/lmfao/inputs"
    for name, text in frozen_inputs().items():
        path = destination / name
        if args.check:
            if path.read_text() != text:
                raise SystemExit(f"Frozen input differs: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    for name, w in regression_inputs().items():
        native = (
            json.dumps(
                {
                    "multi": w.multi,
                    "nested": None,
                    "unsupported_reason": w.unsupported_reason,
                    "expected_goal": name != "different-sources",
                },
                indent=2,
            )
            + "\n"
        )
        for suffix, text in [("egg", w.program), ("ref", native)]:
            path = ROOT / "benchmarks/lmfao/correctness" / f"{name}.{suffix}"
            if args.check:
                if path.read_text() != text:
                    raise SystemExit(f"Frozen correctness input differs: {path}")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
    if args.graphs:
        if args.check:
            parser.error("--graphs cannot be combined with --check")
        import tempfile

        from benchmarking.lmfao.optimizer import export_graph, write_json
        from benchmarking.models import FileSpec
        from benchmarking.targets import sha256_file

        manifest = json.loads(frozen_inputs()["manifest.json"])
        destination = ROOT / "benchmarking/tests/fixtures/lmfao"
        destination.mkdir(parents=True, exist_ok=True)
        hashes = {}
        with tempfile.TemporaryDirectory() as temporary:
            from pathlib import Path

            for name in ["independent", "pack", "fuse", "grouping", "nonlinear"]:
                path = ROOT / "benchmarks/lmfao/correctness" / f"{name}.egg"
                file = FileSpec(str(path), path, sha256_file(path))
                output = Path(temporary) / f"{name}.json"
                graph = export_graph(
                    ROOT / "target/release/egglog-experimental", file, "slotted", output, manifest["export_names"], 30
                )
                write_json(destination / f"{name}.json", graph)
                hashes[name] = {
                    "input_sha256": sha256_file(path),
                    "graph_sha256": sha256_file(destination / f"{name}.json"),
                }
        write_json(destination / "manifest.json", hashes)


def regression_queries():
    return [
        lmfao.Query(),
        lmfao.Query((), ("x",)),
        lmfao.Query((), ("x", "x")),
        lmfao.Query(("k",)),
        lmfao.Query(("k",), ("x",)),
        lmfao.Query(("z",)),
        lmfao.Query(("k", "z")),
        lmfao.Query(("z", "k")),
        lmfao.Query(("k", "k")),
        lmfao.Query(("k", "z", "x")),
    ]


def task_tree(term):
    if term[0] == "Pair":
        return ["TaskPair", *(task_tree(child) for child in term[1:])]
    _, name, (_, _, row, count, body) = term
    return ["Task", name, ["Lambda", row, ["Lambda", count, body]]]


def regression_inputs():
    inp = input_term(regression_queries(), symbol("R"))
    result = {}
    for mode, op in [("independent", None), ("pack", "Batch"), ("fuse", "FusedBatch"), ("grouping", "GroupingBatch")]:
        goal = inp if op is None else [op, symbol("R"), task_tree(inp)]
        w = workload(rounds=8, mode=mode, inp=inp, goal=goal)
        result[mode] = w
    nonlinear = ["Output", symbol("q0"), ["Sum", symbol("R"), "$r", "$c", ["Mult", "$c", "$c"]]]
    result["nonlinear"] = workload(rounds=0, mode="independent", inp=nonlinear, goal=nonlinear)
    # Seed the wrong candidate on both sides, but never equate it with the input.
    # It must remain distinct when the two outputs have different sources.
    left = input_term([lmfao.Query()], symbol("R"))
    right = ["Output", symbol("q1"), aggregate(lmfao.Query(), symbol("S"), 1)]
    inp = ["Pair", left, right]
    wrong = ["Batch", symbol("R"), task_tree(inp)]
    w = workload(rounds=8, inp=inp)
    forms = syntax.parse(w.program)
    forms.insert(-1, ["let", "wrong", wrong])
    forms.append(["fail", ["check", ["=", "input", "wrong"]]])
    from dataclasses import replace

    result["different-sources"] = replace(
        w,
        program="\n".join(syntax.render(f) for f in forms) + "\n",
        multi=w.multi
        + "term "
        + source().lang.sexpr(source().term(wrong, ground=True))
        + "\n"
        + "goal "
        + source().lang.sexpr(source().term(wrong, ground=True))
        + "\n",
    )
    return result


if __name__ == "__main__":
    main()
