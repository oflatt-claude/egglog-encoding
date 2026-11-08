"""Isolate vertical fusion on the slotted paper's unmodified SDQL inputs."""

from __future__ import annotations

import argparse
import json
import os
from collections import Counter
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from benchmarks.reproduction.slotted import reference, sdql

from . import sdql_values
from .engines import Treatment
from .scoped import optimize_programs
from .targets import sha256_file

ROOT = sdql.ROOT
FIXTURES = ROOT / "benchmarks/slotted/vertical"
RULE_NAMES = {"beta", "sum-sum-vert-fuse-1", "sum-sum-vert-fuse-2"}
DECLARATIONS = reference.parse(sdql.RULES.with_name("sdql.egg").read_text())
CONSTRUCTORS = {f[1]: f for f in DECLARATIONS if f[0] == "constructor"}
BINDERS = {
    op: tuple(int(x) + 1 for x in f[f.index(":binder") + 1 :]) for op, f in CONSTRUCTORS.items() if ":binder" in f
}


def to_debruijn(t: Any, scope: tuple[str, ...] = ()) -> Any:
    if isinstance(t, str):
        return ["Var", str(scope[::-1].index(t))] if t.startswith("$") else t
    binders = BINDERS.get(t[0], ())
    extended = (*scope, *(t[i] for i in binders))
    return [
        t[0],
        *[
            to_debruijn(c, extended if binders and i > max(binders) else scope)
            for i, c in enumerate(t[1:], 1)
            if i not in binders
        ],
    ]


def from_debruijn(t: Any, scope: tuple[str, ...] = ()) -> Any:
    if isinstance(t, str):
        return t
    if t[0] in ("Shift", "Subst"):
        raise ValueError("unresolved scope operation in extracted program")
    if t[0] == "Var":
        index = int(t[1])
        if not 0 <= index < len(scope):
            raise ValueError("extracted variable escapes its scope")
        return scope[-1 - index]
    binders = BINDERS.get(t[0], ())
    if not binders:
        return [t[0], *[from_debruijn(c, scope) for c in t[1:]]]
    names = tuple(f"$v{len(scope) + i}" for i in range(len(binders)))
    return [
        t[0],
        *[from_debruijn(c, scope) for c in t[1 : min(binders)]],
        *names,
        from_debruijn(t[-1], (*scope, *names)),
    ]


def program(mode: str, term: Any, *, rounds: int = 64, fuse: bool = True) -> str:
    if mode == "slotted":
        forms = [*DECLARATIONS, *reference.parse((FIXTURES / "rules.egg").read_text())]
    else:
        forms = reference.parse((FIXTURES / "debruijn.egg").read_text())
        term = to_debruijn(term)
    if not fuse:
        forms = [
            f for f in forms if not (f[0] == "rewrite" and ":name" in f and "vert-fuse" in f[f.index(":name") + 1])
        ]
    forms += [["let", "input", term], ["run", str(rounds)], ["extract", "input"]]
    return "\n".join(reference.render(f) for f in forms) + "\n"


def counts(t: Any) -> dict[str, int]:
    result: Counter[str] = Counter()

    def visit(node: Any) -> None:
        if isinstance(node, str):
            if node.startswith("$"):
                result["var"] += 1
            return
        result[node[0]] += 1
        for i, child in enumerate(node[1:], 1):
            if i not in BINDERS.get(node[0], ()):
                visit(child)

    visit(t)
    return dict(result)


def validate(kernel: str, selected: dict[str, Any]) -> dict[str, Any]:
    first, published = sdql.workload(kernel, "1st")[0], sdql.workload(kernel, "2nd")[1]
    source = sdql.workload(kernel, "2nd")[0]
    programs = {"input": source, "published-baseline": published, **selected}
    checked = 0
    for n in range(5):
        for seed in range(3):
            high, low, expected = sdql_values.case(kernel, n, seed)
            if sdql_values.execute(first, high)[0] != expected:
                raise AssertionError((kernel, n, seed, "first-phase oracle"))
            for mode, term in programs.items():
                if sdql_values.execute(term, low)[0] != expected:
                    raise AssertionError((kernel, n, seed, mode))
            checked += 1
    return {
        "exact_cases": checked,
        "diagnostic_n": 4,
        "diagnostic_seed": 0,
        "programs": {
            mode: {
                "ast_size": sum(counts(t).values()),
                "operators": counts(t),
                "evaluation_counts": sdql_values.execute(t, sdql_values.case(kernel, 4, 0)[1])[1],
            }
            for mode, t in programs.items()
        },
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    if len(set(args.kernels)) != len(args.kernels):
        raise ValueError("kernels must not be repeated")
    modes: dict[str, Treatment] = {
        "slotted": "slotted",
        "debruijn": "off",
        "slotted-no-fusion": "slotted",
        "debruijn-no-fusion": "off",
    }
    programs = {}
    for kernel in args.kernels:
        term = sdql.workload(kernel, "2nd")[0]
        for mode, treatment in modes.items():
            programs[f"{kernel}-{mode}"] = (
                treatment,
                program(mode.split("-", 1)[0], term, rounds=args.rewrite_rounds, fuse=not mode.endswith("-no-fusion")),
            )
    optimizer, raw = optimize_programs(args, programs)
    selected: dict[str, dict[str, Any]] = {}
    correctness = {}
    for kernel in args.kernels:
        selected[kernel] = {}
        for mode in modes:
            term = raw[f"{kernel}-{mode}"]
            normalized = from_debruijn(term if mode.startswith("debruijn") else to_debruijn(term))
            selected[kernel][mode] = normalized
            (args.output_dir / f"{kernel}-{mode}-selected.sexp").write_text(sdql.pretty(normalized) + "\n")
        correctness[kernel] = validate(kernel, selected[kernel])
    report = {
        "artifact_commit": sdql.ARTIFACT_COMMIT,
        "source_sha256": {kernel: sha256_file(sdql.FIXTURES / f"{kernel}_2nd.sexp") for kernel in args.kernels},
        "rules": sorted(RULE_NAMES),
        "optimizer": optimizer,
        "selected": selected,
        "correctness": correctness,
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "scope": "Unmodified second-phase SDQL artifact inputs with three rules, not the full 44-rule experiment. "
        "Both extractors minimize source AST size. Substitution strategies differ. Exact interpretation "
        "uses generated small sparse inputs; its operation counts are diagnostics, not execution timings. "
        "Published baseline extractions are checked separately and never seed optimization.",
    }
    (args.output_dir / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernels", nargs="+", choices=sdql.KERNELS, default=list(sdql.KERNELS))
    parser.add_argument("--target", default=str(ROOT))
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--rounds", type=int, default=10)
    parser.add_argument("--rewrite-rounds", type=int, default=64)
    parser.add_argument("--timeout-sec", type=int, default=60)
    parser.add_argument("--cpu", type=int)
    args = parser.parse_args(argv)
    if args.report == Path("-") or min(args.rounds, args.rewrite_rounds, args.timeout_sec) < 1:
        parser.error("provide a filesystem report path and positive sample, rewrite and timeout bounds")
    print(json.dumps(run(args), indent=2))
    return 0
