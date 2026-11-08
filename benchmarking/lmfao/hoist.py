"""Compare scope-aware hoisting and fusion on original Favorita query kernels."""

from __future__ import annotations

import argparse
import json
import os
import struct
import subprocess
import sys
import time
from array import array
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from rich.console import Console

from benchmarking.engines import Treatment
from benchmarking.targets import sha256_file
from benchmarks.reproduction.slotted import reference

from ..scoped import optimize_programs
from . import backend, fusion, model
from .data import load_data
from .optimizer import ROOT, seconds_summary, write_json

FIXTURES = model.FIXTURES / "hoisting"
MODES: dict[str, Treatment] = {"slotted": "slotted", "ordinary": "off"}


def query() -> Any:
    """Oil rows bind the coefficient; the inner bag preserves the other five joins."""
    return [
        "Sum",
        ["Blocks"],
        "$oil",
        [
            "Sum",
            ["Rows", "$oil"],
            "$sale",
            ["Mul", ["Field", "$oil", '"oilprize"'], ["Field", "$sale", '"unit_sales"']],
        ],
    ]


def ordinary(term: Any, *, pattern: bool = False) -> Any:
    if isinstance(term, str):
        if term.startswith("$"):
            return ["Var", term[1:] if pattern else json.dumps(term)]
        return term
    if term[0] == "not-free":
        return ["set-not-contains", ["fv", ordinary(term[2], pattern=pattern)], term[1][1:]]
    return [ordinary(t, pattern=pattern) for t in term]


def program(mode: str, term: Any | None = None, *, rounds: int = 16) -> str:
    forms = reference.parse((FIXTURES / "rules.egg").read_text())
    if mode == "ordinary":
        constructors, rewrites = [], []
        for form in forms:
            if form[0] == "rewrite":
                rewrites.append(ordinary(form, pattern=True))
            else:
                if ":binder" in form:
                    form = form[: form.index(":binder")]
                constructors.append(form)
        forms = constructors + reference.parse((FIXTURES / "free-vars.egg").read_text()) + rewrites
    term = query() if term is None else term
    forms += [
        ["let", "input", ordinary(term) if mode == "ordinary" else term],
        ["run", str(rounds)],
        ["extract", "input"],
    ]
    return "\n".join(reference.render(f) for f in forms) + "\n"


def canonical(term: Any, scope: tuple[str, ...] = ()) -> Any:
    """Normalize extracted binder spellings for comparison and code generation."""
    if isinstance(term, str):
        return f"$v{len(scope) - 1 - scope[::-1].index(term)}" if term in scope else term
    if term[0] == "Var":
        return canonical(json.loads(term[1]), scope)
    if term[0] in fusion.BINDERS:
        index = fusion.BINDERS[term[0]]
        binder = term[index] if isinstance(term[index], str) else json.loads(term[index][1])
        children = [canonical(t, scope) for t in term[1:index]]
        # Give lexical roles distinct names, including shadowed source binders.
        renamed = f"$v{len(scope)}"
        body = canonical(term[index + 1], (*scope, binder))
        return [term[0], *children, renamed, body]
    return [canonical(t, scope) for t in term]


def kernel(term: Any) -> str:
    return fusion.kernel(term)


def prepare_data(directory: Path, destination: Path, *, case: str = "hoist") -> dict[str, Any]:
    if sys.byteorder != "little":
        raise ValueError("kernel probe requires a little-endian host")
    start = time.perf_counter()
    db, metadata = load_data(directory)
    try:
        # Materialize bags, not aggregate answers: duplicate rows remain duplicate.
        tables = [t for t in model.WORKLOAD.relations if t != "Oil"]
        fields = ["unit_sales", "transactions"] if case == "fusion" else ["unit_sales"]
        indices = fusion.query_indices() if case == "fusion" else [20]
        db.execute(
            "CREATE TEMP TABLE sales_bag AS SELECT date, "
            + ", ".join(fields)
            + " FROM "
            + " NATURAL JOIN ".join(map(model.ident, tables))
        )
        expected = []
        for i in indices:
            weight = (
                " * ".join(f"CAST({model.ident(f)} AS DECIMAL(38,6))" for f in model.WORKLOAD.queries[i].factors) or "1"
            )
            answer = db.execute(f"SELECT COALESCE(SUM({weight}), 0) FROM sales_bag NATURAL JOIN Oil").fetchone()
            assert answer is not None
            expected.append(str(answer[0]))
        rows = array("d")
        ranges: dict[int, list[int]] = {}
        db.execute(
            "SELECT date, " + ", ".join(f"CAST({f} AS DOUBLE)" for f in fields) + " FROM sales_bag ORDER BY date"
        )
        while batch := db.fetchmany(65536):
            for date, *values in batch:
                index = len(rows) // len(fields)
                ranges.setdefault(date, [index, index])[1] = index + 1
                rows.extend(values)
        blocks = [
            (ranges.get(date, [0, 0]), value)
            for date, value in db.execute(
                "SELECT date, CAST(oilprize AS DOUBLE) FROM Oil ORDER BY date, oilprize"
            ).fetchall()
        ]
        with destination.open("wb") as output:
            output.write(struct.pack("<Q", len(rows) // len(fields)))
            rows.tofile(output)
            output.write(struct.pack("<Q", len(blocks)))
            for (low, high), value in blocks:
                output.write(struct.pack("<QQd", low, high, value))
        return {
            **metadata,
            "query_indices": indices,
            "expected": expected,
            "sales_width": len(fields),
            "prepared_sales_rows": len(rows) // len(fields),
            "oil_rows": len(blocks),
            "visited_sales_rows": sum(high - low for (low, high), _ in blocks),
            "preparation_seconds": time.perf_counter() - start,
            "prepared_sha256": sha256_file(destination),
        }
    finally:
        db.close()


def run(args: argparse.Namespace) -> dict[str, Any]:
    modes: dict[str, Treatment] = (
        {"slotted": "slotted", "debruijn": "off", "slotted-no-fusion": "slotted", "debruijn-no-fusion": "off"}
        if args.case == "fusion"
        else MODES
    )
    programs = {
        mode: (
            treatment,
            fusion.program(mode.split("-", 1)[0], fuse=not mode.endswith("-no-fusion"))
            if args.case == "fusion"
            else program(mode),
        )
        for mode, treatment in modes.items()
    }
    optimizer, raw = optimize_programs(args, programs)
    selected = {"input": canonical(fusion.query() if args.case == "fusion" else query())}
    for mode, term in raw.items():
        selected[mode] = canonical(fusion.from_debruijn(term) if mode.startswith("debruijn") else term)
    out = args.output_dir.resolve()
    console = Console(stderr=True)
    console.print("Preparing query bags and decimal answers outside kernel timing")
    data = prepare_data(args.data, out / "bags.bin", case=args.case)
    (out / "expected.txt").write_text("\n".join(data["expected"]) + "\n")
    sources: dict[str, str] = {}
    aliases: dict[str, str] = {}
    builds: dict[str, Any] = {}
    for label, term in selected.items():
        source = (
            (FIXTURES / "kernel.cpp")
            .read_text()
            .replace("// KERNEL", kernel(term))
            .replace("SALES_WIDTH", str(data["sales_width"]))
            .replace("OUTPUTS", str(len(data["expected"])))
        )
        if source in sources:
            aliases[label] = sources[source]
            continue
        sources[source] = label
        (out / f"{label}.cpp").write_text(source)
        seconds = backend.command(
            ["g++", "-std=c++11", "-O3", "-mtune=native", f"{label}.cpp", "-o", label],
            out,
            f"{label}-build.log",
            timeout=args.timeout_sec,
        )
        builds[label] = {"compilation_seconds": seconds, "binary_sha256": sha256_file(out / label)}
    execution: dict[str, list[dict[str, Any]]] = {label: [] for label in sources.values()}
    labels = list(execution)
    for repeat in range(args.rounds):
        order = labels[repeat % len(labels) :] + labels[: repeat % len(labels)]
        if repeat % 2:
            order.reverse()
        for label in order:
            result = subprocess.run(
                [str(out / label), str(out / "bags.bin"), str(out / "expected.txt"), str(args.inner_repeats)],
                capture_output=True,
                text=True,
                check=True,
                timeout=args.timeout_sec,
            )
            execution[label].append(json.loads(result.stdout))
    report = {
        "case": args.case,
        "data": data,
        "optimizer": optimizer,
        "selected": selected,
        "execution_aliases": aliases,
        "builds": builds,
        "execution_samples": execution,
        "inner_repeats": args.inner_repeats,
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "execution": {
            label: seconds_summary(row["seconds_per_execution"] for row in samples)
            for label, samples in execution.items()
        },
        "scope": "Original scalar covariance query kernels over prepared bags, not full LMFAO execution. "
        "Bag construction, data loading, "
        "independent checking and compilation are excluded from kernel timings. Identical C++ "
        "shares execution samples. Original LMFAO already implements hoisting and multi-output fusion.",
    }
    write_json(out / "result.json", report)
    return report


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=["hoist", "fusion"], default="hoist")
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--target", default=str(ROOT))
    parser.add_argument("--report", type=Path, help="Optimizer JSONL cache; default OUTPUT/optimizer.jsonl")
    parser.add_argument("--rounds", type=int, default=10)
    parser.add_argument("--inner-repeats", type=int, default=100)
    parser.add_argument("--timeout-sec", type=int, default=60)
    parser.add_argument("--cpu", type=int)
    args = parser.parse_args(argv)
    if args.report == Path("-"):
        parser.error("--report requires a filesystem path, not '-'")
    if min(args.rounds, args.inner_repeats, args.timeout_sec) < 1:
        parser.error("rounds, inner repeats and timeout must be positive")
    print(json.dumps(run(args), indent=2))
    return 0
