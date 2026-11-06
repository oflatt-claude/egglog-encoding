"""Compare scope-aware hoisting on a kernel from the original Favorita query q20."""

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

from benchmarking.collection import BenchmarkRequest, collect, plan_collection, resolve_requests
from benchmarking.engines import Treatment
from benchmarking.models import BenchmarkEndpoint, EndpointRequest
from benchmarking.native_memory import native_memory_command
from benchmarking.reports.store import ReportStore, select_observations
from benchmarking.targets import parse_target, sha256_file
from benchmarking.workloads import resolve_files
from benchmarks.reproduction.slotted import reference

from . import backend, model
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
    if term[0] in ("Sum", "ScaleSum"):
        index = 2 if term[0] == "Sum" else 3
        binder = term[index] if isinstance(term[index], str) else json.loads(term[index][1])
        children = [canonical(t, scope) for t in term[1:index]]
        # Give lexical roles distinct names, including shadowed source binders.
        renamed = f"$v{len(scope)}"
        body = canonical(term[index + 1], (*scope, binder))
        return [term[0], *children, renamed, body]
    return [canonical(t, scope) for t in term]


def kernel(term: Any) -> str:
    """Lower the selected sum expression; code generation performs no hoisting."""
    lines = ["__attribute__((noinline)) double kernel(const Data& data) {"]
    serial = 0

    def emit(t: Any, scope: dict[str, tuple[str, str]]) -> str:
        nonlocal serial
        op = t[0]
        if op == "Field":
            var, kind = scope[t[1]]
            name = json.loads(t[2])
            if (kind, name) == ("block", "oilprize"):
                return f"data.blocks[{var}].oil"
            if (kind, name) == ("sale", "unit_sales"):
                return f"data.sales[{var}]"
            raise ValueError("field does not belong to this binding")
        if op == "Mul":
            return f"({emit(t[1], scope)} * {emit(t[2], scope)})"
        if op not in ("Sum", "ScaleSum"):
            raise ValueError(f"unsupported selected operator: {op}")
        serial += 1
        result, index = f"sum{serial}", f"i{serial}"
        domain, binder, body = t[1], t[-2], t[-1]
        factor = emit(t[2], scope) if op == "ScaleSum" else None
        if domain[0] == "Blocks":
            low, high, kind = "0", "data.blocks.size()", "block"
        elif domain[0] == "Rows":
            parent, parent_kind = scope[domain[1]]
            if parent_kind != "block":
                raise ValueError("Rows requires an oil binding")
            low, high, kind = f"data.blocks[{parent}].begin", f"data.blocks[{parent}].end", "sale"
        else:
            raise ValueError("unsupported sum domain")
        lines.append(f"double {result} = 0;")
        lines.append(f"for (size_t {index} = {low}; {index} < {high}; ++{index}) {{")
        value = emit(body, {**scope, binder: (index, kind)})
        lines.extend([f"{result} += {value};", "}"])
        return f"({factor} * {result})" if factor is not None else result

    answer = emit(term, {})
    return "\n".join([*lines, f"return {answer};", "}"])


def prepare_data(directory: Path, destination: Path) -> dict[str, Any]:
    if sys.byteorder != "little":
        raise ValueError("kernel probe requires a little-endian host")
    start = time.perf_counter()
    db, metadata = load_data(directory)
    try:
        # Materialize bags, not aggregate answers: duplicate rows remain duplicate.
        tables = [t for t in model.WORKLOAD.relations if t != "Oil"]
        db.execute(
            "CREATE TEMP TABLE sales_bag AS SELECT date, unit_sales FROM "
            + " NATURAL JOIN ".join(map(model.ident, tables))
        )
        expected = db.execute(
            "SELECT COALESCE(SUM(CAST(unit_sales AS DECIMAL(38,6)) * "
            "CAST(oilprize AS DECIMAL(38,6))), 0) FROM sales_bag NATURAL JOIN Oil"
        ).fetchone()
        assert expected is not None
        rows = array("d")
        ranges: dict[int, list[int]] = {}
        db.execute("SELECT date, CAST(unit_sales AS DOUBLE) FROM sales_bag ORDER BY date")
        while batch := db.fetchmany(65536):
            for date, value in batch:
                ranges.setdefault(date, [len(rows), len(rows)])[1] = len(rows) + 1
                rows.append(value)
        blocks = [
            (ranges.get(date, [0, 0]), value)
            for date, value in db.execute(
                "SELECT date, CAST(oilprize AS DOUBLE) FROM Oil ORDER BY date, oilprize"
            ).fetchall()
        ]
        with destination.open("wb") as output:
            output.write(struct.pack("<Q", len(rows)))
            rows.tofile(output)
            output.write(struct.pack("<Q", len(blocks)))
            for (low, high), value in blocks:
                output.write(struct.pack("<QQd", low, high, value))
        q = model.Query((), ("unit_sales", "oilprize"))
        return {
            **metadata,
            "query_index": model.WORKLOAD.queries.index(q),
            "expected": str(expected[0]),
            "prepared_sales_rows": len(rows),
            "oil_rows": len(blocks),
            "visited_sales_rows": sum(high - low for (low, high), _ in blocks),
            "preparation_seconds": time.perf_counter() - start,
            "prepared_sha256": sha256_file(destination),
        }
    finally:
        db.close()


def run(args: argparse.Namespace) -> dict[str, Any]:
    if args.cpu is not None:
        os.sched_setaffinity(0, {args.cpu})
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    console = Console(stderr=True)
    request = parse_target(args.target)
    requests = []
    files = {}
    for mode, treatment in MODES.items():
        path = out / f"{mode}.egg"
        path.write_text(program(mode))
        files[mode] = resolve_files([str(path)], ROOT)[0]
        requests.append(BenchmarkRequest(EndpointRequest(request, treatment), (files[mode],)))
    store = ReportStore(args.report or out / "optimizer.jsonl")
    targets = resolve_requests(tuple(requests), store, args.rounds, args.timeout_sec, False, ROOT, ROOT, console)
    plans = plan_collection(store, tuple(requests), targets, args.rounds, args.timeout_sec, False)
    collect(store, plans, tuple(requests), targets, args.timeout_sec, console)
    target = targets[request]
    optimizer, selected = {}, {"unhoisted": canonical(query())}
    for mode, treatment in MODES.items():
        endpoint = BenchmarkEndpoint(target.row, target.binary_sha256_for(treatment), treatment)
        observations = select_observations(store, endpoint, files[mode], args.rounds, args.timeout_sec)
        if observations.issue or any(row.record["status"] != "success" for row in observations.rows):
            raise RuntimeError(f"optimizer collection failed for {mode}")
        binary = target.binary_path_for(treatment)
        assert binary is not None
        command, env = native_memory_command(
            [str(binary), *(["--slotted"] if mode == "slotted" else []), str(files[mode].absolute_path)], os.environ
        )
        result = subprocess.run(command, env=env, capture_output=True, text=True, check=True, timeout=args.timeout_sec)
        selected[mode] = canonical(reference.parse(result.stdout)[0])
        optimizer[mode] = {
            "process_seconds": seconds_summary(
                row.record["wall_sec"] for row in observations.rows if row.record["wall_sec"] is not None
            ),
            "binary_sha256": sha256_file(binary),
            "input_sha256": files[mode].sha256,
        }
    console.print("Preparing q20 bags and decimal answer outside kernel timing")
    data = prepare_data(args.data, out / "bags.bin")
    sources: dict[str, str] = {}
    aliases: dict[str, str] = {}
    builds: dict[str, Any] = {}
    for label, term in selected.items():
        source = (FIXTURES / "kernel.cpp").read_text().replace("// KERNEL", kernel(term))
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
    execution: dict[str, list[dict[str, float]]] = {label: [] for label in sources.values()}
    labels = list(execution)
    for repeat in range(args.rounds):
        order = labels[repeat % len(labels) :] + labels[: repeat % len(labels)]
        if repeat % 2:
            order.reverse()
        for label in order:
            result = subprocess.run(
                [str(out / label), str(out / "bags.bin"), data["expected"], str(args.inner_repeats)],
                capture_output=True,
                text=True,
                check=True,
                timeout=args.timeout_sec,
            )
            execution[label].append(json.loads(result.stdout))
    report = {
        "data": data,
        "optimizer": optimizer,
        "selected": selected,
        "execution_aliases": aliases,
        "builds": builds,
        "execution_samples": execution,
        "inner_repeats": args.inner_repeats,
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "execution": {
            label: seconds_summary(row["seconds_per_query"] for row in samples) for label, samples in execution.items()
        },
        "scope": "q20 kernel over prepared bags, not full LMFAO execution. Bag construction, data loading, "
        "independent checking and compilation are excluded from kernel timings. Identical C++ "
        "shares execution samples. Original LMFAO already implements partial-product hoisting.",
    }
    write_json(out / "result.json", report)
    return report


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
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
