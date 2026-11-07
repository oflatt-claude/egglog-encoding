"""Scope and bag-semantics checks for the hoisting follow-up experiment."""

from __future__ import annotations

import json
import struct
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any

import pytest

from benchmarking.lmfao import fusion, hoist, model
from benchmarking.lmfao.optimizer import extractor_path
from benchmarks.reproduction.slotted import reference


def evaluate(t: Any, blocks: list[dict[str, Any]], scope: dict[str, Any] | None = None) -> Any:
    scope = {} if scope is None else scope
    if isinstance(t, str):
        return scope[t]
    if t[0] == "One":
        return (Fraction(1),)
    if t[0] == "Field":
        return (Fraction(scope[t[1]][json.loads(t[2])]),)
    if t[0] == "Mul":
        return (evaluate(t[1], blocks, scope)[0] * evaluate(t[2], blocks, scope)[0],)
    if t[0] == "Pair":
        return evaluate(t[1], blocks, scope) + evaluate(t[2], blocks, scope)
    if t[0] == "Lambda":
        return lambda value: evaluate(t[2], blocks, {**scope, t[1]: value})
    if t[0] == "App":
        return evaluate(t[1], blocks, scope)(evaluate(t[2], blocks, scope))
    domain = blocks if t[1][0] == "Blocks" else scope[t[1][1]]["rows"]
    answer = (Fraction(),) * fusion.width(t)
    for row in domain:
        values = evaluate(t[-1], blocks, {**scope, t[-2]: row})
        answer = tuple(a + b for a, b in zip(answer, values, strict=True))
    factor = evaluate(t[2], blocks, scope)[0] if t[0] == "ScaleSum" else Fraction(1)
    return tuple(a * factor for a in answer)


@pytest.fixture(scope="module")
def binary() -> Path:
    subprocess.run(
        [
            "cargo",
            "build",
            "--locked",
            "-p",
            "egglog-experimental",
            "--no-default-features",
            "--features",
            "bin",
            "--bin",
            "egglog-experimental",
        ],
        cwd=hoist.ROOT,
        check=True,
    )
    return extractor_path("debug").with_name("egglog-experimental")


@pytest.mark.parametrize("mode", ["slotted", "ordinary"])
def test_hoisting_preserves_bags_and_rejects_bound_factor(mode: str, binary: Path, tmp_path: Path) -> None:
    term = hoist.query()
    right = hoist.query()
    product = right[-1][-1]
    product[1], product[2] = product[2], product[1]
    dependent = [
        "Sum",
        ["Blocks"],
        "$oil",
        [
            "Sum",
            ["Rows", "$oil"],
            "$sale",
            ["Mul", ["Field", "$sale", '"unit_sales"'], ["Field", "$sale", '"unit_sales"']],
        ],
    ]
    for case, expression in [("hoist-left", term), ("hoist-right", right), ("dependent", dependent)]:
        path = tmp_path / f"{case}.egg"
        path.write_text(hoist.program(mode, expression))
        args = [str(binary), *(["--slotted"] if mode == "slotted" else []), str(path)]
        result = subprocess.run(args, capture_output=True, text=True, check=True, timeout=30)
        selected = hoist.canonical(reference.parse(result.stdout)[0])
        assert (selected[-1][0] == "ScaleSum") == case.startswith("hoist")
        for rows in [[], [{"unit_sales": 0}], [{"unit_sales": Fraction(-3, 2)}, {"unit_sales": 4}] * 2]:
            blocks = [{"oilprize": 3, "rows": rows}, {"oilprize": -2, "rows": rows}, {"oilprize": 9, "rows": []}]
            assert evaluate(selected, blocks) == evaluate(expression, blocks)
        if case.startswith("hoist"):
            code = hoist.kernel(selected)
            assert "*" not in code.split("for (size_t i2", 1)[1].split("}", 1)[0]


def test_canonicalization_preserves_shadowing_and_domains() -> None:
    term = ["Sum", ["Blocks"], "$x", ["Sum", ["Rows", "$x"], "$x", ["Field", "$x", '"unit_sales"']]]
    normalized = hoist.canonical(term)
    assert normalized[-1][1] == ["Rows", "$v0"]
    assert normalized[-1][-1] == ["Field", "$v1", '"unit_sales"']
    assert hoist.canonical(hoist.ordinary(term)) == normalized


def test_kernel_query_is_in_the_pinned_workload() -> None:
    assert model.WORKLOAD.queries[20] == model.Query((), ("unit_sales", "oilprize"))


def optimize(binary: Path, tmp_path: Path, mode: str, term: Any, *, fuse: bool = True) -> Any:
    path = tmp_path / f"{mode}.egg"
    path.write_text(fusion.program(mode, term, fuse=fuse))
    result = subprocess.run(
        [str(binary), *(["--slotted"] if mode == "slotted" else []), str(path)],
        capture_output=True,
        text=True,
        check=True,
        timeout=60,
    )
    selected = reference.parse(result.stdout)[0]
    return hoist.canonical(fusion.from_debruijn(selected) if mode == "debruijn" else selected)


@pytest.mark.parametrize("mode", ["slotted", "debruijn"])
@pytest.mark.parametrize("fuse", [False, True])
def test_covariance_fusion_executes_original_outputs(mode: str, fuse: bool, binary: Path, tmp_path: Path) -> None:
    term = fusion.query()
    selected = optimize(binary, tmp_path, mode, term, fuse=fuse)
    assert fusion.query_indices() == [0, 17, 18, 20, 25, 47, 48, 53, 103, 104]
    assert selected[0] == ("Sum" if fuse else "Pair")
    rows: list[dict[str, Any]] = [
        {"unit_sales": Fraction(-3, 2), "transactions": 7},
        {"unit_sales": 4, "transactions": 2},
    ] * 2
    blocks: list[dict[str, Any]] = [
        {"oilprize": 3, "rows": rows},
        {"oilprize": -2, "rows": rows},
        {"oilprize": 3, "rows": rows},
        {"oilprize": 9, "rows": []},
    ]
    expected = []
    for i in fusion.query_indices():
        factors = model.WORKLOAD.queries[i].factors
        values = []
        for block in blocks:
            for row in block["rows"]:
                value = Fraction(1)
                for f in factors:
                    value *= {**block, **row}[f]
                values.append(value)
        expected.append(sum(values, Fraction()))
    assert evaluate(selected, blocks) == evaluate(term, blocks) == tuple(expected)
    assert evaluate(selected, []) == (Fraction(),) * 10
    code = hoist.kernel(selected)
    # Fusion must reduce the scans; code generation merely emits the selected loops.
    assert code.count("for (size_t") == (2 if fuse else 20)
    source = (
        (hoist.FIXTURES / "kernel.cpp")
        .read_text()
        .replace("// KERNEL", code)
        .replace("SALES_WIDTH", "2")
        .replace("OUTPUTS", "10")
    )
    (tmp_path / "kernel.cpp").write_text(source)
    subprocess.run(["g++", "-std=c++11", "-O3", "kernel.cpp", "-o", "kernel"], cwd=tmp_path, check=True)
    with (tmp_path / "bags.bin").open("wb") as output:
        output.write(struct.pack("<Q", len(rows)))
        for row in rows:
            output.write(struct.pack("<dd", float(row["unit_sales"]), row["transactions"]))
        output.write(struct.pack("<Q", len(blocks)))
        for block in blocks:
            output.write(struct.pack("<QQd", 0, len(block["rows"]), block["oilprize"]))
    (tmp_path / "expected.txt").write_text("\n".join(str(float(v)) for v in expected))
    subprocess.run(["./kernel", "bags.bin", "expected.txt", "2"], cwd=tmp_path, check=True)


@pytest.mark.parametrize("mode", ["slotted", "debruijn"])
def test_beta_avoids_capture_and_fusion_respects_domains(mode: str, binary: Path, tmp_path: Path) -> None:
    # Substituting the outer $oil for $x must rename the inner binder also spelled $oil.
    capture = [
        "Sum",
        ["Blocks"],
        "$oil",
        [
            "App",
            [
                "Lambda",
                "$x",
                [
                    "Sum",
                    ["Rows", "$oil"],
                    "$oil",
                    ["Mul", ["Field", "$x", '"oilprize"'], ["Field", "$oil", '"unit_sales"']],
                ],
            ],
            "$oil",
        ],
    ]
    different = [
        "Sum",
        ["Blocks"],
        "$oil",
        [
            "Pair",
            ["Sum", ["Rows", "$oil"], "$sale", ["Field", "$sale", '"unit_sales"']],
            ["Sum", ["Blocks"], "$other", ["Field", "$other", '"oilprize"']],
        ],
    ]
    blocks = [{"oilprize": 3, "rows": [{"unit_sales": 4}, {"unit_sales": -2}]}, {"oilprize": 7, "rows": []}]
    for term in [capture, different]:
        assert hoist.canonical(fusion.from_debruijn(fusion.to_debruijn(term))) == hoist.canonical(term)
        selected = optimize(binary, tmp_path, mode, term)
        assert evaluate(selected, blocks) == evaluate(term, blocks)
        assert "App" not in reference.render(selected)
        if term is different:
            assert selected[-1][0] == "Pair"
