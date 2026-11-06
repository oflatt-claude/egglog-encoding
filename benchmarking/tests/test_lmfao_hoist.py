"""Scope and bag-semantics checks for the hoisting follow-up experiment."""

from __future__ import annotations

import json
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any

import pytest

from benchmarking.lmfao import hoist, model
from benchmarking.lmfao.optimizer import extractor_path
from benchmarks.reproduction.slotted import reference


def evaluate(t: Any, blocks: list[dict[str, Any]], scope: dict[str, Any] | None = None) -> Fraction:
    scope = {} if scope is None else scope
    if t[0] == "Field":
        return Fraction(scope[t[1]][json.loads(t[2])])
    if t[0] == "Mul":
        return evaluate(t[1], blocks, scope) * evaluate(t[2], blocks, scope)
    domain = blocks if t[1][0] == "Blocks" else scope[t[1][1]]["rows"]
    answer = sum((evaluate(t[-1], blocks, {**scope, t[-2]: row}) for row in domain), Fraction())
    return answer * evaluate(t[2], blocks, scope) if t[0] == "ScaleSum" else answer


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
    for case, expression in [("hoist", term), ("dependent", dependent)]:
        path = tmp_path / f"{case}.egg"
        path.write_text(hoist.program(mode, expression))
        args = [str(binary), *(["--slotted"] if mode == "slotted" else []), str(path)]
        result = subprocess.run(args, capture_output=True, text=True, check=True, timeout=30)
        selected = hoist.canonical(reference.parse(result.stdout)[0])
        assert (selected[-1][0] == "ScaleSum") == (case == "hoist")
        for rows in [[], [{"unit_sales": 0}], [{"unit_sales": Fraction(-3, 2)}, {"unit_sales": 4}] * 2]:
            blocks = [{"oilprize": 3, "rows": rows}, {"oilprize": -2, "rows": rows}, {"oilprize": 9, "rows": []}]
            assert evaluate(selected, blocks) == evaluate(expression, blocks)
        if case == "hoist":
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
