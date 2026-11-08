"""Exact SDQL evaluation and sparse inputs for the artifact's five kernels."""

from __future__ import annotations

import random
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Any


@dataclass
class Array:
    values: tuple[Any, ...]
    stop: int | None = None

    def items(self) -> Any:
        end = len(self.values) if self.stop is None else self.stop
        return enumerate(self.values[:end], 1)

    def get(self, key: int, default: Any = 0) -> Any:
        return self.values[key - 1] if 1 <= key <= len(self.values) else default


def add(a: Any, b: Any) -> Any:
    if a == 0:
        return b
    if b == 0:
        return a
    if isinstance(a, dict) and isinstance(b, dict):
        return {k: add(a.get(k, 0), b.get(k, 0)) for k in a.keys() | b.keys()}
    return a + b


def multiply(a: Any, b: Any) -> Any:
    if isinstance(a, dict):
        if isinstance(b, dict):
            raise ValueError("this evaluator supports scalar-dictionary multiplication")
        return {k: multiply(v, b) for k, v in a.items()}
    if isinstance(b, dict):
        return multiply(b, a)
    return a * b


def evaluate(t: Any, scope: dict[str, Any], counts: Counter[str]) -> Any:
    if isinstance(t, str):
        return scope[t]
    op = t[0]
    counts[op] += 1
    if op == "Num":
        return int(t[1])
    if op == "Lambda":
        return lambda value: evaluate(t[2], {**scope, t[1]: value}, counts)
    if op == "Let":
        return evaluate(t[3], {**scope, t[2]: evaluate(t[1], scope, counts)}, counts)
    if op == "Sum":
        domain = evaluate(t[1], scope, counts)
        result: Any = 0
        for key, value in [] if domain == 0 else domain.items():
            counts["iterations"] += 1
            result = add(result, evaluate(t[4], {**scope, t[2]: key, t[3]: value}, counts))
        return result
    if op == "Merge":
        left, right = evaluate(t[1], scope, counts), evaluate(t[2], scope, counts)
        result = 0
        for ka, va in [] if left == 0 else left.items():
            for kb, vb in [] if right == 0 else right.items():
                if va == vb:
                    result = add(result, evaluate(t[6], {**scope, t[3]: ka, t[4]: kb, t[5]: va}, counts))
        return result
    args = [evaluate(c, scope, counts) for c in t[1:]]
    if op == "Sing":
        return {args[0]: args[1]}
    if op == "Unique":
        return args[0]
    if op == "Get":
        return args[0].get(args[1], 0) if args[0] != 0 else 0
    if op == "SubArray":
        a, start, end = args
        return {i: v for i, v in a.items() if start <= i <= end}
    if op == "Range":
        start, end = args
        return {i: i + start - 1 for i in range(1, end - start + 2)}
    if op == "Add":
        return add(*args)
    if op == "Sub":
        return args[0] - args[1]
    if op == "Mult":
        return multiply(*args)
    raise ValueError(f"unsupported SDQL operator: {op}")


def normalize(value: Any) -> Any:
    if isinstance(value, dict):
        return {k: v for k, raw in value.items() if (v := normalize(raw)) != 0} or 0
    return value


def execute(term: Any, arguments: list[Any]) -> tuple[Any, dict[str, int]]:
    counts: Counter[str] = Counter()
    value = evaluate(term, {}, counts)
    for arg in arguments:
        value = value(arg)
    return normalize(value), dict(counts)


def csr(matrix: dict[int, dict[int, Fraction]]) -> list[Array]:
    pointers, indices, values = [1], [], []
    for row in matrix.values():
        for col, value in row.items():
            indices.append(col)
            values.append(value)
        pointers.append(len(indices) + 1)
    return [Array(tuple(pointers), len(matrix)), Array(tuple(indices)), Array(tuple(values))]


def csf(tensor: dict[int, dict[int, dict[int, Fraction]]]) -> list[Array]:
    outer, middle, inner, values = [], [], [], []
    middle_ptr, inner_ptr = [1], [1]
    for i, slab in tensor.items():
        outer.append(i)
        for j, row in slab.items():
            middle.append(j)
            for k, value in row.items():
                inner.append(k)
                values.append(value)
            inner_ptr.append(len(inner) + 1)
        middle_ptr.append(len(middle) + 1)
    arrays: list[list[Any]] = [outer, middle_ptr, middle, inner_ptr, inner, values]
    return [Array(tuple(v)) for v in arrays]


def case(kernel: str, n: int, seed: int) -> tuple[list[Any], list[Any], Any]:
    """Return first/second-phase arguments and an independent dense-loop answer."""
    rng = random.Random(seed)
    keys = range(1, n + 1)
    a = {(i, j): Fraction(rng.randrange(-2, 3), 2) for i, j in product(keys, repeat=2)}
    b = {(i, j): Fraction(rng.randrange(-2, 3), 2) for i, j in product(keys, repeat=2)}
    t = {(i, j, k): Fraction(rng.randrange(-2, 3), 2) for i, j, k in product(keys, repeat=3)}
    vector = {i: Fraction(rng.randrange(-2, 3), 2) for i in keys}
    ma = {i: {j: a[i, j] for j in keys if a[i, j]} for i in keys}
    mb = {i: {j: b[i, j] for j in keys if b[i, j]} for i in keys}
    tensor = {i: {j: {k: t[i, j, k] for k in keys if t[i, j, k]} for j in keys} for i in keys}
    expected: Any
    if kernel == "mmm_sum":
        expected = sum(a[k, i] * b[k, j] for k, i, j in product(keys, repeat=3))
        return [ma, mb], [*csr(ma), *csr(mb)], expected
    if kernel == "mmm":
        expected = {i: {j: sum(a[i, k] * b[k, j] for k in keys) for j in keys} for i in keys}
        return [ma, mb], [*csr(ma), *csr(mb)], normalize(expected)
    if kernel == "ttm":
        expected = {
            i: {j: {k: sum(t[i, j, ell] * a[k, ell] for ell in keys) for k in keys} for j in keys} for i in keys
        }
        return [ma, tensor], [*csr(ma), *csf(tensor)], normalize(expected)
    if kernel == "mttkrp":
        expected = {
            i: {j: sum(t[i, k, ell] * a[k, j] * b[j, ell] for k, ell in product(keys, repeat=2)) for j in keys}
            for i in keys
        }
        return [tensor, ma, mb], [*csf(tensor), *csr(ma), *csr(mb)], normalize(expected)
    if kernel == "batax":
        scalar = Fraction(-3, 2)
        expected = {j: scalar * sum(a[i, j] * a[i, k] * vector[k] for i, k in product(keys, repeat=2)) for j in keys}
        return [scalar, ma, vector], [scalar, *csr(ma), Array(tuple(vector.values())), n], normalize(expected)
    raise ValueError(kernel)
