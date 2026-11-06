"""Check joint DAG selection against exhaustive search, including cycles."""

import itertools
import random
from types import SimpleNamespace
from typing import Any

import pytest

from benchmarking.lmfao.batch import BatchExtractor
from benchmarking.lmfao.dag import solve


def problem(alternatives: dict[str, list[tuple[float, list[str]]]], roots: list[str]) -> Any:
    options = {c: [f"{c}/{i}" for i in range(len(ns))] for c, ns in alternatives.items()}
    nodes, deps, costs = {}, {}, {}
    for c, ns in alternatives.items():
        for n, (cost, children) in zip(options[c], ns, strict=True):
            nodes[n], deps[n], costs[n] = {"op": "work", "eclass": c}, children, cost
    graph = SimpleNamespace(
        options=options,
        allowed={c: set(ns) for c, ns in options.items()},
        nodes=nodes,
        dependencies=deps.__getitem__,
        outputs=[(i, c, ()) for i, c in enumerate(roots)],
    )
    extractor: Any = BatchExtractor.__new__(BatchExtractor)
    extractor.g = graph
    extractor.costs = costs
    return extractor


def exhaustive(extractor: Any) -> float:
    best = float("inf")
    for choices in itertools.product(*extractor.g.options.values()):
        try:
            cost, _ = extractor.score(dict(zip(extractor.g.options, choices, strict=True)))
        except ValueError:
            continue
        best = min(best, cost)
    return best


def test_joint_roots_pay_optional_producer_once() -> None:
    ex = problem({"a": [(8, []), (1, ["p"])], "b": [(8, []), (1, ["p"])], "p": [(12, [])]}, ["a", "b"])
    initial = {c: ns[0] for c, ns in ex.g.options.items()}
    assert ex.score(initial)[0] == 16
    assert ex.score(initial | {"a": "a/1"})[0] == 21
    selected, info = solve(ex, initial, 5)
    assert ex.score(selected)[0] == 14 == exhaustive(ex)
    assert info["optimal"] and info["relative_gap"] == pytest.approx(0)


@pytest.mark.parametrize("self_loop", [False, True])
def test_recursive_choices_are_excluded(self_loop: bool) -> None:
    ex = problem({"a": [(5, []), (0, ["a" if self_loop else "b"])], "b": [(7, []), (0, ["a"])]}, ["a", "b"])
    selected, info = solve(ex, {"a": "a/0", "b": "b/0"}, 5)
    assert ex.score(selected)[0] == exhaustive(ex) == 5
    assert info["optimal"] and info["cyclic_classes"] > 0


def test_small_random_graphs_match_exhaustive_optimum() -> None:
    rng = random.Random(7814)
    for _ in range(20):
        alternatives: dict[str, list[tuple[float, list[str]]]] = {
            c: [(rng.randrange(1, 10), []), (rng.randrange(4), rng.sample(list("abcd"), rng.randrange(1, 3)))]
            for c in "abcd"
        }
        ex = problem(alternatives, ["a", "b"])
        selected, info = solve(ex, {c: f"{c}/0" for c in "abcd"}, 5)
        assert info["optimal"]
        assert ex.score(selected)[0] == exhaustive(ex)


def test_solver_limit_retains_feasible_incumbent() -> None:
    ex = problem({"a": [(8, []), (1, ["p"])], "b": [(8, []), (1, ["p"])], "p": [(12, [])]}, ["a", "b"])
    initial = {c: ns[0] for c, ns in ex.g.options.items()}
    selected, info = solve(ex, initial, 1e-9)
    assert ex.score(selected)[0] <= 16
    assert info["warm_start"]
