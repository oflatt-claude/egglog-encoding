"""Select an acyclic DAG covering every required root under a solver budget.

Charge each selected node once. Retain the feasible incumbent if the solver
cannot improve its cost; report optimality only for the configured objective.
"""

from __future__ import annotations

import time
from collections import Counter
from typing import Any


def solve(extractor: Any, incumbent: dict[str, str], timeout: float) -> tuple[dict[str, str], dict[str, Any]]:
    import highspy
    import numpy as np
    from scipy.sparse import coo_array
    from scipy.sparse.csgraph import connected_components

    start = time.perf_counter()
    g = extractor.g
    best, incumbent_order = extractor.score(incumbent)
    # Exclude nodes unreachable even when every alternative is permitted.
    roots = {c for _, c, _ in g.outputs}
    live, pending = set(), list(roots)
    while pending:
        cid = pending.pop()
        if cid not in live:
            live.add(cid)
            pending.extend(d for n in g.options[cid] for d in g.dependencies(n))
    classes = [c for c in g.options if c in live]
    nodes = [n for c in classes for n in g.options[c]]
    index = {c: i for i, c in enumerate(classes)}
    edges = [(index[g.nodes[n]["eclass"]], index[d]) for n in nodes for d in g.dependencies(n)]
    adjacency = coo_array(
        (np.ones(len(edges)), ([a for a, _ in edges], [b for _, b in edges])),
        shape=(len(classes), len(classes)),
    ).tocsr()
    _, component = connected_components(adjacency, directed=True, connection="strong")
    sizes = Counter(component)
    cyclic = {c for c in classes if sizes[component[index[c]]] > 1 or any(c in g.dependencies(n) for n in g.options[c])}
    # Class activation and ranks need not be integral: the representative
    # equality makes activation integral, and continuous ranks exclude cycles.
    x = {n: i for i, n in enumerate(nodes)}
    y = {c: len(x) + i for i, c in enumerate(classes)}
    h = {c: len(x) + len(y) + i for i, c in enumerate(c for c in classes if c in cyclic)}
    count = max([*x.values(), *y.values(), *h.values()]) + 1
    objective = np.zeros(count)
    integer = np.zeros(count)
    upper = np.ones(count)
    for n, i in x.items():
        objective[i] = extractor.costs[n]
        integer[i] = 1
    for c, i in h.items():
        upper[i] = sizes[component[index[c]]] - 1
    ri: list[int] = []
    ci: list[int] = []
    data: list[float] = []
    lower: list[float] = []
    bounds: list[float] = []

    def constraint(terms: Any, lo: float = -np.inf, hi: float = np.inf) -> None:
        row = len(lower)
        for col, coefficient in terms:
            ri.append(row)
            ci.append(col)
            data.append(coefficient)
        lower.append(lo)
        bounds.append(hi)

    for c in classes:
        constraint([(y[c], -1), *((x[n], 1) for n in g.options[c])], 0, 0)
        if c in roots:
            constraint([(y[c], 1)], 1, 1)
    for n in nodes:
        parent = g.nodes[n]["eclass"]
        for child in set(g.dependencies(n)):
            constraint([(x[n], 1), (y[child], -1)], hi=0)
            if parent in cyclic and component[index[parent]] == component[index[child]]:
                size = sizes[component[index[parent]]]
                constraint([(h[parent], 1), (h[child], -1), (x[n], -size)], lo=1 - size)
    constraint([(i, c) for i, c in enumerate(objective) if c], hi=best)
    matrix = coo_array((data, (ri, ci)), shape=(len(lower), count)).tocsc()
    warm = np.zeros(count)
    heights: dict[str, int] = {}
    for c in incumbent_order:
        n = incumbent[c]
        warm[x[n]] = warm[y[c]] = 1
        if c in h:
            heights[c] = max(
                (heights[d] + 1 for d in g.dependencies(n) if component[index[c]] == component[index[d]]), default=0
            )
            warm[h[c]] = heights[c]
    activity = matrix @ warm
    if np.any(activity < np.array(lower) - 1e-6) or np.any(activity > np.array(bounds) + 1e-6):
        raise AssertionError("the DAG incumbent does not satisfy the MILP")
    if not np.isclose(objective @ warm, best, rtol=1e-10, atol=1e-8):
        raise AssertionError("the MILP and executable DAG cost disagree")
    model = highspy.HighsLp()
    model.num_col_, model.num_row_ = count, len(lower)
    model.col_cost_, model.col_lower_, model.col_upper_ = objective, np.zeros(count), upper
    model.row_lower_, model.row_upper_ = lower, bounds
    model.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    model.a_matrix_.start_, model.a_matrix_.index_, model.a_matrix_.value_ = matrix.indptr, matrix.indices, matrix.data
    model.integrality_ = [highspy.HighsVarType.kInteger if i else highspy.HighsVarType.kContinuous for i in integer]
    solver = highspy.Highs()
    solver.setOptionValue("output_flag", False)
    solver.setOptionValue("threads", 1)
    solver.setOptionValue("mip_rel_gap", 0.0)
    solver.setOptionValue("mip_abs_gap", 0.0)
    if solver.passModel(model) != highspy.HighsStatus.kOk:
        raise RuntimeError("HiGHS rejected the DAG model")
    solution = highspy.HighsSolution()
    solution.col_value, solution.value_valid = warm, True
    if solver.setSolution(solution) != highspy.HighsStatus.kOk:
        raise RuntimeError("HiGHS rejected the DAG warm start")
    prepared = time.perf_counter() - start
    solver.setOptionValue("time_limit", max(0.001, timeout - prepared))
    solver.run()
    result, solution = solver.getInfo(), solver.getSolution()
    status = solver.getModelStatus()
    selected = incumbent
    accepted = False
    if solution.value_valid:
        choices = {g.nodes[n]["eclass"]: n for n in nodes if solution.col_value[x[n]] > 0.5}
        # Validate the selection independently of the solver's numeric status.
        score, order = extractor.score(choices)
        if score <= best + 1e-6:
            selected = incumbent | {c: choices[c] for c in order}
            best, accepted = score, True
    bound = result.mip_dual_bound if result.valid else None
    lower_bound = None if bound is None or not np.isfinite(bound) else max(0.0, float(bound))
    gap = None if lower_bound is None else max(0.0, best - lower_bound) / max(best, 1e-12)
    return selected, {
        "method": "HiGHS MILP: one joint DAG over all output roots",
        "version": solver.version(),
        "status": solver.modelStatusToString(status),
        "optimal": bool(status == highspy.HighsModelStatus.kOptimal and accepted),
        "warm_start": True,
        "optimality_scope": "configured DAG-cost objective within this exported e-graph, not runtime",
        "accepted_solver_plan": accepted,
        "lower_bound": lower_bound,
        "relative_gap": gap,
        "seconds": time.perf_counter() - start,
        "preparation_seconds": prepared,
        "time_limit_seconds": timeout,
        "node_variables": len(x),
        "cyclic_classes": len(cyclic),
        "constraints": len(lower),
    }
