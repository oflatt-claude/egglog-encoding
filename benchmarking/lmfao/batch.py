"""Select and execute actual multi-output batch nodes from a slotted e-graph.

The program root is an ordered tree containing every required query. A batch
may replace any subtree, so batch sizes are extraction choices. Sources are
shared DAG dependencies. Bodies and output names come exclusively from the
export, including all binder/edge renamings; no optimized target is supplied.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import asdict, dataclass
from functools import cache
from typing import Any

from .dag import solve
from .sql import Choice, aggregate_batches, execution_sql, ident, join_sql, scalar, symbol

BATCHES = ("Batch", "FusedBatch", "GroupingBatch")


@dataclass(frozen=True)
class Edge:
    cid: str
    renaming: tuple[tuple[int, int], ...]


class Graph:
    def __init__(self, document: dict[str, Any], schema: dict[str, list[str]]) -> None:
        self.document, self.schema, self.nodes = document, schema, document["nodes"]
        self.classes: dict[str, list[str]] = defaultdict(list)
        self.args: dict[str, list[Any]] = {}
        for nid, n in self.nodes.items():
            if n.get("subsumed", False):
                continue
            self.classes[n["eclass"]].append(nid)
            children = iter(n["children"])
            self.args[nid] = [
                a["slot"]
                if a["kind"] == "slot"
                else Edge(self.nodes[next(children)]["eclass"], tuple(map(tuple, a["renaming"])))
                for a in document["slotted"]["nodes"][nid]["arguments"]
            ]
        for data in document["slotted"]["classes"].values():
            if data["group"] != [list(range(len(data["slots"])))]:
                raise ValueError("batch compiler requires trivial class symmetries")
        referenced = {e.cid for args in self.args.values() for e in args if isinstance(e, Edge)}
        roots = [c for c, data in document["slotted"]["classes"].items() if not data["slots"] and c not in referenced]
        if len(roots) != 1:
            raise ValueError("expected one closed program root")
        self.root = roots[0]
        self.outputs = [(0, self.root, ())]  # One tuple root contains every required output.
        self.original: dict[str, str] = {}
        self.options: dict[str, list[str]] = {}
        self.sources: dict[str, tuple[str, list[str]]] = {}
        self.requests: dict[str, tuple[str, list[Choice]]] = {}
        self.deps: dict[str, list[str]] = {}
        self.labels: list[int] = []

        def visit(cid: str) -> None:
            if cid in self.options:
                return
            original = [n for n in self.classes[cid] if self.nodes[n]["op"] in ("Output", "Pair")]
            if len(original) != 1:
                raise ValueError("missing or ambiguous original output tree")
            nid = original[0]
            self.original[cid] = nid
            self.options[cid] = self.classes[cid]
            if self.nodes[nid]["op"] == "Pair":
                for edge in self.args[nid]:
                    visit(edge.cid)
            else:
                name, aggregate = self.args[nid]
                expr = self.expression(aggregate.cid)
                if expr[0] != "sum":
                    raise ValueError("expected an original aggregate")
                src = self.args[self.unique(aggregate.cid)][0].cid
                self.source(src)
                choice = self.choice(self.expression(name.cid), nid, src, expr[2], expr[3], expr[4])
                self.labels.append(choice.output)
                self.requests[nid] = (src, [choice])
            for n in self.options[cid]:
                op = self.nodes[n]["op"]
                if op == "Pair":
                    self.deps[n] = [e.cid for e in self.args[n]]
                elif op == "Output":
                    self.deps[n] = [self.requests[n][0]]
                elif op in BATCHES:
                    source, tasks = self.args[n]
                    self.source(source.cid)
                    self.requests[n] = (source.cid, self.tasks(tasks.cid, source.cid))
                    self.deps[n] = [source.cid]
                else:
                    raise ValueError(f"unsupported program alternative: {op}")

        visit(self.root)
        if sorted(self.labels) != list(range(len(self.labels))):
            raise ValueError("missing or duplicate output labels")

        # Independently check every batch's ordered outputs, source and bodies
        # against its original subtree before permitting extraction.
        @cache
        def signature(cid: str) -> tuple[Any, ...]:
            n = self.original[cid]
            if self.nodes[n]["op"] == "Pair":
                return tuple(x for c in self.deps[n] for x in signature(c))
            source, qs = self.requests[n]
            return tuple((q.output, source, q.groups, q.weight) for q in qs)

        for cid, ns in list(self.options.items()):
            for n in ns:
                if self.nodes[n]["op"] in BATCHES:
                    source, qs = self.requests[n]
                    if tuple((q.output, source, q.groups, q.weight) for q in qs) != signature(cid):
                        raise ValueError("batch changes its original output sequence, source or aggregate body")
        for cid in self.sources:
            n = self.unique(cid)
            self.options[cid] = [n]
            self.original[cid], self.deps[n] = n, []
        self.allowed = {c: set(ns) for c, ns in self.options.items()}

    def unique(self, cid: str) -> str:
        ns = self.classes[cid]
        if len(ns) != 1:
            raise ValueError("unsupported ambiguity inside an aggregate body or source")
        return ns[0]

    def dependencies(self, nid: str) -> list[str]:
        return self.deps[nid]

    def expression(self, cid: str, frame: dict[int, str] | None = None, depth: int = 0) -> tuple[Any, ...]:
        frame = dict(frame or {})
        nid = self.unique(cid)
        op = self.nodes[nid]["op"]
        args: list[Any] = []
        for i, a in enumerate(self.args[nid]):
            if isinstance(a, Edge):
                args.append(self.expression(a.cid, {s: frame[t] for s, t in a.renaming}, depth + 1))
            elif op == "var":
                args.append(frame[a])
            elif (op == "sum" and i in (1, 2)) or (op == "lambda" and i == 0):
                frame[a] = f"v{depth}_{i}"
                args.append(frame[a])
            else:
                raise ValueError("unsupported binding operator")
        return (op, *args)

    def source(self, cid: str) -> tuple[str, list[str]]:
        if cid not in self.sources:
            expr = self.expression(cid)
            if expr[0].startswith("sym:"):
                name = symbol(expr)
                self.sources[cid] = (f"SELECT * FROM {ident(name)}", self.schema[name])
            else:
                self.sources[cid] = join_sql(expr, self.schema)
        return self.sources[cid]

    def choice(
        self, name: tuple[Any, ...], nid: str, source: str, row: str, count: str, body: tuple[Any, ...]
    ) -> Choice:
        fields = self.sources[source][1]

        def degree(expr: tuple[Any, ...]) -> int:
            op, *args = expr
            if op == "var" and args == [count]:
                return 1
            if op == "get" and args[0] == ("var", row) and symbol(args[1]) in fields:
                return 0
            if not args and op.lstrip("-").isdigit():
                return 0
            if op == "*":
                return sum(degree(a) for a in args)
            if op in ("+", "-"):
                a, b = map(degree, args)
                if a == b:
                    return a
            raise ValueError("unsupported aggregate expression or nonhomogeneous multiplicity")

        def group_key(expr: tuple[Any, ...]) -> bool:
            if expr[0] == "Pair":
                return all(group_key(a) for a in expr[1:])
            return expr[0] == "get" and expr[1] == ("var", row) and symbol(expr[2]) in fields

        env = {row: {f: ident(f) for f in fields}, count: "CAST(1 AS DOUBLE)"}
        if body[0] == "sing":
            if not group_key(body[1]):
                raise ValueError("grouping keys must be columns or tuples of columns")
            keys = scalar(body[1], env)

            def flatten(key: Any) -> tuple[str, ...]:
                return tuple(v for k in key for v in flatten(k)) if isinstance(key, tuple) else (key,)

            groups = flatten(keys)
            weight = body[2]
        else:
            groups, weight = (), body
        # A physical SQL row represents one bag occurrence. Replacing the Sum
        # multiplicity by 1 is sound only for bodies linear in multiplicity.
        if degree(weight) != 1:
            raise ValueError("SQL aggregate bodies must be linear in bag multiplicity")
        # Numeric casts are attached to field reads, never grouping keys.
        numeric = {row: {f: f"CAST({ident(f)} AS DOUBLE)" for f in fields}, count: "CAST(1 AS DOUBLE)"}
        return Choice(int(symbol(name).removeprefix("q")), nid, groups, scalar(weight, numeric))

    def tasks(self, cid: str, source: str) -> list[Choice]:
        n = self.unique(cid)
        op, args = self.nodes[n]["op"], self.args[n]
        if op == "TaskPair":
            return [q for a in args for q in self.tasks(a.cid, source)]
        if op != "Task":
            raise ValueError("expected an aggregate task tree")
        name, function = (self.expression(a.cid) for a in args)
        if function[0] != "lambda" or function[2][0] != "lambda":
            raise ValueError("a task must bind row and multiplicity")
        _, row, (_, count, body) = function
        return [self.choice(name, n, source, row, count, body)]


class BatchExtractor:
    def reachable(self, selected: dict[str, str]) -> list[str]:
        order, seen, active = [], set(), set()

        def visit(cid: str) -> None:
            if cid in active:
                raise ValueError("cyclic extracted plan")
            if cid in seen:
                return
            active.add(cid)
            nid = selected[cid]
            if nid not in self.g.allowed[cid]:
                raise ValueError("selected operator is absent from the exported class")
            for dep in self.g.dependencies(nid):
                visit(dep)
            active.remove(cid)
            seen.add(cid)
            order.append(cid)

        for _, root, _ in self.g.outputs:
            visit(root)
        return order

    def __init__(self, graph: Graph, source_rows: dict[str, int], output_rows: dict[int, int]) -> None:
        self.g, self.costs = graph, {}
        for cid, ns in graph.options.items():
            for n in ns:
                if cid in graph.sources:
                    self.costs[n] = source_rows[cid] * len(graph.sources[cid][1])
                elif graph.nodes[n]["op"] == "Pair":
                    self.costs[n] = 0
                else:
                    src, qs = graph.requests[n]
                    mode = graph.nodes[n]["op"]
                    batches = aggregate_batches(qs, fuse=mode in BATCHES[1:], grouping_sets=mode == "GroupingBatch")
                    # Approximate scan/aggregation work, not calibrated seconds.
                    # GROUPING SETS still performs work for every grouping; only
                    # shared source scans and duplicate weight updates disappear.
                    scan = len(batches) * source_rows[src]
                    updates = sum(
                        len({q.weight for q in group}) * source_rows[src] for _, gs in batches for group in gs
                    )
                    result = sum(output_rows[q.output] * (len(q.groups) + 1) for q in qs)
                    self.costs[n] = scan + updates + result

    def score(self, selected: dict[str, str]) -> tuple[int, list[str]]:
        order = self.reachable(selected)
        return sum(self.costs[selected[c]] for c in order), order

    def extract(self, *, dag_timeout: float = 30) -> tuple[dict[str, str], dict[str, Any]]:
        selected = dict(self.g.original)
        original, _ = self.score(selected)
        # A feasible bottom-up initialization; the joint solver below accounts
        # for sharing across subtrees and retains this plan if it cannot improve.
        for cid in self.reachable(selected):
            best, _ = self.score(selected)
            for n in self.g.options[cid]:
                old = selected[cid]
                selected[cid] = n
                value, _ = self.score(selected)
                if value < best:
                    best = value
                else:
                    selected[cid] = old
        initial, _ = self.score(selected)
        solver = None
        if dag_timeout:
            selected, solver = solve(self, selected, dag_timeout)
        cost, order = self.score(selected)
        return selected, {
            "estimated_cost": cost,
            "original_plan_dag_cost": original,
            "heuristic_dag_cost": initial,
            "cost_model": "source scans + aggregate updates per grouping + output cells; shared sources charged once",
            "optimal": bool(solver and solver["optimal"]),
            "solver": solver,
            "selected_nodes": {c: selected[c] for c in order},
        }

    def sql(
        self, selected: dict[str, str], *, lowering_control: bool = False
    ) -> tuple[list[str], list[dict[str, Any]]]:
        g = self.g
        order = self.reachable(selected)
        sources = {c: f"source{i}" for i, c in enumerate(c for c in order if c in g.sources)}
        statements: list[str] = []
        operators: list[dict[str, Any]] = []
        for cid in order:
            n, op = selected[cid], g.nodes[selected[cid]]["op"]
            if cid in sources:
                statements.append(f"CREATE TEMP TABLE {sources[cid]} AS {g.sources[cid][0]}")
                operators.append({"class": cid, "node": n, "op": "Source", "table": sources[cid]})
            elif op != "Pair":
                src, qs = g.requests[n]
                operators.append({"class": cid, "node": n, "op": op, "source": src, "queries": [asdict(q) for q in qs]})
        if lowering_control:
            # Explicit counterfactual: batch across selected program boundaries
            # in the compiler. Label separately; never credit this to rewrites.
            grouped: dict[str, list[Choice]] = defaultdict(list)
            for o in operators:
                if "queries" in o:
                    grouped[o["source"]].extend(Choice(**q) for q in o["queries"])
            blocks = [(s, qs, "GroupingBatch") for s, qs in grouped.items()]
        else:
            blocks = [(o["source"], [Choice(**q) for q in o["queries"]], o["op"]) for o in operators if "queries" in o]
        seen: list[int] = []
        for i, (source, qs, op) in enumerate(blocks):
            seen.extend(q.output for q in qs)
            statements += execution_sql(
                g.sources[source][0],
                qs,
                fuse=op in BATCHES[1:],
                grouping_sets=op == "GroupingBatch",
                source_table=sources[source],
                prefix=f"b{i}_",
                emit_join=False,
            )
        if sorted(seen) != sorted(g.labels):
            raise ValueError("selected program does not produce exactly the required outputs")
        return statements, operators
