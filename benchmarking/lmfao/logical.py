"""Decode executable alternatives and extract one shared DAG for all queries."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from functools import cache
from typing import Any

from . import model
from .dag import solve


@dataclass(frozen=True)
class Edge:
    cid: str
    renaming: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class Region:
    origin: str
    destination: str
    attributes: tuple[int, ...]
    functions: tuple[int, ...]
    local: tuple[int, ...]
    children: tuple[tuple[str, tuple[int, ...]], ...]


@dataclass(frozen=True)
class View:
    region: str
    keys: tuple[int, ...]
    weights: tuple[int, ...]
    local: tuple[int, ...]
    incoming: tuple[str, ...]
    producer: str | None


class Graph:
    def __init__(self, document: dict[str, Any]) -> None:
        self.nodes = document["nodes"]
        self.classes: dict[str, list[str]] = defaultdict(list)
        self.args: dict[str, list[Edge | int]] = {}
        for nid, node in self.nodes.items():
            if node.get("subsumed", False):
                continue
            self.classes[node["eclass"]].append(nid)
            children = iter(node["children"])
            self.args[nid] = [
                a["slot"]
                if a["kind"] == "slot"
                else Edge(self.nodes[next(children)]["eclass"], tuple(map(tuple, a["renaming"])))
                for a in document["slotted"]["nodes"][nid]["arguments"]
            ]
        for data in document["slotted"]["classes"].values():
            if data["group"] != [list(range(len(data["slots"])))]:
                raise ValueError("logical decoder requires trivial class symmetries")
        self._weights: dict[str, tuple[int, ...]] = {}
        self.function_specs = model.function_specs()
        self.relations = model.schema()[1]
        self.regions: dict[str, Region] = {}
        for cid, ns in self.classes.items():
            for n in ns:
                if self.nodes[n]["op"] == "Region":
                    origin, destination, attrs, functions, local, children = self.edges(n)
                    self.regions[cid] = Region(
                        self.symbol(origin),
                        self.symbol(destination),
                        self.mask(attrs),
                        self.mask(functions),
                        self.mask(local),
                        tuple(
                            (self.edges(e)[0], self.mask(self.edges(e)[1]))
                            for c in self.linked(children)
                            for e in [self.one(c, {"Neighbor"})]
                        ),
                    )
        programs = [n for n in self.args if self.nodes[n]["op"] == "Program"]
        if len(programs) != 1:
            raise ValueError("expected one Program")
        self.outputs: list[tuple[int, str, tuple[Any, ...]]] = []

        def output_tree(cid: str) -> None:
            n = self.one(cid, {"Pair", "Output"})
            if self.nodes[n]["op"] == "Pair":
                for c in self.edges(n):
                    output_tree(c)
            else:
                label, root = self.edges(n)
                query = self.one(root, {"AggregateQuery"})
                _, keys, weights = self.edges(query)
                self.outputs.append(
                    (int(self.symbol(label).removeprefix("q")), root, (self.mask(keys), self.weights(weights)))
                )

        output_tree(self.edges(programs[0])[0])
        self.outputs.sort()
        if [i for i, _, _ in self.outputs] != list(range(len(self.outputs))):
            raise ValueError("missing or duplicate query labels")
        self.views: dict[str, View] = {}
        self.producers: dict[str, tuple[str, tuple[int, ...]]] = {}
        self.options: dict[str, list[str]] = {}
        self.deps: dict[str, list[str]] = {}
        pending = [c for _, c, _ in self.outputs]
        while pending:
            cid = pending.pop()
            if cid in self.options:
                continue
            ns = [n for n in self.classes[cid] if self.nodes[n]["op"] in {"ComputeView", "ViewColumn", "SharedView"}]
            if not ns:
                raise ValueError(f"no executable alternative for {cid}; increase rewrite budget")
            self.options[cid] = ns
            for n in ns:
                op, args = self.nodes[n]["op"], self.edges(n)
                if op == "SharedView":
                    region, keys = args
                    self.producers[n] = (region, self.mask(keys))
                    self.deps[n] = []
                    continue
                if op == "ComputeView":
                    region, keys, weights, local, children = args
                    producer = None
                else:
                    producer, weights, local, children = args
                    region, keys = self.edges(self.one(producer, {"SharedView"}))
                incoming = tuple(self.linked(children))
                self.views[n] = View(
                    region, self.mask(keys), self.weights(weights), self.weights(local), incoming, producer
                )
                self.deps[n] = [*incoming, *([producer] if producer else [])]
                pending.extend(self.deps[n])
        self.validate()

    def one(self, cid: str, ops: set[str]) -> str:
        ns = [n for n in self.classes[cid] if self.nodes[n]["op"] in ops]
        if len(ns) != 1:
            raise ValueError(f"expected one canonical {ops} in {cid}, got {len(ns)}")
        return ns[0]

    def edges(self, nid: str) -> list[str]:
        args = self.args[nid]
        if any(not isinstance(a, Edge) or a.renaming for a in args):
            raise ValueError("expected closed metadata")
        return [a.cid for a in args if isinstance(a, Edge)]

    def symbol(self, cid: str) -> str:
        ns = [n for n in self.classes[cid] if self.nodes[n]["op"].startswith("sym:")]
        if len(ns) != 1:
            raise ValueError("expected one symbol")
        return str(self.nodes[ns[0]]["op"]).removeprefix("sym:")

    def bits(self, cid: str) -> tuple[bool, ...]:
        n = self.one(cid, {"Mask", "B0", "B1"})
        if self.nodes[n]["op"] == "Mask":
            return tuple(b for c in self.edges(n) for b in self.bits(c))
        return (self.nodes[n]["op"] == "B1",)

    def mask(self, cid: str) -> tuple[int, ...]:
        return tuple(i for i, b in enumerate(self.bits(cid)) if b)

    def linked(self, cid: str) -> tuple[str, ...]:
        n = self.one(cid, {"Cons", "Nil"})
        if self.nodes[n]["op"] == "Nil":
            return ()
        head, tail = self.edges(n)
        return (head, *self.linked(tail))

    def expression(self, cid: str, frame: dict[int, str] | None = None, depth: int = 0) -> tuple[Any, ...]:
        frame = dict(frame or {})
        n = self.one(
            cid,
            {"lambda", "var", "get", "*"}
            | {self.nodes[n]["op"] for n in self.classes[cid] if self.nodes[n]["op"].startswith("sym:")},
        )
        op = self.nodes[n]["op"]
        args: list[Any] = []
        for a in self.args[n]:
            if isinstance(a, Edge):
                args.append(self.expression(a.cid, {s: frame[t] for s, t in a.renaming}, depth + 1))
            elif op == "lambda":
                frame[a] = f"v{depth}"
                args.append(frame[a])
            elif op == "var":
                args.append(frame[a])
            else:
                raise ValueError("unsupported scalar binding")
        return (op, *args)

    def weight_leaves(self, cid: str) -> tuple[tuple[Any, ...] | None, ...]:
        n = self.one(cid, {"Weights", "WeightOne", "Scalar"})
        op = self.nodes[n]["op"]
        if op == "Weights":
            return tuple(w for c in self.edges(n) for w in self.weight_leaves(c))
        if op == "WeightOne":
            return (None,)
        owner, body = self.edges(n)
        return ((self.symbol(owner), self.expression(body)),)

    def weights(self, cid: str) -> tuple[int, ...]:
        if cid in self._weights:
            return self._weights[cid]
        specs, relations = self.function_specs, self.relations
        result = []
        for i, value in enumerate(self.weight_leaves(cid)):
            if value is None:
                continue
            if i >= len(specs):
                raise ValueError("nonempty padding weight")
            name, power = specs[i]
            owner, body = value
            var = body[1]
            expected: tuple[Any, ...] = ("get", ("var", var), (f"sym:{name}",))
            if power == 2:
                expected = ("*", expected, expected)
            if name not in relations[owner] or body != ("lambda", var, expected):
                raise ValueError("scalar kernel differs from the original function")
            result.append(i)
        self._weights[cid] = tuple(result)
        return self._weights[cid]

    def dependencies(self, nid: str) -> list[str]:
        return self.deps[nid]

    def signature(self, cid: str) -> tuple[str, tuple[int, ...], tuple[int, ...]]:
        signatures = {
            (self.views[n].region, self.views[n].keys, self.views[n].weights)
            for n in self.options[cid]
            if n in self.views
        }
        if len(signatures) != 1:
            raise ValueError("ambiguous intermediate view semantics")
        return next(iter(signatures))

    def validate(self) -> None:
        for _, cid, (keys, weights) in self.outputs:
            for n in self.options[cid]:
                v = self.views[n]
                r = self.regions[v.region]
                if (v.keys, v.weights) != (keys, weights) or r.origin != r.destination:
                    raise ValueError("alternative changes original query")
        for v in self.views.values():
            r = self.regions[v.region]
            if v.local != tuple(w for w in v.weights if w in r.local) or len(v.incoming) != len(r.children):
                raise ValueError("invalid local kernel or incoming arity")
            for cid, (region, separator) in zip(v.incoming, r.children, strict=True):
                child = self.regions[region]
                expected_keys = tuple(sorted(set(separator) | (set(v.keys) & set(child.attributes))))
                expected_weights = tuple(w for w in v.weights if w in child.functions)
                if self.signature(cid) != (region, expected_keys, expected_weights):
                    raise ValueError("invalid aggregate pushdown")


class Extractor:
    def __init__(
        self, graph: Graph, statistics: dict[tuple[str, tuple[int, ...]], tuple[int, int]] | None = None
    ) -> None:
        self.g, self.costs = graph, {}
        self.cost_model = "structural" if statistics is None else "cardinality"
        for ns in graph.options.values():
            for n in ns:
                v = graph.views.get(n)
                region, keys = (v.region, v.keys) if v else graph.producers[n]
                work, rows = (1, 1) if statistics is None else statistics[region, keys]
                base = work * (1 + len(graph.regions[region].children)) + rows * len(keys)
                update = work * (1 + len(v.local)) + rows if v else 0
                self.costs[n] = update + (base if v is None or v.producer is None else 0)

    def score(self, selected: dict[str, str]) -> tuple[float, list[str]]:
        done, visiting, order = set(), set(), []

        def visit(cid: str) -> None:
            if cid in done:
                return
            if cid in visiting:
                raise ValueError("cyclic extraction")
            n = selected[cid]
            if n not in self.g.options[cid]:
                raise ValueError("selection is not an exported alternative")
            visiting.add(cid)
            for d in self.g.dependencies(n):
                visit(d)
            visiting.remove(cid)
            done.add(cid)
            order.append(cid)

        for _, c, _ in self.g.outputs:
            visit(c)
        return sum(self.costs[selected[c]] for c in order), order

    def extract(self, timeout: float = 30) -> tuple[dict[str, str], dict[str, Any]]:
        @cache
        def tree(cid: str) -> tuple[float, str]:
            return min(
                (self.costs[n] + sum(tree(d)[0] for d in self.g.dependencies(n)), n) for n in self.g.options[cid]
            )

        selected = {c: tree(c)[1] for c in self.g.options}
        initial, _ = self.score(selected)
        selected, solver = solve(self, selected, timeout)
        cost, order = self.score(selected)
        return selected, {
            "estimated_cost": cost,
            "initial_tree_plan_dag_cost": initial,
            "solver": solver,
            "cost_model": self.cost_model,
            "cost_description": (
                "producer + join inputs + grouping columns; per-column update/output + local functions; "
                "shared producers charged once; no data statistics"
                if self.cost_model == "structural"
                else "scan/join rows + per-column update rows + output cells; shared producers charged once"
            ),
            "selected_nodes": {c: selected[c] for c in order},
        }

    def plan(self, selected: dict[str, str]) -> dict[str, Any]:
        """Serialize selected producer identities and columns, without merging views."""
        g = self.g
        _, order = self.score(selected)
        tables = list(model.schema()[1])
        views: list[dict[str, Any]] = []
        producers: dict[str, int] = {}
        columns: dict[str, tuple[int, int]] = {}
        for cid in order:
            n = selected[cid]
            if n not in g.views:
                continue
            v = g.views[n]
            producer = v.producer or cid
            if producer not in producers:
                r = g.regions[v.region]
                producers[producer] = len(views)
                views.append(
                    {
                        "origin": tables.index(r.origin),
                        "destination": tables.index(r.destination),
                        "keys": list(v.keys),
                        "aggregates": [],
                    }
                )
            index = producers[producer]
            aggregates = views[index]["aggregates"]
            columns[cid] = (index, len(aggregates))
            aggregates.append({"functions": list(v.local), "incoming": [list(columns[c]) for c in v.incoming]})
        outputs = [
            {"view": columns[c][0], "aggregate": columns[c][1], "root": views[columns[c][0]]["origin"]}
            for _, c, _ in g.outputs
        ]
        return {"views": views, "outputs": outputs}
