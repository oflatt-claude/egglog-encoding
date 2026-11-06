"""Untimed exact cardinalities for the finite view alternatives in an export."""

from __future__ import annotations

from functools import cache
from typing import Any

import duckdb

from . import model
from .logical import Graph
from .model import ident


def collect(
    db: duckdb.DuckDBPyConnection, graph: Graph
) -> tuple[dict[tuple[str, tuple[int, ...]], tuple[int, int]], list[dict[str, Any]]]:
    attrs = [a for a, _ in model.schema()[0]]
    records: list[dict[str, Any]] = []
    by_view: dict[tuple[str, tuple[int, ...]], dict[str, Any]] = {}

    @cache
    def relations(region: str) -> tuple[str, ...]:
        r = graph.regions[region]
        return (r.origin, *(t for child, _ in r.children for t in relations(child)))

    @cache
    def distinct(region: str, keys: tuple[int, ...]) -> tuple[str, int]:
        table = f"stats_{len(records)}"
        columns = ", ".join(ident(attrs[i]) for i in keys) or "1 AS scalar_key"
        source = " NATURAL JOIN ".join(map(ident, relations(region)))
        db.execute(f"CREATE TEMP TABLE {table} AS SELECT DISTINCT {columns} FROM {source}")
        rows = db.execute(f"SELECT COUNT(*) FROM {table}").fetchall()[0][0]
        records.append({"region": region, "relations": relations(region), "keys": keys, "output_rows": rows})
        by_view[region, keys] = records[-1]
        return table, rows

    requests = sorted({(v.region, v.keys) for v in graph.views.values()} | set(graph.producers.values()))
    result = {}
    try:
        for region, keys in requests:
            r = graph.regions[region]
            _, rows = distinct(region, keys)
            sources = [ident(r.origin)]
            for child, separator in r.children:
                childkeys = tuple(sorted(set(separator) | (set(keys) & set(graph.regions[child].attributes))))
                table, _ = distinct(child, childkeys)
                sources.append(table)
            # Incoming aggregate bags have one row per key. Do not use the
            # original join's multiplicities as the physical join-work estimate.
            work = db.execute("SELECT COUNT(*) FROM " + " NATURAL JOIN ".join(sources)).fetchall()[0][0]
            by_view[region, keys]["join_rows"] = work
            result[region, keys] = (work, rows)
        return result, records
    finally:
        for i in range(len(records)):
            db.execute(f"DROP TABLE stats_{i}")
