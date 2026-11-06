"""Same-backend execution and an independent decimal oracle for all outputs."""

from __future__ import annotations

import hashlib
import math
import time
from pathlib import Path
from typing import Any

import duckdb

from . import model
from .sql import Choice, execution_sql, ident

type Results = list[list[tuple[Any, ...]]]


def load_data(directory: Path) -> tuple[duckdb.DuckDBPyConnection, dict[str, Any]]:
    for filename in ("features.conf", "treedecomposition.conf"):
        if (directory / filename).read_bytes() != (model.FIXTURES / filename).read_bytes():
            raise ValueError(f"{filename} differs from the pinned artifact")
    attrs, relations, _ = model.schema()
    types = {name: "DECIMAL(18,6)" if kind == "double" else "BIGINT" for name, kind in attrs}
    db = duckdb.connect()
    db.execute("SET threads=1")
    hashes, sizes = {}, {}
    try:
        for name, columns in relations.items():
            path = directory / f"{name}.tbl"
            hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
            db.read_csv(str(path), delimiter="|", header=False, columns={c: types[c] for c in columns}).create(name)
            sizes[name] = db.sql(f"SELECT COUNT(*) FROM {ident(name)}").fetchall()[0][0]
    except Exception:
        db.close()
        raise
    return db, {"duckdb": duckdb.__version__, "data_sha256": hashes, "input_rows": sizes, "lmfao_commit": model.COMMIT}


def reference_results(db: duckdb.DuckDBPyConnection) -> Results:
    db.execute("CREATE TEMP TABLE oracle AS SELECT * FROM " + " NATURAL JOIN ".join(map(ident, model.schema()[1])))
    expected = []
    for query in model.queries():
        groups = [ident(g) for g in query.groups]
        weight = " * ".join(f"CAST({ident(f)} AS DECIMAL(38,6))" for f in query.factors) or "1"
        fields = [f"{g} AS g{i}" for i, g in enumerate(groups)] + [f"COALESCE(SUM({weight}), 0) AS value"]
        sql = f"SELECT {', '.join(fields)} FROM oracle" + (" GROUP BY " + ", ".join(groups) if groups else "")
        expected.append(db.execute(sql).fetchall())
    return expected


def strong_baseline() -> list[str]:
    choices = []
    for i, query in enumerate(model.queries()):
        weight = " * ".join(f"CAST({ident(f)} AS DOUBLE)" for f in query.factors) or "CAST(1 AS DOUBLE)"
        choices.append(Choice(i, "SQL-baseline", tuple(map(ident, query.groups)), weight))
    join = "SELECT * FROM " + " NATURAL JOIN ".join(map(ident, model.schema()[1]))
    return execution_sql(join, choices, fuse=True, grouping_sets=True)


def execute(
    db: duckdb.DuckDBPyConnection, statements: list[str], expected: Results, queries: list[model.Query]
) -> dict[str, Any]:
    connection = db.cursor()
    try:
        start = time.perf_counter()
        for sql in statements:
            connection.execute(sql).fetchall()
        seconds = time.perf_counter() - start
        worst = 0.0
        for i, want_rows in enumerate(expected):
            got_rows = connection.execute(f"SELECT * FROM q{i}").fetchall()
            got = {tuple(r[:-1]): r[-1] for r in got_rows}
            want = {tuple(r[:-1]): r[-1] for r in want_rows}
            if len(got) != len(got_rows) or got.keys() != want.keys():
                raise AssertionError(f"query {i}: output grouping keys differ")
            for key, value in want.items():
                actual, value = float(got[key]), float(value)
                equal = (
                    math.isclose(actual, value, rel_tol=1e-9, abs_tol=1e-7) if queries[i].factors else actual == value
                )
                if not equal:
                    raise AssertionError((i, key, actual, value))
                worst = max(worst, abs(actual - value) / max(1.0, abs(value)))
        return {"seconds": seconds, "queries_checked": len(expected), "max_scaled_error": worst}
    finally:
        connection.close()
