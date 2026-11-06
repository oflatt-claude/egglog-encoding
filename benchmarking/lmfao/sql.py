"""Compile selected task bodies into shared SQL aggregates."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Any


def ident(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def symbol(term: tuple[Any, ...]) -> str:
    if len(term) != 1 or not term[0].startswith("sym:"):
        raise ValueError(f"expected symbol, got {term}")
    return str(term[0][4:])


def scalar(term: tuple[Any, ...], env: dict[str, Any], *, decimal: bool = False) -> Any:
    op, *args = term
    if op == "var":
        return env[args[0]]
    if op == "get":
        record = scalar(args[0], env)
        result = record[symbol(args[1])]
        return f"CAST({result} AS DECIMAL(38,6))" if decimal else result
    if op in ("*", "+", "-", "eq"):
        a, b = (scalar(t, env, decimal=decimal) for t in args)
        return f"({a} {'=' if op == 'eq' else op} {b})"
    if op == "Pair":
        return tuple(scalar(t, env, decimal=decimal) for t in args)
    if op in ("First", "Second"):
        return scalar(args[0], env, decimal=decimal)[op == "Second"]
    if not args and op.lstrip("-").isdigit():
        return op
    raise ValueError(f"unsupported SQL expression: {term}")


def record_fields(term: tuple[Any, ...]) -> list[tuple[str, tuple[Any, ...]]]:
    if term[0] == "+":
        return record_fields(term[1]) + record_fields(term[2])
    if term[0] == "sing":
        return [(symbol(term[1]), term[2])]
    raise ValueError("expected a record of field singletons")


def join_sql(term: tuple[Any, ...], schema: dict[str, list[str]]) -> tuple[str, list[str]]:
    """Lower the extracted nested bag comprehension, including its predicates.

    Physical input tables contain one row per bag occurrence, so each input
    multiplicity is one and SQL joins preserve duplicates. A different weight
    expression is rejected instead of accidentally dropping bag multiplicities.
    """
    tables: list[str] = []
    predicates: list[str] = []
    env: dict[str, Any] = {}
    multiplicities: list[str] = []
    while term[0] in ("sum", "ifthen"):
        if term[0] == "sum":
            _, domain, k, v, term = term
            table = symbol(domain)
            alias = f"t{len(tables)}"
            env[k] = {c: f"{alias}.{ident(c)}" for c in schema[table]}
            env[v] = "1"
            tables.append(f"{ident(table)} AS {alias}")
            multiplicities.append(v)
        else:
            _, predicate, term = term
            predicates.append(scalar(predicate, env))
    if term[0] != "sing":
        raise ValueError("expected join record singleton")

    def weight_variables(t: tuple[Any, ...]) -> list[str]:
        if t[0] == "*":
            return weight_variables(t[1]) + weight_variables(t[2])
        if t[0] == "var":
            return [t[1]]
        raise ValueError("unsupported join multiplicity")

    if sorted(weight_variables(term[2])) != sorted(multiplicities):
        raise ValueError("join multiplicities are not the product of the input multiplicities")
    fields = record_fields(term[1])
    select = ", ".join(f"{scalar(t, env)} AS {ident(name)}" for name, t in fields)
    sql = "SELECT " + select + " FROM " + " CROSS JOIN ".join(tables)
    if predicates:
        sql += " WHERE " + " AND ".join(predicates)
    return sql, [name for name, _ in fields]


@dataclass(frozen=True)
class Choice:
    output: int
    node: str
    groups: tuple[str, ...]
    weight: str


def aggregate_batches(
    choices: list[Choice], *, fuse: bool = False, grouping_sets: bool = False, source_table: str = "joined"
) -> list[Any]:
    """The physical batches used by both cost estimation and SQL generation."""
    if grouping_sets and not fuse:
        raise ValueError("grouping sets require aggregate fusion")
    batches = defaultdict(list)
    for c in choices:
        groups = tuple(sorted(set(c.groups))) if fuse else c.groups
        batches[(groups, None if fuse else c.output)].append(c)
    combined = defaultdict(list)
    for (groups, identity), batch in batches.items():
        signature = tuple(sorted({c.weight for c in batch})) if grouping_sets else (groups, identity)
        combined[signature].append(batch)
    return [(source_table, groups) for groups in combined.values()]


def execution_sql(
    join: str,
    choices: list[Choice],
    *,
    fuse: bool = False,
    grouping_sets: bool = False,
    source_table: str = "joined",
    prefix: str = "",
    emit_join: bool = True,
) -> list[str]:
    """Lower one selected batch implementation into materialized aggregate tables.

    The caller enables fusion from its selected enode or explicitly labelled
    compiler control. Group compatibility is implemented by this SQL backend.
    """
    if grouping_sets and not fuse:
        raise ValueError("grouping sets require aggregate fusion")
    statements = [f"CREATE TEMP TABLE {ident(source_table)} AS " + join] if emit_join else []
    for step, (source, group_batches) in enumerate(
        aggregate_batches(choices, fuse=fuse, grouping_sets=grouping_sets, source_table=source_table)
    ):
        table = f"{prefix}batch{step}"
        if len(group_batches) == 1:
            batch = group_batches[0]
            groups = tuple(sorted(set(batch[0].groups))) if fuse else batch[0].groups
            keys = [f"{g} AS g{i}" for i, g in enumerate(groups)]
            fields = keys + [f"COALESCE(SUM({c.weight}), 0) AS v{c.output}" for c in batch]
            statements.append(
                f"CREATE TEMP TABLE {table} AS SELECT {', '.join(fields)} FROM {ident(source)}"
                + (" GROUP BY " + ", ".join(groups) if groups else "")
            )
            for c in batch:
                columns = [f"g{groups.index(g)} AS g{i}" for i, g in enumerate(c.groups)] + [f"v{c.output} AS value"]
                statements.append(f"CREATE TEMP VIEW q{c.output} AS SELECT {', '.join(columns)} FROM {table}")
        else:
            # Coalesce distinct grouping keys only when all requested weights
            # agree. GROUPING_ID distinguishes rollup NULLs from data NULLs.
            keys = sorted({g for batch in group_batches for g in batch[0].groups})
            weights = sorted({c.weight for c in group_batches[0]})
            groups = [tuple(sorted(set(batch[0].groups))) for batch in group_batches]
            if len({frozenset(g) for g in groups}) != len(groups):
                raise ValueError("duplicate grouping sets after key reordering")
            fields = [f"{g} AS h{i}" for i, g in enumerate(keys)]
            fields += [f"COALESCE(SUM({w}), 0) AS w{i}" for i, w in enumerate(weights)]
            fields += [f"GROUPING_ID({', '.join(keys)}) AS grouping_tag"]
            sets = ", ".join("(" + ", ".join(g) + ")" for g in groups)
            statements.append(
                f"CREATE TEMP TABLE {table} AS SELECT {', '.join(fields)} FROM {ident(source)}"
                + f" GROUP BY GROUPING SETS ({sets})"
            )
            for batch in group_batches:
                for c in batch:
                    columns = [f"h{keys.index(g)} AS g{i}" for i, g in enumerate(c.groups)]
                    columns += [f"w{weights.index(c.weight)} AS value"]
                    tag = sum(1 << (len(keys) - 1 - i) for i, k in enumerate(keys) if k not in c.groups)
                    statements.append(
                        f"CREATE TEMP VIEW q{c.output} AS SELECT {', '.join(columns)} FROM {table}"
                        + f" WHERE grouping_tag = {tag}"
                    )
    return statements
