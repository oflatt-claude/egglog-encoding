"""Frontend kernels and a de Bruijn control for multi-output sum fusion."""

from __future__ import annotations

import json
from typing import Any

from benchmarks.reproduction.slotted import reference
from benchmarks.reproduction.slotted.lmfao import balanced

from . import model

FIXTURES = model.FIXTURES / "hoisting"
BINDERS = {"Sum": 2, "ScaleSum": 3, "Lambda": 1}


def query_indices() -> list[int]:
    return [i for i, q in enumerate(model.WORKLOAD.queries) if not q.groups]


def query() -> Any:
    outputs = []
    for i in query_indices():
        oil, sale = f"$oil{i}", f"$sale{i}"
        functions = []
        for f in model.WORKLOAD.document["queries"][i]["functions"]:
            name, power = model.WORKLOAD.functions[int(f)]
            arg = f"$function{i}_{f}"
            value: Any = ["Field", arg, json.dumps(name)]
            if power == 2:
                value = ["Mul", value, value]
            functions.append(["App", ["Lambda", arg, value], oil if name == "oilprize" else sale])
        body = balanced("Mul", functions) if functions else ["One"]
        outputs.append(["Sum", ["Blocks"], oil, ["Sum", ["Rows", oil], sale, body]])
    return balanced("Pair", outputs)


def to_debruijn(t: Any, scope: tuple[str, ...] = ()) -> Any:
    if isinstance(t, str):
        if t.startswith("$"):
            return ["Var", str(scope[::-1].index(t))]
        return t
    if t[0] in BINDERS:
        i = BINDERS[t[0]]
        return [t[0], *[to_debruijn(c, scope) for c in t[1:i]], to_debruijn(t[i + 1], (*scope, t[i]))]
    return [to_debruijn(c, scope) for c in t]


def from_debruijn(t: Any, scope: tuple[str, ...] = ()) -> Any:
    if isinstance(t, str):
        return t
    if t[0] == "Var":
        index = int(t[1])
        if not 0 <= index < len(scope):
            raise ValueError("extracted de Bruijn variable escapes its scope")
        return scope[-index - 1]
    if t[0] in BINDERS:
        name = f"$v{len(scope)}"
        return [t[0], *[from_debruijn(c, scope) for c in t[1:-1]], name, from_debruijn(t[-1], (*scope, name))]
    if t[0] in ("Shift", "Subst"):
        raise ValueError("extraction selected unresolved scope operations")
    return [from_debruijn(c, scope) for c in t]


def program(mode: str, term: Any | None = None, *, rounds: int = 64, fuse: bool = True) -> str:
    if mode == "debruijn":
        forms = reference.parse((FIXTURES / "debruijn.egg").read_text())
    else:
        forms = reference.parse((FIXTURES / "rules.egg").read_text())
        forms += reference.parse((FIXTURES / "fusion.egg").read_text())
    if not fuse:
        forms = [f for f in forms if not (f[0] == "rewrite" and '"fuse-sums"' in f)]
    term = query() if term is None else term
    forms += [
        ["let", "input", to_debruijn(term) if mode == "debruijn" else term],
        ["run", str(rounds)],
        ["extract", "input"],
    ]
    return "\n".join(reference.render(f) for f in forms) + "\n"


def width(t: Any) -> int:
    if t[0] == "Pair":
        return width(t[1]) + width(t[2])
    if t[0] in BINDERS:
        return width(t[-1])
    return 1


def kernel(term: Any) -> str:
    """Emit the selected loops and calls verbatim, with componentwise tuple sums."""
    lines = ["__attribute__((noinline)) Answers kernel(const Data& data) {"]
    serial = 0

    def emit(t: Any, scope: dict[str, tuple[str, str]]) -> list[str]:
        nonlocal serial
        op = t[0]
        if op == "One":
            return ["1.0"]
        if op == "Field":
            var, kind = scope[t[1]]
            name = json.loads(t[2])
            if (kind, name) == ("block", "oilprize"):
                return [f"data.blocks[{var}].oil"]
            if kind == "sale" and name in ("unit_sales", "transactions"):
                return [f"data.sales[{var}][{int(name == 'transactions')}]"]
            raise ValueError("field does not belong to this binding")
        if op == "Mul":
            a, b = emit(t[1], scope), emit(t[2], scope)
            if len(a) != 1 or len(b) != 1:
                raise ValueError("Mul requires scalars")
            return [f"({a[0]} * {b[0]})"]
        if op == "Pair":
            return emit(t[1], scope) + emit(t[2], scope)
        serial += 1
        suffix = serial
        if op == "App" and t[1][0] == "Lambda" and isinstance(t[2], str):
            arg, kind = scope[t[2]]
            fn, param, result = f"fn{suffix}", f"p{suffix}", f"call{suffix}"
            lines.append(f"auto {fn} = [&](size_t {param}) -> double {{")
            body = emit(t[1][-1], {**scope, t[1][1]: (param, kind)})
            if len(body) != 1:
                raise ValueError("frontend functions return scalars")
            lines.extend([f"return {body[0]};", "};", f"double {result} = {fn}({arg});"])
            return [result]
        if op not in ("Sum", "ScaleSum"):
            raise ValueError(f"unsupported selected operator: {op}")
        results, index = [f"sum{suffix}_{i}" for i in range(width(t))], f"i{suffix}"
        domain, binder, body = t[1], t[-2], t[-1]
        factor = emit(t[2], scope)[0] if op == "ScaleSum" else None
        if domain[0] == "Blocks":
            low, high, kind = "0", "data.blocks.size()", "block"
        elif domain[0] == "Rows":
            parent, parent_kind = scope[domain[1]]
            if parent_kind != "block":
                raise ValueError("Rows requires an oil binding")
            low, high, kind = f"data.blocks[{parent}].begin", f"data.blocks[{parent}].end", "sale"
        else:
            raise ValueError("unsupported sum domain")
        lines.extend(f"double {result} = 0;" for result in results)
        lines.append(f"for (size_t {index} = {low}; {index} < {high}; ++{index}) {{")
        values = emit(body, {**scope, binder: (index, kind)})
        lines.extend(f"{result} += {value};" for result, value in zip(results, values, strict=True))
        lines.append("}")
        return [f"({factor} * {result})" if factor is not None else result for result in results]

    answers = emit(term, {})
    return "\n".join([*lines, "return {{" + ", ".join(answers) + "}};", "}"])
