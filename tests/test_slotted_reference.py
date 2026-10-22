"""Reference translation must preserve side patterns and reject omitted constraints."""

import importlib
from pathlib import Path
from typing import Any

import pytest

syntax = importlib.import_module("slotted.reference")
LANGUAGES = Path(__file__).resolve().parents[1] / "slotted/languages"


@pytest.mark.parametrize(
    "name,term,reference",
    [
        ("toy", ("F", ("Lam", 0, ("var", 0)), ("Num", 3)), "(f (lam $0 (var $0)) 3)"),
        ("array", ("App", ("Sym", "map"), ("Lam", 0, ("var", 0))), "(app map (lam $0 (var $0)))"),
        ("sdql", ("Add", ("Symbol", "sum"), ("Num", 3)), "(+ sym:sum 3)"),
    ],
)
def test_constructor_names_translate_to_reference_syntax(name: str, term: Any, reference: str) -> None:
    path = LANGUAGES / f"{name}.egg"
    lang = syntax.language(path, path.with_suffix(".ref"))
    assert set(lang.ops) == set(syntax.read_language(path))
    assert lang.sexpr(term) == reference


def source(tmp_path: Path) -> Any:
    path = tmp_path / "language.egg"
    path.write_text("(datatype U (F U U) (G U U) (Null))")
    src = syntax.Source(path)
    for op in src.lang.ops.values():
        op.ref = op.ctor
    return src


@pytest.mark.parametrize(
    "declaration",
    [
        "(datatype Var (Lam Var Var :binder 0) (Pair Var Var))",
        "(datatype* (Var (Lam Var Var :binder 0) (Pair Var Var)))",
        "(sort Var) (constructor Lam (Var Var) Var :binder 0) (constructor Pair (Var Var) Var)",
    ],
)
def test_var_is_an_ordinary_carrier_name(tmp_path: Path, declaration: str) -> None:
    path = tmp_path / "language.egg"
    path.write_text(declaration)
    src = syntax.Source(path)
    assert src.sorts == ["Var"]
    assert src.spec == {"Lam": [syntax.BINDER, syntax.CHILD], "Pair": [syntax.CHILD, syntax.CHILD]}
    assert src.term(syntax.parse("(Lam $a (Pair $a $b))")[0]) == (
        "Lam",
        src.slots.intern("$a"),
        ("Pair", ("var", src.slots.intern("$a")), ("var", src.slots.intern("$b"))),
    )


def test_multipattern_side_conditions_share_their_roots(tmp_path: Path) -> None:
    src = source(tmp_path)
    rule = syntax.parse("(rewrite (Null) a :when ((= t (Null)) (= t (F a b)) (= b (G a b))))")[0]
    lines = syntax.rule_lines(src, src.lang, rule)
    assert {"atom t Null ", "atom t F a b", "atom b G a b"} <= set(lines)
    with pytest.raises(syntax.NestedPatternUnsupported):
        syntax.rule_lines(src, src.lang, rule, nested=True)


def test_generated_reference_variables_do_not_alias_user_variables(tmp_path: Path) -> None:
    src = source(tmp_path)
    rule = syntax.parse("(rewrite (F _sl1 $x) _sl1 :when ((= _p (G $y _sl1))))")[0]
    lines = syntax.rule_lines(src, src.lang, rule)
    variable_roots = {line.split()[1] for line in lines if line.startswith("atom ") and line.split()[2] == "var"}
    assert len(variable_roots) == 2
    assert not variable_roots & {"_sl1", "_p"}
    lhs_root = next(line.split()[1] for line in lines if line.startswith("rhs "))
    assert lhs_root not in {"_sl1", "_p", *variable_roots}


@pytest.mark.parametrize("options", [":when ((= a b))", ":when ((!= a b))", ":fresh $new", ":lead 1"])
def test_unrepresented_reference_constraints_are_rejected(tmp_path: Path, options: str) -> None:
    src = source(tmp_path)
    rule = syntax.parse(f"(rewrite (F a b) a {options})")[0]
    for nested in (False, True):
        with pytest.raises(ValueError, match="unsupported reference rewrite options"):
            syntax.rule_lines(src, src.lang, rule, nested=nested)


def test_side_patterns_can_bind_the_action_through_a_child(tmp_path: Path) -> None:
    src = source(tmp_path)
    rule = syntax.parse("(rewrite a (Null) :when ((= parent (F a b))))")[0]
    assert syntax.rule_lines(src, src.lang, rule)[-1] == "rhs a Null"
    unbound = syntax.parse("(rewrite missing (Null) :when ((= parent (F a b))))")[0]
    with pytest.raises(ValueError, match="root must be bound"):
        syntax.rule_lines(src, src.lang, unbound)
