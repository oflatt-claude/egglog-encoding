"""Reference translation must preserve side patterns and reject omitted constraints."""

import importlib
from pathlib import Path
from typing import Any

import pytest

syntax = importlib.import_module("slotted.reference")


def source(tmp_path: Path) -> Any:
    path = tmp_path / "language.egg"
    path.write_text("(datatype U (F U U) (G U U) (Null))")
    src = syntax.Source(path)
    for op in src.lang.ops.values():
        op.ref = op.ctor
    return src


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
