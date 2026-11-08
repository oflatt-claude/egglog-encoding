"""Exact semantic checks for the pinned SDQL inputs and scope translation."""

from pathlib import Path

import pytest

from benchmarking import sdql_values as values
from benchmarking import sdql_vertical as vertical
from benchmarks.reproduction.slotted import reference, sdql


@pytest.mark.parametrize("kernel", sdql.KERNELS)
def test_artifact_phases_and_published_extraction_match_dense_oracle(kernel: str) -> None:
    assert vertical.validate(kernel, {})["exact_cases"] == 15
    source, _ = sdql.workload(kernel, "2nd")
    indices = vertical.to_debruijn(source)
    assert vertical.to_debruijn(vertical.from_debruijn(indices)) == indices


def test_three_slotted_rules_match_the_paper_rule_library() -> None:
    library = [
        f
        for f in reference.parse(sdql.RULES.read_text())
        if f[0] == "rewrite" and f[f.index(":name") + 1].strip('"') in vertical.RULE_NAMES
    ]
    assert reference.parse((vertical.FIXTURES / "rules.egg").read_text()) == library


def test_frozen_ttm_checks_use_the_pinned_input_and_scope_correct_target() -> None:
    source, _ = sdql.workload("ttm", "2nd")
    named = reference.parse((vertical.FIXTURES / "checks-slotted.egg").read_text())
    indexed = reference.parse((vertical.FIXTURES / "checks-debruijn.egg").read_text())
    assert named[0] == ["let", "input", source]
    assert indexed[0] == ["let", "input", vertical.to_debruijn(source)]
    definitions = {f[1]: f[2] for f in named if f[0] == "let"}
    target = definitions["expected"]
    for n in range(5):
        _, low, want = values.case("ttm", n, 0)
        assert values.execute(target, low)[0] == want
    for f in indexed:
        if f[0] == "let":
            assert vertical.to_debruijn(definitions[f[1]]) == f[2]
    assert values.execute(definitions["capture"], [3, 7])[0] == 21
    assert values.execute(definitions["collision"], [{1: 1, 2: 2}])[0] == 9
    assert values.execute(definitions["collision-wrong"], [{1: 1, 2: 2}])[0] == 5
    assert values.execute(definitions["value-collision"], [{1: 2, 2: 2}])[0] == 16
    assert values.execute(definitions["collision-wrong"], [{1: 2, 2: 2}])[0] == 8


def test_decode_rejects_unresolved_and_escaping_scope_operations() -> None:
    for term in [["Var", "0"], ["Var", "-1"], ["Shift", ["Num", "1"], "1", "0"]]:
        with pytest.raises(ValueError):
            vertical.from_debruijn(term)


def test_cli_rejects_invalid_limits_and_report(tmp_path: Path) -> None:
    for options in [["--rounds", "0"], ["--rewrite-rounds", "0"], ["--report", "-"]]:
        with pytest.raises(SystemExit) as error:
            vertical.main(["--output-dir", str(tmp_path), *options])
        assert error.value.code == 2
