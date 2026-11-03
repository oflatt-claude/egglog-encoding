"""Test workload identity, commands, fact directories, defaults, and prove screening."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from benchmarking import models, targets, workloads
from benchmarking.engines import validate_binary_workload

from .report_fixtures import ROOT


def test_validate_workloads_rejects_duplicate_cache_identities(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts")

    with pytest.raises(ValueError, match=r"first\.egg.*second\.egg.*identical file and fact-directory hashes"):
        workloads.validate_workloads((first, second))


def test_same_file_with_different_fact_contents_is_a_distinct_workload(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts-a")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts-b")

    workloads.validate_workloads((first, second))


@pytest.mark.parametrize("command", ("prove", "prove-extract"))
def test_resolve_files_rejects_executable_prove_benchmark_file(tmp_path: Path, command: str) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(
        f"; comments may mention (prove ...)\n(datatype Expr)\n({command} (Fact))\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="explicit prove command"):
        workloads.resolve_files([str(prove_file)], tmp_path)


@pytest.mark.parametrize(
    "source",
    (
        "(check (= 1 1)) (prove (= 1 1))\n",
        "( check (= 1 1))\n( ; comment between the parenthesis and command\n prove (= 1 1))\n",
    ),
)
def test_prove_scan_detects_top_level_commands_beyond_line_starts(tmp_path: Path, source: str) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(source, encoding="utf-8")

    with pytest.raises(ValueError, match="explicit prove command"):
        workloads.resolve_files([str(prove_file)], tmp_path)


def test_resolve_files_allows_prove_mentions_in_comments(tmp_path: Path) -> None:
    check_file = tmp_path / "check.egg"
    check_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(check (Fact))\n",
        encoding="utf-8",
    )

    assert workloads.resolve_files([str(check_file)], tmp_path)[0].absolute_path == check_file.resolve()


def test_prove_scan_ignores_comments_strings_and_longer_atoms(tmp_path: Path) -> None:
    check_file = tmp_path / "check.egg"
    check_file.write_text(
        '; (prove (Comment))\n(let text "escaped \\"(prove (String))\\"")\n'
        "(check (= 1 1)) ; (prove (InlineComment))\n(prove-more (NotACommand))\n",
        encoding="utf-8",
    )

    assert workloads.resolve_files([str(check_file)], tmp_path)[0].sha256 == targets.sha256_file(check_file)


def test_default_workloads_are_the_eleven_research_cases() -> None:
    files = workloads.resolve_files([], ROOT)
    assert tuple(file.display_path for file in files) == (
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg",
        "egglog/tests/pointer-analysis-initdb.egg",
        "egglog/tests/hardboiled_conv1d_32.egg",
        "egglog/tests/luminal-llama.egg",
        "egglog/tests/web-demo/herbie.egg",
        "egglog/tests/papers/misaal-hvx-dot-product.egg",
        "egglog/tests/papers/churchroad-wide-multiply.egg",
        "egglog-experimental/tests/papers/dialegg-nmm40.egg",
        "egglog/tests/papers/speq-preserved-reference-suite.egg",
        "benchmarks/disequality/parameter-analysis.egg",
    )
    pointer = next(file for file in files if file.display_path == "egglog/tests/pointer-analysis-initdb.egg")
    assert pointer.fact_directory == (ROOT / "egglog/tests/pointer-analysis-initdb").resolve()
    assert pointer.fact_directory_sha256.startswith("sha256:")


def test_pointer_initdb_facts_are_the_complete_consumed_artifact_relations() -> None:
    fact_directory = ROOT / "egglog/tests/pointer-analysis-initdb"
    files = tuple(sorted(fact_directory.glob("*.csv")))

    assert len(files) == 23
    assert sum(len(path.read_text(encoding="utf-8").splitlines()) for path in files) == 73_864
    assert targets.sha256_directory(fact_directory) == (
        "sha256:28354d7f25d8c198d923be014bbb1ee2292501e12cdde29ea90e666bc86b6929"
    )


def test_explicit_fact_directory_is_resolved_and_hashed(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "input.egg"
    benchmark_file.write_text('(input Edge "edge.tsv")\n', encoding="utf-8")
    facts = tmp_path / "facts"
    facts.mkdir()
    (facts / "edge.tsv").write_text("a\tb\n", encoding="utf-8")

    (file_spec,) = workloads.resolve_files(["input.egg"], tmp_path, "facts")

    assert file_spec.fact_directory == facts.resolve()
    assert file_spec.fact_directory_sha256 == targets.sha256_directory(facts)


def test_fact_directory_requires_explicit_benchmark_file(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="requires at least one explicit benchmark file"):
        workloads.resolve_files([], tmp_path, "facts")


def test_workload_command_matches_benchmark_behavior() -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "off") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proofs") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--proofs",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proof-extraction") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--proof-extraction",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proof-testing") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--proof-testing",
        str(file_spec.absolute_path),
    ]

    facts = ROOT / "facts"
    file_with_facts = models.FileSpec(
        "file.egg",
        ROOT / "file.egg",
        "sha256:file",
        facts,
        "sha256:facts",
    )
    command = targets.workload_command(ROOT / "egglog-experimental", file_with_facts, "proofs")
    assert command[5:7] == ["--fact-directory", str(facts)]


def test_egg_workload_command_uses_the_fixed_math_driver_contract() -> None:
    (math,) = workloads.resolve_files(["egglog-experimental/tests/math-microbenchmark-rational.egg"], ROOT)

    assert targets.workload_command(ROOT / "egg-math-benchmark", math, "egg-proof-testing") == [
        str(ROOT / "egg-math-benchmark"),
        "--proof-mode",
        "check",
    ]


def test_egg_treatments_reject_other_workloads_and_fact_directories(tmp_path: Path) -> None:
    other_path = tmp_path / "other.egg"
    other_path.write_text("(check (= 1 1))")
    other = models.FileSpec("other.egg", other_path, targets.sha256_file(other_path))
    with pytest.raises(ValueError, match="only supports registered Math workloads"):
        validate_binary_workload(other, "egg")

    math = models.FileSpec(
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        ROOT / "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "sha256:math",
        ROOT / "facts",
    )
    with pytest.raises(ValueError, match="does not support --fact-directory"):
        validate_binary_workload(math, "egg-proofs")


@pytest.mark.parametrize("prefix", ("", '; input include prove "\n', '(let message "text; not a comment")\n'))
def test_self_contained_input_hashes_file_and_fact_directory(tmp_path: Path, prefix: str) -> None:
    path = tmp_path / "main.egg"
    facts = tmp_path / "facts"
    facts.mkdir()
    csv = facts / "rows.csv"
    csv.write_text("1\n")
    path.write_text(prefix + '(input F "rows.csv")\n')
    first = workloads.resolve_files([str(path)], tmp_path, str(facts))[0]
    assert first.sha256 == targets.sha256_file(path)
    assert first.fact_directory_sha256 == targets.sha256_directory(facts)
    csv.write_text("2\n")
    changed = workloads.resolve_files([str(path)], tmp_path, str(facts))[0]
    assert changed.sha256 == first.sha256
    assert changed.fact_directory_sha256 != first.fact_directory_sha256
    with pytest.raises(ValueError, match="workload changed"):
        workloads.require_workload_unchanged(first)


@pytest.mark.parametrize("newline", ["\n", "\r\n"])
def test_standalone_identity_ignores_control_words_in_comments(tmp_path: Path, newline: str) -> None:
    path = tmp_path / "main.egg"
    source = '; input include prove "\n(datatype T (A))\n(check (= (A) (A)))'
    path.write_bytes(source.replace("\n", newline).encode())
    assert workloads.resolve_files([str(path)], tmp_path)[0].sha256 == targets.sha256_file(path)


@pytest.mark.parametrize("note", ("not; a comment", "(", ")", 'escaped "(include file)"'))
def test_proof_after_quoted_text_is_not_hidden(tmp_path: Path, note: str) -> None:
    path = tmp_path / "main.egg"
    path.write_text(f"(let note {json.dumps(note)}) (prove (= 1 1))")
    with pytest.raises(ValueError, match="explicit prove command"):
        workloads.resolve_files([str(path)], tmp_path)


@pytest.mark.parametrize(
    "source", ('(include "other.egg")', '(fail (include "other.egg"))', '(let note "(") (include "other.egg")')
)
def test_benchmark_inputs_reject_includes(tmp_path: Path, source: str) -> None:
    path = tmp_path / "main.egg"
    path.write_text(source)
    with pytest.raises(ValueError, match="self-contained"):
        workloads.resolve_files([str(path)], tmp_path)


@pytest.mark.parametrize("name", ("../outside.csv", "absolute", "symlink.csv"))
@pytest.mark.parametrize("options", ("", " :internal-proof-base 1"))
def test_input_paths_cannot_escape_the_hashed_fact_directory(tmp_path: Path, name: str, options: str) -> None:
    facts = tmp_path / "facts"
    facts.mkdir()
    outside = tmp_path / "outside.csv"
    outside.write_text("1\n")
    (facts / "symlink.csv").symlink_to(outside)
    if name == "absolute":
        name = str(outside)
    path = tmp_path / "main.egg"
    path.write_text(f"(input F {json.dumps(name)}{options})")
    with pytest.raises(ValueError, match="inside --fact-directory"):
        workloads.resolve_files([str(path)], tmp_path, str(facts))


def test_csv_input_requires_an_explicit_hashed_directory(tmp_path: Path) -> None:
    path = tmp_path / "main.egg"
    path.write_text('(input F "rows.csv")')
    with pytest.raises(ValueError, match="require --fact-directory"):
        workloads.resolve_files([str(path)], tmp_path)


def test_shared_exclusions_match_logical_and_physical_configuration(tmp_path: Path) -> None:
    import json

    (tmp_path / "slotted").mkdir()
    (tmp_path / "slotted/a.egg").write_text("(check (= 1 1))")
    (tmp_path / "slotted/a.ref").write_text("{}")
    ignore = tmp_path / "ignore.json"
    ignore.write_text(
        json.dumps(
            [
                {
                    "file": "slotted/*.egg",
                    "treatments": ["slotted-ref-nested"],
                    "kind": "unsupported",
                    "reason": "fixture has no nested representation",
                    "evidence": "a.ref",
                }
            ]
        )
    )
    file = workloads.resolve_files(["slotted/a.egg"], tmp_path, ignore_file=ignore)[0]
    assert file.exclusion_for("slotted", memory_limit_bytes=None) is None
    rule = file.exclusion_for("slotted-ref-nested", memory_limit_bytes=None)
    assert rule is not None and rule.kind == "unsupported"
    assert file.for_binary("slotted-reference").exclusion_for("slotted-ref-nested", memory_limit_bytes=None) == rule


def test_cap_specific_exclusions_do_not_suppress_uncapped_results(tmp_path: Path) -> None:
    import json

    (tmp_path / "a.egg").write_text("(check (= 1 1))")
    ignore = tmp_path / "ignore.json"
    ignore.write_text(
        json.dumps(
            [
                {
                    "file": "a.egg",
                    "treatments": ["proof-testing"],
                    "kind": "resource",
                    "reason": "recorded address-space cap stop",
                    "evidence": "exit 86 in a fresh process",
                    "memory_limit_bytes": 10 * 1024**3,
                }
            ]
        )
    )
    file = workloads.resolve_files(["a.egg"], tmp_path, ignore_file=ignore)[0]
    assert file.exclusion_for("proof-testing", memory_limit_bytes=10 * 1024**3) is not None
    assert file.exclusion_for("proof-testing", memory_limit_bytes=8 * 1024**3) is not None
    assert file.exclusion_for("proof-testing", memory_limit_bytes=None) is None
    assert file.exclusion_for("proof-testing", memory_limit_bytes=16 * 1024**3) is None
    assert file.exclusion_for("off", memory_limit_bytes=10 * 1024**3) is None


@pytest.mark.parametrize("sizes", [None, {}, {"A": [1]}, {"A": [1, True]}, {"A": [-1, 2]}, {"A": [1, 1]}])
def test_expected_failure_requires_a_precise_table_size_difference(tmp_path: Path, sizes: object) -> None:
    source = tmp_path / "case.egg"
    source.write_text("(check (= 1 1))")
    policy = tmp_path / "ignore.json"
    policy.write_text(
        json.dumps(
            [
                {
                    "file": "case.egg",
                    "kind": "expected-failure",
                    "treatments": ["term"],
                    "reason": "tracked bug",
                    "evidence": "issue",
                    "expected_table_sizes": sizes,
                }
            ]
        )
    )
    with pytest.raises(ValueError, match="expected failures require"):
        workloads.resolve_files([str(source)], tmp_path, ignore_file=policy)


def test_expected_failure_is_quarantined_only_for_its_treatment(tmp_path: Path) -> None:
    source = tmp_path / "case.egg"
    source.write_text("(check (= 1 1))")
    policy = tmp_path / "ignore.json"
    policy.write_text(
        json.dumps(
            [
                {
                    "file": "case.egg",
                    "kind": "expected-failure",
                    "treatments": ["term"],
                    "reason": "tracked bug",
                    "evidence": "issue",
                    "expected_table_sizes": {"A": [1, 2]},
                }
            ]
        )
    )
    (file,) = workloads.resolve_files([str(source)], tmp_path, ignore_file=policy)
    excluded = file.exclusion_for("term", memory_limit_bytes=None)
    assert excluded is not None and excluded.kind == "expected-failure"
    assert file.exclusion_for("off", memory_limit_bytes=None) is None
    assert file.exclusion_for("proof-testing", memory_limit_bytes=None) is None


def test_overlapping_exclusions_reject_ambiguous_execution_policy(tmp_path: Path) -> None:
    resource = models.Exclusion("resource", "cap", "capture", ("term",), memory_limit_bytes=10 * 1024**3)
    expected = models.Exclusion("expected-failure", "bug", "issue", ("term",))
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file", exclusions=(resource, expected))
    with pytest.raises(ValueError, match="overlapping benchmark exclusions"):
        file.exclusion_for("term", memory_limit_bytes=10 * 1024**3)
    assert file.exclusion_for("term", memory_limit_bytes=None) == expected
    assert file.exclusion_for("off", memory_limit_bytes=10 * 1024**3) is None


def test_input_containment_resolves_a_symlinked_fact_directory(tmp_path: Path) -> None:
    facts = tmp_path / "facts"
    facts.mkdir()
    (facts / "rows.csv").write_text("1\n")
    alias = tmp_path / "alias"
    alias.symlink_to(facts, target_is_directory=True)
    path = tmp_path / "main.egg"
    path.write_text('(input F "rows.csv")')
    file = models.FileSpec("main.egg", path, targets.sha256_file(path), fact_directory=alias)
    workloads.validate_workloads((file,))
