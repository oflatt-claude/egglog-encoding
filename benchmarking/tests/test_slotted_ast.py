"""AST exports must retain selected inputs and distinguish compilation from timing."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any

import pytest

from benchmarking.models import FileSpec
from benchmarking.slotted_ast import export_slotted_ast
from benchmarking.targets import sha256_file


def test_exports_include_native_input_hashes_and_actual_programs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = "(sort U)\n"
    file = tmp_path / "case_1st.egg"
    native = file.with_suffix(".ref")
    file.write_text(source)
    native.write_text("native fixture")
    compiler = tmp_path / "compiler"
    compiler.write_text("compiler fixture")
    physical = FileSpec(str(native), native, sha256_file(native))
    selected = FileSpec(str(file), file, sha256_file(file), (("slotted-reference", physical),))
    measured: dict[str, Any] = {
        "file": str(file),
        "benchmark": file.stem,
        "compiler_binary": str(compiler),
        "programs": {
            "source": source,
            "slotted": "(sort U) (rule () ())",
            "proof_compatible_slotted": "(sort U) (rule () ()) (ruleset proof)",
            "proof_congruence": "(sort U) (rule () ()) (ruleset proof) (rule () ())",
        },
        "source_ast_nodes": 4,
        "slotted_ast_nodes": 8,
        "proof_compatible_slotted_ast_nodes": 12,
        "proof_congruence_ast_nodes": 16,
        "proof_congruence_error": None,
        "proof_congruence_error_debug": None,
        "proof_congruence_error_stage": None,
        "congruence_ast_nodes": 15,
        "congruence_error": None,
    }
    run = subprocess.run
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda args, **kwargs: (
            subprocess.CompletedProcess([], 0, json.dumps(measured) + "\n")
            if args[0] == str(compiler)
            else run(args, **kwargs)
        ),
    )
    outputs = export_slotted_ast([selected], tmp_path / "out", compiler=compiler)
    report = json.loads((tmp_path / "out/slotted-runtime.ast.json").read_text())
    assert report["rows"][0]["reference_sha256"] == physical.sha256
    assert report["rows"][0]["proof_compatible_slotted_ast_nodes"] == 12
    assert report["compiler_binary_sha256"] == sha256_file(compiler)
    assert "Compiler::compile_program with ProofMode::Prove" in report["metric"]
    assert "ProofMode::Check" in report["diagnostics"]
    assert json.loads((tmp_path / "out/slotted-runtime.ast-programs.json").read_text())[0]["source"] == source
    assert (tmp_path / "out/slotted-runtime.files.txt").read_text() == f"{file}\t{native}\n"
    assert len(outputs) == 6

    measured["proof_congruence_ast_nodes"] = None
    measured["programs"]["proof_congruence"] = None
    measured["proof_congruence_error"] = "At beta rewrite\nuses subst, which has no proof translation"
    measured["proof_congruence_error_debug"] = "Source(UnsupportedProofFeature { feature: Substitution })"
    measured["proof_congruence_error_stage"] = "source-slotted-proofs"
    export_slotted_ast([selected], tmp_path / "unsupported", compiler=compiler)
    unsupported = json.loads((tmp_path / "unsupported/slotted-runtime.ast.json").read_text())
    assert unsupported["rows"][0]["proof_congruence_ast_nodes"] is None
    assert "proof_congruence" not in unsupported["rows"][0]["program_sha256"]
    assert "Unsupported" in (tmp_path / "unsupported/slotted-runtime.ast.tex").read_text()
    assert "uses subst, which has no proof translation" in (tmp_path / "unsupported/slotted-runtime.ast.md").read_text()
    assert unsupported["rows"][0]["proof_congruence_error_stage"] == "source-slotted-proofs"
    assert "UnsupportedProofFeature" in unsupported["rows"][0]["proof_congruence_error_debug"]

    measured["programs"]["source"] = "(sort Changed)"
    with pytest.raises(ValueError, match="changed input"):
        export_slotted_ast([selected], tmp_path / "out", compiler=compiler)
    assert json.loads((tmp_path / "out/slotted-runtime.ast.json").read_text()) == report


def test_rejects_compiler_workload_selection_drift(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    selected = FileSpec("selected.egg", tmp_path / "selected.egg", "hash")
    monkeypatch.setattr(
        subprocess, "run", lambda *args, **kwargs: subprocess.CompletedProcess([], 0, '{"file":"different.egg"}\n')
    )
    with pytest.raises(ValueError, match="different workload selection"):
        export_slotted_ast([selected], tmp_path / "out", compiler=tmp_path / "compiler")
    assert not (tmp_path / "out").exists()
