"""Compile-only program-size exports for the restricted SDQL comparison."""

from __future__ import annotations

import csv
import hashlib
import io
import json
import subprocess
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from .models import FileSpec
from .targets import git_sha, sha256_file

ROOT = Path(__file__).resolve().parents[1]
STAGES = ("source", "slotted", "proof_congruence")
COLUMNS = ("Benchmark", "Input", "Input → Slotted", "Input → Slotted → Proofs")
NOTE = (
    "Whole-program S-expression AST nodes: each list, atom, and literal counts once; "
    "comments and whitespace do not count. These are the current adapted inputs for the same ten named "
    "SDQL workloads, compiled by the current source checkout. Source and compiler identities are "
    "recorded separately from the timing figure; these sizes do not describe different historical "
    "input/compiler identities. The second column of sizes is the current restricted-aliasing "
    "Slotted compiler output. The final column first applies the public Slotted source proof "
    "profile (Compiler::compile_program with ProofMode::Prove), then lowers accepted output through "
    "core congruence and proof instrumentation. Current SDQL inputs are rejected by the source "
    "proof profile because their subst rewrite has no proof translation. Proof-compatible Check "
    "sizes and congruence-only attempts are separate diagnostics, not substitutes for the final "
    "Proofs stage. Compilation only: no saturation, proof extraction, or verification runs. These "
    "sizes do not establish proof correctness. Unsupported means compilation rejected the source "
    "profile or subsequent composition; a partially lowered program is not counted."
)


def export_slotted_ast(
    files: Sequence[FileSpec], destination: Path, *, compiler: Path | None = None
) -> tuple[Path, ...]:
    """Use the real compiler and parser, then publish auditable companion files."""
    command = (
        [str(compiler.resolve())]
        if compiler is not None
        else ["cargo", "run", "--locked", "--release", "-p", "egglog-experimental", "--example", "slotted_ast", "--"]
    )
    completed = subprocess.run(
        [*command, *(str(file.absolute_path) for file in files)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        check=True,
    )
    measured = [json.loads(line) for line in completed.stdout.splitlines()]
    if [row["file"] for row in measured] != [str(file.absolute_path) for file in files]:
        raise ValueError("AST compiler returned a different workload selection")
    rows: list[dict[str, Any]] = []
    programs = []
    for file, row in zip(files, measured, strict=True):
        native = file.for_binary("slotted-reference")
        source_hash = "sha256:" + hashlib.sha256(row["programs"]["source"].encode()).hexdigest()
        if source_hash != file.sha256:
            raise ValueError(f"AST compiler read changed input: {file.display_path}")
        kernel, separator, phase = row["benchmark"].removesuffix("-44rules").rpartition("_")
        publication = {"batax": "BATAX", "mmm": "MMM", "mmm_sum": "ΣMMM", "mttkrp": "MTTKRP", "ttm": "TTM"}
        label = f"{publication.get(kernel, kernel)} / {phase}" if separator else row["benchmark"]
        rows.append(
            {
                "benchmark": row["benchmark"],
                "label": label,
                "file": file.display_path,
                "file_sha256": source_hash,
                "reference_file": native.display_path,
                "reference_sha256": native.sha256,
                **{f"{stage}_ast_nodes": row[f"{stage}_ast_nodes"] for stage in STAGES},
                "proof_compatible_slotted_ast_nodes": row["proof_compatible_slotted_ast_nodes"],
                "proof_congruence_error": row["proof_congruence_error"],
                "proof_congruence_error_debug": row["proof_congruence_error_debug"],
                "proof_congruence_error_stage": row["proof_congruence_error_stage"],
                "congruence_ast_nodes": row["congruence_ast_nodes"],
                "congruence_error": row["congruence_error"],
                "program_sha256": {
                    stage: "sha256:" + hashlib.sha256(row["programs"][stage].encode()).hexdigest()
                    for stage in row["programs"]
                    if row["programs"][stage] is not None
                },
            }
        )
        programs.append({"file": file.display_path, **row["programs"]})
    compiler_path = Path(measured[0]["compiler_binary"])
    report = {
        "figure": "slotted-runtime",
        "source_checkout": str(ROOT),
        "source_revision": git_sha(ROOT),
        "timing_identity": "See slotted-runtime.results.json; compare its input/engine hashes separately",
        "metric": NOTE,
        "proof_pipeline": "Compiler::compile_program(ProofMode::Prove) -> new_egraph_with_proofs().resolve_program",
        "diagnostics": "ProofMode::Check intermediate size and congruence-only lowering are diagnostic fields only",
        "compiler_binary": str(compiler_path),
        "compiler_binary_sha256": sha256_file(compiler_path),
        "command": command,
        "rows": rows,
    }
    csv_output = io.StringIO()
    writer = csv.writer(csv_output, lineterminator="\n")
    writer.writerow(COLUMNS)
    markdown = ["| " + " | ".join(COLUMNS) + " |", "| :--- | ---: | ---: | ---: |"]
    latex = [
        r"\begin{tabular}{lrrr}",
        r"\toprule",
        r"Benchmark & Input & \shortstack{Input $\rightarrow$\\ Slotted} & "
        r"\shortstack{Input $\rightarrow$ Slotted\\ $\rightarrow$ Proofs} \\",
        r"\midrule",
    ]
    for row in rows:
        values = [row[f"{stage}_ast_nodes"] for stage in STAGES]
        writer.writerow([row["label"], *(value if value is not None else "Unsupported" for value in values)])
        markdown.append(
            "| "
            + " | ".join([row["label"], *(f"{value:,}" if value is not None else "Unsupported" for value in values)])
            + " |"
        )
        name = row["label"].replace("_", r"\_").replace("Σ", r"$\Sigma$")
        latex.append(
            name + " & " + " & ".join(f"{value:,}" if value is not None else "Unsupported" for value in values) + r" \\"
        )
    latex.extend([r"\bottomrule", r"\end{tabular}", ""])
    markdown.extend(["", NOTE, ""])
    failures = {
        next((line.removeprefix("Reason: ") for line in error.splitlines() if line.startswith("Reason: ")), error)
        for row in rows
        if (error := row["proof_congruence_error"])
    }
    if failures:
        markdown.extend(["The Proofs compilation stage is unavailable:", ""])
        markdown.extend(f"- {failure}" for failure in sorted(failures))
        markdown.append("")
    markdown.extend(["Files:", ""])
    markdown.extend(f"- `{row['file']}` (native: `{row['reference_file']}`)" for row in rows)
    contents = {
        "ast.json": json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        "ast-programs.json": json.dumps(programs, indent=2, ensure_ascii=False) + "\n",
        "ast.csv": csv_output.getvalue(),
        "ast.tex": "\n".join(latex),
        "ast.md": "\n".join(markdown) + "\n",
        "files.txt": "".join(f"{row['file']}\t{row['reference_file']}\n" for row in rows),
    }
    destination.mkdir(parents=True, exist_ok=True)
    outputs = []
    for suffix, content in contents.items():
        path = destination / f"slotted-runtime.{suffix}"
        path.write_text(content)
        outputs.append(path)
    return tuple(outputs)
