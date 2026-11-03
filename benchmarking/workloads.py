"""Resolve and validate benchmark workload files shared by run and profile modes.

This module owns the default workload suite, invocation-relative file and fact
directory resolution, content identities, and the rule that measured inputs do
not execute ``(prove ...)``. CLI parsing and endpoint selection belong in their
respective command modules.
"""

from __future__ import annotations

import glob
import hashlib
import json
import os
import re
from collections.abc import Iterator, Sequence
from dataclasses import dataclass, replace
from pathlib import Path

from .engines import ENGINE_INPUT_SUFFIXES, TREATMENTS
from .models import Exclusion, FileSpec, validate_unique_file_identities
from .reports.store import GroupedExclusion
from .targets import sha256_directory, sha256_file


@dataclass(frozen=True)
class WorkloadConfig:
    """One repository-default workload and its optional fact directory."""

    file: str
    fact_directory: str | None = None


DEFAULT_WORKLOADS = (
    WorkloadConfig("egglog-experimental/tests/math-microbenchmark-rational.egg"),
    WorkloadConfig("egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg"),
    WorkloadConfig(
        "egglog/tests/pointer-analysis-initdb.egg",
        "egglog/tests/pointer-analysis-initdb",
    ),
    WorkloadConfig("egglog/tests/hardboiled_conv1d_32.egg"),
    WorkloadConfig("egglog/tests/luminal-llama.egg"),
    WorkloadConfig("egglog/tests/web-demo/herbie.egg"),
    WorkloadConfig("egglog/tests/papers/misaal-hvx-dot-product.egg"),
    WorkloadConfig("egglog/tests/papers/churchroad-wide-multiply.egg"),
    WorkloadConfig("egglog-experimental/tests/papers/dialegg-nmm40.egg"),
    WorkloadConfig("egglog/tests/papers/speq-preserved-reference-suite.egg"),
    WorkloadConfig("benchmarks/disequality/parameter-analysis.egg"),
)
IGNORE_FILE = Path(__file__).resolve().parents[1] / "benchmarks/ignore.json"


def resolve_files(
    raw_files: Sequence[str],
    invocation_cwd: Path,
    fact_directory: str | None = None,
    *,
    ignore_file: Path = IGNORE_FILE,
) -> tuple[FileSpec, ...]:
    """Resolve selected or default workloads relative to the invocation directory."""

    if raw_files:
        chosen = tuple(WorkloadConfig(file, fact_directory) for file in raw_files)
    else:
        if fact_directory is not None:
            raise ValueError("--fact-directory requires at least one explicit benchmark file")
        chosen = DEFAULT_WORKLOADS
    rules = json.loads(ignore_file.read_text())
    if not isinstance(rules, list):
        raise ValueError("benchmark ignore file must contain a list")
    matched_paths: dict[str, set[Path]] = {}
    for rule in rules:
        if (
            not isinstance(rule, dict)
            or not {"file", "kind", "reason", "evidence"} <= set(rule)
            or set(rule)
            - {
                "file",
                "kind",
                "reason",
                "evidence",
                "treatments",
                "disequality_encoding",
                "memory_limit_bytes",
                "expected_table_sizes",
            }
            or any(not isinstance(rule[key], str) or not rule[key].strip() for key in ("file", "reason", "evidence"))
            or rule["kind"] not in ("resource", "unsupported", "expected-failure")
            or not isinstance(rule.get("treatments", []), list)
            or any(t not in TREATMENTS for t in rule.get("treatments", []))
            or rule.get("disequality_encoding") not in (None, "nee", "ee")
            or (
                "memory_limit_bytes" in rule
                and (
                    type(rule["memory_limit_bytes"]) is not int
                    or rule["memory_limit_bytes"] < 1
                    or rule["kind"] != "resource"
                )
            )
        ):
            raise ValueError(f"invalid benchmark exclusion: {rule!r}")
        if rule["kind"] == "expected-failure":
            sizes = rule.get("expected_table_sizes")
            if (
                not isinstance(sizes, dict)
                or not sizes
                or any(not isinstance(name, str) or not name for name in sizes)
                or any(
                    not isinstance(pair, list)
                    or len(pair) != 2
                    or any(type(value) is not int or value < 0 for value in pair)
                    for pair in sizes.values()
                )
                or any(pair[0] == pair[1] for pair in sizes.values())
                or len(rule.get("treatments", [])) != 1
                or rule["treatments"][0] not in ("term", "proof-testing")
                or glob.has_magic(rule["file"])
            ):
                raise ValueError("expected failures require one exact file/treatment and recorded table-size pairs")
        elif "expected_table_sizes" in rule:
            raise ValueError("table-size failure expectations require kind expected-failure")
        if ".." in Path(rule["file"]).parts or Path(rule["file"]).is_absolute():
            raise ValueError("exclusion patterns must stay inside benchmarks/")
        matched_paths[rule["file"]] = {
            Path(path).resolve()
            for path in glob.glob(str(ignore_file.parent / rule["file"]), recursive=True)
            if Path(path).is_file()
        }
        if not matched_paths[rule["file"]]:
            raise ValueError(f"exclusion pattern matched nothing: {rule['file']}")
    files: list[FileSpec] = []
    for workload in chosen:
        display_path = workload.file
        absolute_path = Path(display_path).expanduser()
        if not absolute_path.is_absolute():
            absolute_path = invocation_cwd / absolute_path
        absolute_path = absolute_path.resolve()
        if not absolute_path.is_file():
            raise FileNotFoundError(f"benchmark file does not exist: {display_path}")

        resolved_fact_directory: Path | None = None
        fact_directory_sha256 = ""
        if workload.fact_directory is not None:
            resolved_fact_directory = Path(workload.fact_directory).expanduser()
            if not resolved_fact_directory.is_absolute():
                resolved_fact_directory = invocation_cwd / resolved_fact_directory
            resolved_fact_directory = resolved_fact_directory.resolve()
            if not resolved_fact_directory.is_dir():
                raise FileNotFoundError(f"benchmark fact directory does not exist: {workload.fact_directory}")
            fact_directory_sha256 = sha256_directory(resolved_fact_directory)
        logical_path = absolute_path.with_suffix(".egg")
        if absolute_path.suffix not in (".ref", ".in") or not logical_path.is_file():
            logical_path = absolute_path
        files.append(
            FileSpec(
                display_path=display_path,
                absolute_path=absolute_path,
                sha256=complete_input_sha256(absolute_path, invocation_cwd, resolved_fact_directory),
                working_directory=invocation_cwd.resolve(),
                exclusions=tuple(
                    Exclusion(
                        rule["kind"],
                        rule["reason"],
                        rule["evidence"],
                        tuple(rule.get("treatments", [])),
                        rule.get("disequality_encoding"),
                        rule.get("memory_limit_bytes"),
                    )
                    for rule in rules
                    if logical_path in matched_paths[rule["file"]]
                ),
                fact_directory=resolved_fact_directory,
                fact_directory_sha256=fact_directory_sha256,
            )
        )
    for index, file in enumerate(files):
        representations = []
        for engine, suffix in ENGINE_INPUT_SUFFIXES.items():
            if suffix == file.absolute_path.suffix:
                continue
            native_path = file.absolute_path.with_suffix(suffix)
            if not native_path.is_file():
                continue
            native = replace(
                file,
                display_path=str(Path(file.display_path).with_suffix(suffix)),
                absolute_path=native_path,
                sha256=complete_input_sha256(native_path, invocation_cwd, file.fact_directory),
            )
            representations.append((engine, native))
        files[index] = replace(file, engine_inputs=tuple(representations))
    resolved = tuple(files)
    validate_workloads(resolved)
    return resolved


def exclusion_bindings(files: Sequence[FileSpec]) -> list[GroupedExclusion]:
    """Freeze the current policy for every excluded input, including later retargeting.

    Exclusions belong to the invocation's grouped snapshot, never synthetic raw
    observations. Hash only the small explicit ignore list beyond selected files.
    """
    rules = json.loads(IGNORE_FILE.read_text())
    paths = dict.fromkeys(
        path for rule in rules for path in glob.glob(str(IGNORE_FILE.parent / rule["file"]), recursive=True)
    )
    excluded_files = [*files]
    resolved_paths = {
        physical.absolute_path
        for logical in files
        for physical in (logical, *(file for _, file in logical.engine_inputs))
    }
    for path in paths:
        if Path(path).resolve() in resolved_paths:
            continue
        excluded_files.extend(resolve_files([path], IGNORE_FILE.parent.parent))
    bindings = []
    seen = set()
    for logical in excluded_files:
        for physical in (logical, *(file for _, file in logical.engine_inputs)):
            for rule in logical.exclusions:
                identity = (physical.sha256, rule)
                if identity in seen:
                    continue
                seen.add(identity)
                bindings.append(
                    GroupedExclusion(
                        file_sha256=physical.sha256,
                        treatments=list(rule.treatments),
                        disequality_encoding=rule.disequality_encoding,
                        memory_limit_bytes=rule.memory_limit_bytes,
                        kind=rule.kind,
                        reason=rule.reason,
                        evidence=rule.evidence,
                    )
                )
    return bindings


def _egglog_tokens(source: str, *, strings: bool = False) -> Iterator[str | None]:
    """Yield parentheses and atoms while hiding comments and string contents."""

    index = 0
    while index < len(source):
        character = source[index]
        if character.isspace():
            index += 1
            continue
        if character == ";":
            newline = source.find("\n", index)
            index = len(source) if newline == -1 else newline + 1
            continue
        if character == '"':
            start = index
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            yield json.loads(source[start:index]) if strings else None
            continue
        if character in "()":
            yield character
            index += 1
            continue
        end = index
        while end < len(source) and not source[end].isspace() and source[end] not in ";()":
            end += 1
        yield source[index:end]
        index = end


def file_contains_executable_prove_command(path: Path) -> bool:
    """Return whether a workload contains a top-level proof extraction command."""

    depth = 0
    expecting_command = False
    for token in _egglog_tokens(path.read_text(encoding="utf-8")):
        if token == "(":
            if depth == 0:
                expecting_command = True
            elif expecting_command:
                expecting_command = False
            depth += 1
        elif token == ")":
            if depth == 1:
                expecting_command = False
            depth = max(0, depth - 1)
        elif depth == 1 and expecting_command:
            if token in ("prove", "prove-extract"):
                return True
            expecting_command = False
    return False


def complete_input_sha256(path: Path, cwd: Path, fact_directory: Path | None = None) -> str:
    """Hash the invocation-relative include/input closure, rejecting hidden proof work.

    Egglog resolves includes against its process directory, including nested
    includes. Use that same directory for hashing and execution, independent of
    the selected executable's checkout. Standalone fixtures retain their raw SHA.
    """
    dependencies: dict[str, str] = {}
    active: set[Path] = set()

    def visit(current: Path) -> None:
        if current in active:
            raise ValueError(f"cyclic workload include: {current}")
        active.add(current)
        source = current.read_text(encoding="utf-8")
        # Without quotes, every semicolon starts a comment. Otherwise retain
        # full tokenization, including string validation and escaped quotes.
        if '"' not in source:
            uncommented = re.sub(r";[^\n]*", "", source)
            if not any(word in uncommented for word in ("include", "input", "prove")):
                active.remove(current)
                return
        if file_contains_executable_prove_command(current):
            raise ValueError(f"{current} contains an explicit prove command")
        depth = 0
        command: list[str | None] = []
        for token in _egglog_tokens(source, strings=True):
            if token == "(":
                depth += 1
            elif token == ")":
                depth -= 1
                if depth == 0 and command and command[0] in ("include", "input"):
                    name = command[-1]
                    if not isinstance(name, str):
                        raise ValueError(f"invalid {command[0]} path in {current}")
                    base = fact_directory if command[0] == "input" and fact_directory is not None else cwd
                    dependency = (base / name).resolve()
                    identity = os.path.relpath(dependency, cwd)
                    if identity not in dependencies:
                        dependencies[identity] = sha256_file(dependency)
                        if command[0] == "include":
                            visit(dependency)
                if depth == 0:
                    command = []
            elif depth == 1:
                command.append(token)
        active.remove(current)

    if path.suffix == ".egg":
        visit(path)
    digest = sha256_file(path)
    if not dependencies:
        return digest
    closure = [digest, sorted(dependencies.items())]
    return "sha256:" + hashlib.sha256(json.dumps(closure, separators=(",", ":")).encode()).hexdigest()


def require_workload_unchanged(file_spec: FileSpec) -> None:
    """Reject an observation if its mutable inputs no longer match their cache identity."""

    try:
        file_sha256 = (
            complete_input_sha256(
                file_spec.absolute_path, file_spec.working_directory or Path.cwd(), file_spec.fact_directory
            )
            if file_spec.absolute_path.is_file()
            else None
        )
        if file_spec.fact_directory is None:
            fact_directory_sha256 = ""
        elif file_spec.fact_directory.is_dir():
            fact_directory_sha256 = sha256_directory(file_spec.fact_directory)
        else:
            fact_directory_sha256 = None
    except OSError as error:
        raise ValueError(f"workload changed during execution: {file_spec.display_path}") from error
    if file_sha256 != file_spec.sha256 or fact_directory_sha256 != file_spec.fact_directory_sha256:
        raise ValueError(f"workload changed during execution: {file_spec.display_path}")


def validate_workloads(files: Sequence[FileSpec]) -> None:
    """Validate cache identity and timing-boundary invariants for workloads."""

    validate_unique_file_identities(files)
    for file_spec in files:
        if file_spec.working_directory is None and file_contains_executable_prove_command(file_spec.absolute_path):
            raise ValueError(
                f"{file_spec.display_path} contains an explicit prove command; "
                "benchmark files should use check or extract so the selected treatment controls proof extraction"
            )
