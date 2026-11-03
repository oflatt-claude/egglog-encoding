"""Define dependency-free benchmark identities and invariants.

This module owns endpoint selection, comparison scope, and the uniqueness rules
required by cache-backed statistics. Feature-local requests, subprocess
outcomes, persisted records, and derived report rows live beside their owners.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from .engines import BINARIES, TREATMENT_SPECS, BinaryName, Treatment
from .native_memory import NATIVE_LIMIT_BYTES

Status = Literal["success", "timed-out", "failure"]
DisequalityEncoding = Literal["nee", "ee"]
DetailLevel = Literal["summary", "files", "phases", "rulesets"]
ExclusionKind = Literal["resource", "unsupported", "expected-failure"]


@dataclass(frozen=True)
class TargetRow:
    source: str
    path: str
    git_ref: str
    git_sha: str
    is_dirty: bool
    label: str | None = None


@dataclass(frozen=True)
class Exclusion:
    """A reviewed configuration exclusion, attached to its matched logical input."""

    kind: ExclusionKind
    reason: str
    evidence: str
    treatments: tuple[Treatment, ...] = ()
    disequality_encoding: DisequalityEncoding | None = None
    memory_limit_bytes: int | None = None


@dataclass(frozen=True)
class FileSpec:
    display_path: str
    absolute_path: Path
    sha256: str
    fact_directory: Path | None = None
    fact_directory_sha256: str = ""
    binary_inputs: tuple[tuple[BinaryName, FileSpec], ...] = ()
    exclusions: tuple[Exclusion, ...] = ()

    def exclusion_for(
        self,
        treatment: Treatment,
        encoding: DisequalityEncoding = "nee",
        *,
        memory_limit_bytes: int | None,
    ) -> Exclusion | None:
        """Apply both selectors so testing and reports exclude the same configuration."""
        matched = None
        for rule in self.exclusions:
            if rule.treatments and treatment not in rule.treatments:
                continue
            if rule.disequality_encoding is not None and rule.disequality_encoding != encoding:
                continue
            if rule.memory_limit_bytes is not None and (
                memory_limit_bytes is None or memory_limit_bytes > rule.memory_limit_bytes
            ):
                continue
            if matched is not None:
                raise ValueError(f"overlapping benchmark exclusions for {self.display_path}/{treatment}")
            matched = rule
        return matched

    def for_binary(self, binary_name: BinaryName) -> FileSpec:
        """Resolve an engine's physical representation of this logical workload."""

        for input_engine, file in self.binary_inputs:
            if input_engine == binary_name:
                return file
        return self


def validate_unique_file_identities(files: Sequence[FileSpec]) -> None:
    """Reject workloads that would select the same cached observations."""

    by_identity: dict[tuple[str, str], FileSpec] = {}
    for file in files:
        identity = (file.sha256, file.fact_directory_sha256)
        previous = by_identity.get(identity)
        if previous is not None:
            raise ValueError(
                f"benchmark files {previous.display_path!r} and {file.display_path!r} have identical "
                "file and fact-directory hashes; select each workload only once"
            )
        by_identity[identity] = file


@dataclass(frozen=True)
class TargetRequest:
    raw: str
    source: str
    label: str | None

    @property
    def is_label_lookup(self) -> bool:
        return self.label is not None and self.source == ""


@dataclass(frozen=True)
class BuiltBinary:
    binary_name: BinaryName
    sha256: str
    path: Path | None


@dataclass(frozen=True)
class ResolvedTarget:
    request: TargetRequest
    row: TargetRow
    binary_sha256: str
    binary_path: Path | None
    binaries: tuple[BuiltBinary, ...] = ()
    primary_binary: BinaryName | None = None

    def binary_sha256_for(self, treatment: Treatment) -> str:
        binary_name = TREATMENT_SPECS[treatment].binary_name
        for binary in self.binaries:
            if binary.binary_name == binary_name:
                return binary.sha256
        if binary_name == "egglog-experimental" and self.primary_binary in (None, "egglog-experimental"):
            return self.binary_sha256
        raise ValueError(f"target {self.display_label} has no {binary_name} binary")

    def binary_path_for(self, treatment: Treatment) -> Path | None:
        binary_name = TREATMENT_SPECS[treatment].binary_name
        for binary in self.binaries:
            if binary.binary_name == binary_name:
                return binary.path
        if binary_name == "egglog-experimental" and self.primary_binary in (None, "egglog-experimental"):
            return self.binary_path
        raise ValueError(f"target {self.display_label} has no {binary_name} binary")

    @property
    def display_label(self) -> str:
        if self.row.label:
            return self.row.label
        if self.row.git_ref != "HEAD":
            return self.row.git_ref
        if self.row.git_sha:
            return self.row.git_sha[:12]
        return Path(self.row.path).name


@dataclass(frozen=True)
class EndpointRequest:
    """One unresolved target/treatment selected by the CLI."""

    target: TargetRequest
    treatment: Treatment
    disequality_encoding: DisequalityEncoding = "nee"
    memory_limit_bytes: int | None = NATIVE_LIMIT_BYTES

    def __post_init__(self) -> None:
        if TREATMENT_SPECS[self.treatment].binary_name != "egglog-experimental" and self.disequality_encoding != "nee":
            raise ValueError("disequality encoding selection is only supported by egglog treatments")
        if not BINARIES[TREATMENT_SPECS[self.treatment].binary_name].allocator_limit:
            object.__setattr__(self, "memory_limit_bytes", None)
        if self.memory_limit_bytes is not None and self.memory_limit_bytes < 1:
            raise ValueError("allocator memory limit must be positive")


@dataclass(frozen=True)
class BenchmarkEndpoint:
    """One resolved target/treatment addressed by benchmark cache rows."""

    target: ResolvedTarget
    treatment: Treatment
    disequality_encoding: DisequalityEncoding = "nee"
    memory_limit_bytes: int | None = NATIVE_LIMIT_BYTES

    def __post_init__(self) -> None:
        if not BINARIES[TREATMENT_SPECS[self.treatment].binary_name].allocator_limit:
            object.__setattr__(self, "memory_limit_bytes", None)

    @property
    def cache_identity(self) -> tuple[str, Treatment, DisequalityEncoding, bool]:
        """Return the endpoint coordinates shared by all of its file keys."""

        return (
            self.target.binary_sha256_for(self.treatment),
            self.treatment,
            self.disequality_encoding,
            self.memory_limit_bytes is not None,
        )


@dataclass(frozen=True)
class ComparisonSpec:
    """The exact baseline/candidate pair and workloads selected for one report."""

    baseline: BenchmarkEndpoint
    candidate: BenchmarkEndpoint
    files: tuple[FileSpec, ...]
    rounds: int
    timeout_sec: int

    def __post_init__(self) -> None:
        if not self.files:
            raise ValueError("benchmark comparison requires at least one file")
        validate_unique_file_identities(self.files)
        for endpoint in (self.baseline, self.candidate):
            binary_name = TREATMENT_SPECS[endpoint.treatment].binary_name
            validate_unique_file_identities(tuple(file.for_binary(binary_name) for file in self.files))
        if self.rounds < 1:
            raise ValueError("benchmark rounds must be positive")
        if self.timeout_sec < 1:
            raise ValueError("benchmark timeout must be positive")
        if self.baseline.cache_identity == self.candidate.cache_identity:
            raise ValueError("baseline and candidate endpoints must be different")
