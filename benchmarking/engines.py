"""Describe benchmark treatments and engine-specific workload commands."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Protocol

type BinaryName = Literal[
    "egglog-experimental", "egg-math-benchmark", "egg-de", "egg-ee", "egg-nee", "egg-oee", "slotted-reference"
]
type Treatment = Literal[
    "off",
    "term",
    "proofs",
    "proof-extraction",
    "proof-testing",
    "egg",
    "egg-proofs",
    "egg-proof-extraction",
    "egg-proof-testing",
    "egg-de",
    "egg-ee",
    "egg-nee",
    "egg-oee",
    "slotted",
    "slotted-no-aliasing",
    "slotted-ref-multi",
    "slotted-ref-nested",
    "slotted-ref-nested-snapshot",
]


class WorkloadFile(Protocol):
    @property
    def display_path(self) -> str: ...

    @property
    def absolute_path(self) -> Path: ...

    @property
    def fact_directory(self) -> Path | None: ...


PARAMETER_BINARIES: tuple[BinaryName, ...] = ("egg-de", "egg-ee", "egg-nee", "egg-oee")


@dataclass(frozen=True)
class BinarySpec:
    """One buildable executable and the protocol it implements."""

    input_suffix: str
    build_args: tuple[str, ...]
    timing_summary: bool = True
    allocator_limit: bool = True
    target_directory: str | None = None


BINARIES: dict[BinaryName, BinarySpec] = {
    "egglog-experimental": BinarySpec(
        ".egg",
        (
            "--locked",
            "-p",
            "egglog-experimental",
            "--no-default-features",
            "--features",
            "bin",
            "--bin",
            "egglog-experimental",
        ),
    ),
    "egg-math-benchmark": BinarySpec(".egg", ("-p", "egg-math-benchmark")),
    "slotted-reference": BinarySpec(
        ".ref",
        ("--locked", "-p", "slotted-reference", "--no-default-features", "--bin", "slotted-reference"),
        timing_summary=False,
    ),
    **{
        name: BinarySpec(
            ".in",
            ("--locked", "--manifest-path", "benchmarks/disequality/native/Cargo.toml", "--bin", name),
            timing_summary=False,
            allocator_limit=False,
            target_directory="benchmarks/local/parameter-native/target",
        )
        for name in PARAMETER_BINARIES
    },
}


@dataclass(frozen=True)
class TreatmentSpec:
    """A public experiment name: one executable plus its mode flags."""

    binary_name: BinaryName
    flags: tuple[str, ...]


TREATMENT_SPECS: dict[Treatment, TreatmentSpec] = {
    "off": TreatmentSpec("egglog-experimental", ()),
    "term": TreatmentSpec("egglog-experimental", ("--term-encoding",)),
    "proofs": TreatmentSpec("egglog-experimental", ("--proofs",)),
    "proof-extraction": TreatmentSpec("egglog-experimental", ("--proof-extraction",)),
    "proof-testing": TreatmentSpec("egglog-experimental", ("--proof-testing",)),
    "egg": TreatmentSpec("egg-math-benchmark", ("--proof-mode", "off")),
    "egg-proofs": TreatmentSpec("egg-math-benchmark", ("--proof-mode", "enabled")),
    "egg-proof-extraction": TreatmentSpec("egg-math-benchmark", ("--proof-mode", "extract")),
    "egg-proof-testing": TreatmentSpec("egg-math-benchmark", ("--proof-mode", "check")),
    "egg-de": TreatmentSpec("egg-de", ()),
    "egg-ee": TreatmentSpec("egg-ee", ()),
    "egg-nee": TreatmentSpec("egg-nee", ()),
    "egg-oee": TreatmentSpec("egg-oee", ()),
    "slotted": TreatmentSpec("egglog-experimental", ("--slotted",)),
    "slotted-no-aliasing": TreatmentSpec("egglog-experimental", ("--slotted", "--slotted-no-aliasing")),
    "slotted-ref-multi": TreatmentSpec("slotted-reference", ("--matcher", "multi", "--substitution", "snapshot")),
    "slotted-ref-nested": TreatmentSpec("slotted-reference", ("--matcher", "nested", "--substitution", "syntactic")),
    "slotted-ref-nested-snapshot": TreatmentSpec(
        "slotted-reference", ("--matcher", "nested", "--substitution", "snapshot")
    ),
}
TREATMENTS = tuple(TREATMENT_SPECS)
EGGLOG_FLAGS = ("--mode", "no-messages", "-j", "1")
PROCESS_ENV = {"RUST_LOG": "error"}
NATIVE_PARAMETER_ARGUMENTS = ("100000", "10000")

MATH_WORKLOAD_PATH = Path("egglog-experimental/tests/math-microbenchmark-rational.egg")
MATH_WORKLOAD_SHA256 = "sha256:29e120079c588d0bf079891b393ae041ec4e1a45d369114cde3754e5c6b7878f"
# The frozen round-twelve distribution witness uses operands from the unchanged
# integration-by-parts closure; its complete input identity fixes both endpoints.
MATH12_WORKLOAD_PATH = Path("benchmarks/corpus/math/math-iteration-12.egg")
MATH12_WORKLOAD_SHA256 = "sha256:fde0b4a62c8d5904014babd00dfce11fcab429fa26125280ccd4515f9dd6915f"
MATH_WORKLOAD_ARGUMENTS: dict[str, tuple[str, ...]] = {
    MATH_WORKLOAD_SHA256: (),
    MATH12_WORKLOAD_SHA256: ("--math12",),
}
PARAMETER_WORKLOAD_PATH = Path("benchmarks/disequality/parameter-analysis.egg")


def math_workload_arguments(file_spec: WorkloadFile) -> tuple[str, ...]:
    """Derive the exact native schedule and witness from registered complete input bytes."""
    actual = "sha256:" + hashlib.sha256(file_spec.absolute_path.read_bytes()).hexdigest()
    try:
        return MATH_WORKLOAD_ARGUMENTS[actual]
    except KeyError:
        raise ValueError(
            "native egg only supports registered Math workloads (fixed Math11 and Math12); "
            f"cannot run {file_spec.display_path}"
        ) from None


def validate_binary_workload(file_spec: WorkloadFile, treatment: Treatment) -> None:
    """Reject workload features unsupported by the selected treatment engine."""

    binary_name = TREATMENT_SPECS[treatment].binary_name
    if binary_name == "egglog-experimental":
        if treatment == "slotted-no-aliasing":
            reference = file_spec.absolute_path.with_suffix(".ref")
            if reference.is_file():
                frozen = json.loads(reference.read_text())
                if frozen["nested"] is None:
                    raise ValueError(frozen["unsupported_reason"])
        return
    if file_spec.fact_directory is not None:
        raise ValueError(f"treatment {treatment} does not support --fact-directory")
    if binary_name == "slotted-reference":
        if file_spec.absolute_path.suffix != ".ref":
            raise ValueError(f"treatment {treatment} requires a frozen slotted .ref workload")
        frozen = json.loads(file_spec.absolute_path.read_text())
        matcher = "multi" if treatment == "slotted-ref-multi" else "nested"
        if frozen[matcher] is None:
            raise ValueError(frozen["unsupported_reason"])
        return
    if binary_name != "egg-math-benchmark":
        if file_spec.absolute_path.suffix != ".in":
            raise ValueError(f"treatment {treatment} requires a native .in workload")
        return
    math_workload_arguments(file_spec)
