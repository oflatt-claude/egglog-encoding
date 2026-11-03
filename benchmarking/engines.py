"""Describe benchmark treatments and engine-specific workload commands."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Protocol

from .native_memory import NATIVE_ALLOCATOR_ENV

type Engine = Literal["egglog", "egg", "egg-de", "egg-ee", "egg-nee", "egg-oee", "slotted"]
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


@dataclass(frozen=True)
class TreatmentSpec:
    engine: Engine
    flags: tuple[str, ...]
    timing_summary: bool = True
    allocator_limit: bool = True


TREATMENT_SPECS: dict[Treatment, TreatmentSpec] = {
    "off": TreatmentSpec("egglog", ()),
    "term": TreatmentSpec("egglog", ("--term-encoding",)),
    "proofs": TreatmentSpec("egglog", ("--proofs",)),
    "proof-extraction": TreatmentSpec("egglog", ("--proof-extraction",)),
    "proof-testing": TreatmentSpec("egglog", ("--proof-testing",)),
    "egg": TreatmentSpec("egg", ("--proof-mode", "off")),
    "egg-proofs": TreatmentSpec("egg", ("--proof-mode", "enabled")),
    "egg-proof-extraction": TreatmentSpec("egg", ("--proof-mode", "extract")),
    "egg-proof-testing": TreatmentSpec("egg", ("--proof-mode", "check")),
    "egg-de": TreatmentSpec("egg-de", (), timing_summary=False, allocator_limit=False),
    "egg-ee": TreatmentSpec("egg-ee", (), timing_summary=False, allocator_limit=False),
    "egg-nee": TreatmentSpec("egg-nee", (), timing_summary=False, allocator_limit=False),
    "egg-oee": TreatmentSpec("egg-oee", (), timing_summary=False, allocator_limit=False),
    "slotted": TreatmentSpec("egglog", ("--slotted",)),
    "slotted-no-aliasing": TreatmentSpec("egglog", ("--slotted", "--slotted-no-aliasing")),
    "slotted-ref-multi": TreatmentSpec(
        "slotted", ("--matcher", "multi", "--substitution", "snapshot"), timing_summary=False
    ),
    "slotted-ref-nested": TreatmentSpec(
        "slotted", ("--matcher", "nested", "--substitution", "syntactic"), timing_summary=False
    ),
    "slotted-ref-nested-snapshot": TreatmentSpec(
        "slotted", ("--matcher", "nested", "--substitution", "snapshot"), timing_summary=False
    ),
}
TREATMENTS = tuple(TREATMENT_SPECS)
ENGINE_INPUT_SUFFIXES: dict[Engine, str] = {
    "egglog": ".egg",
    "egg": ".egg",
    "egg-de": ".in",
    "egg-ee": ".in",
    "egg-nee": ".in",
    "egg-oee": ".in",
    "slotted": ".ref",
}
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


def execution_settings_sha256(
    treatment: Treatment, file_sha256: str, disequality_encoding: str, memory_limit_bytes: int | None
) -> str:
    """Invalidate observations when resolved driver flags or allocator settings change."""
    spec = TREATMENT_SPECS[treatment]
    settings = {
        "flags": spec.flags,
        "engine": spec.engine,
        "timing_summary": spec.timing_summary,
        "disequality_encoding": disequality_encoding,
        "memory_limit_bytes": memory_limit_bytes,
        "environment": PROCESS_ENV,
        "allocator_environment": NATIVE_ALLOCATOR_ENV if memory_limit_bytes is not None else {},
        "driver_arguments": (
            EGGLOG_FLAGS
            if spec.engine == "egglog"
            else MATH_WORKLOAD_ARGUMENTS.get(file_sha256, ())
            if spec.engine == "egg"
            else NATIVE_PARAMETER_ARGUMENTS
            if spec.engine.startswith("egg-")
            else ()
        ),
    }
    return "sha256:" + hashlib.sha256(json.dumps(settings, sort_keys=True).encode()).hexdigest()


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


def validate_engine_workload(file_spec: WorkloadFile, treatment: Treatment) -> None:
    """Reject workload features unsupported by the selected treatment engine."""

    engine = TREATMENT_SPECS[treatment].engine
    if engine == "egglog":
        if treatment == "slotted-no-aliasing":
            reference = file_spec.absolute_path.with_suffix(".ref")
            if reference.is_file():
                frozen = json.loads(reference.read_text())
                if frozen["nested"] is None:
                    raise ValueError(frozen["unsupported_reason"])
        return
    if file_spec.fact_directory is not None:
        raise ValueError(f"treatment {treatment} does not support --fact-directory")
    if engine == "slotted":
        if file_spec.absolute_path.suffix != ".ref":
            raise ValueError(f"treatment {treatment} requires a frozen slotted .ref workload")
        frozen = json.loads(file_spec.absolute_path.read_text())
        matcher = "multi" if treatment == "slotted-ref-multi" else "nested"
        if frozen[matcher] is None:
            raise ValueError(frozen["unsupported_reason"])
        return
    if engine != "egg":
        if file_spec.absolute_path.suffix != ".in":
            raise ValueError(f"treatment {treatment} requires a native .in workload")
        return
    math_workload_arguments(file_spec)
