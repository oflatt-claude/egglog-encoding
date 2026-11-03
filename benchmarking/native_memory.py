"""Configure optional allocator protection for local experiments.

Python supplies the cap through a CLI flag; Rust validates and installs it before
running the workload. Allocator settings must be in the environment before exec:
mimalloc can reserve memory before main, too early for CLI parsing or option setters.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence

NATIVE_LIMIT_BYTES = 10 * 1024**3
NATIVE_ALLOCATION_EXIT = 86
NATIVE_SETUP_EXIT = 87
NATIVE_ALLOCATOR_ENV = {
    "MIMALLOC_ARENA_RESERVE": "0",
    "MIMALLOC_DISALLOW_ARENA_ALLOC": "1",
    "MIMALLOC_RESERVE_OS_MEMORY": "0",
    "MIMALLOC_RESERVE_HUGE_OS_PAGES": "0",
}


def native_memory_command(
    command: Sequence[str], env: Mapping[str, str], limit_bytes: int | None = NATIVE_LIMIT_BYTES
) -> tuple[list[str], dict[str, str]]:
    """Pass explicit protection and the fixed startup policy before native exec.

    Controlled engines accept this option; unchanged author drivers do not.
    No cap or allocator-startup overrides are imposed when the limit is absent.
    Peak-memory measurement is owned by the caller and remains independent.
    """
    args = list(command)
    if limit_bytes is not None:
        args.insert(1, f"--memory-limit-bytes={limit_bytes}")
        return args, {**env, **NATIVE_ALLOCATOR_ENV}
    return args, dict(env)
