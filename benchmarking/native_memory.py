"""Configure optional allocator protection for local experiments.

Python supplies the cap through a CLI flag; Rust validates and installs it before
running the workload. Allocator settings must be in the environment before exec:
mimalloc can reserve memory before main, too early for CLI parsing or option setters.
"""

from __future__ import annotations

import argparse
from collections.abc import Mapping, Sequence

from .config import DEFAULT_MEMORY_LIMIT_BYTES as NATIVE_LIMIT_BYTES

NATIVE_ALLOCATION_EXIT = 86
NATIVE_SETUP_EXIT = 87
NATIVE_ALLOCATOR_ENV = {
    "MIMALLOC_ARENA_RESERVE": "0",
    "MIMALLOC_DISALLOW_ARENA_ALLOC": "1",
    "MIMALLOC_RESERVE_OS_MEMORY": "0",
    "MIMALLOC_RESERVE_HUGE_OS_PAGES": "0",
}


def add_memory_limit_options(parser: argparse.ArgumentParser, *, default: int | None) -> None:
    """Keep explicit bounds and the capped/uncapped choice consistent across CLIs."""

    def positive_bytes(value: str) -> int:
        limit = int(value)
        if limit < 1:
            raise argparse.ArgumentTypeError("memory limit must be positive")
        return limit

    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        "--memory-limit",
        action="store_const",
        const=NATIVE_LIMIT_BYTES,
        dest="memory_limit_bytes",
        help=f"apply the configured local allocator cap ({NATIVE_LIMIT_BYTES} bytes)",
    )
    group.add_argument(
        "--memory-limit-bytes",
        type=positive_bytes,
        dest="memory_limit_bytes",
        metavar="BYTES",
        help="apply a custom local allocator cap",
    )
    group.add_argument("--no-memory-limit", action="store_const", const=None, dest="memory_limit_bytes")
    parser.set_defaults(memory_limit_bytes=default)


def native_memory_command(
    command: Sequence[str], env: Mapping[str, str], limit_bytes: int | None = NATIVE_LIMIT_BYTES
) -> tuple[list[str], dict[str, str]]:
    """Pass explicit protection and the fixed startup policy before native exec.

    Controlled engines accept this option; unchanged author drivers do not.
    Allocator startup is fixed in capped and uncapped runs; the bound is only a guard.
    Peak-memory measurement is owned by the caller and remains independent.
    """
    args = list(command)
    if limit_bytes is not None:
        args.insert(1, f"--memory-limit-bytes={limit_bytes}")
    return args, {**env, **NATIVE_ALLOCATOR_ENV}
