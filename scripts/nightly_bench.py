#!/usr/bin/env python3
"""Collect nightly benchmarks through bench.py and publish one shared report.

Each run replaces <output_dir>/index.jsonl and index.html. Slotted correctness
failures remain visible in the page; collection errors prevent publication.
"""

from __future__ import annotations

import argparse
import os
import shlex
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

type Target = tuple[str, str]

REPO_ROOT = Path(__file__).resolve().parents[1]
BENCH_SCRIPT = REPO_ROOT / "bench.py"
DEFAULT_OUTPUT_DIR = REPO_ROOT / "nightly" / "output"
CARGO_BIN_DIR = Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo") / "bin"
BRANCH: Target = ("branch", ".")
TARGETS: tuple[Target, ...] = (BRANCH, ("main", "@origin/main"))
TREATMENTS = ("term", "proofs", "proof-extraction")


def _bench_env() -> dict[str, str]:
    """Use rustup's pinned toolchain and suppress browser launch on the nightly host."""
    shims = str(CARGO_BIN_DIR)
    path = [entry for entry in os.environ.get("PATH", "").split(os.pathsep) if entry != shims]
    return {**os.environ, "PATH": os.pathsep.join([shims, *path]), "BROWSER": "true"}


def _run(args: Sequence[str]) -> int:
    command = [sys.executable, str(BENCH_SCRIPT), *args]
    print(f"nightly: {shlex.join(command)}", file=sys.stderr)
    return subprocess.run(command, cwd=REPO_ROOT, env=_bench_env(), check=False).returncode


def _comparison(target: Target, treatment: str) -> list[str]:
    label, source = target
    # The CLI defaults the baseline checkout to the candidate checkout.
    return ["--target", f"{label}={source}", "--treatment", treatment, "--compare-treatment", "off"]


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("output_dir", nargs="?", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--rounds", type=_positive_int, help="samples per proof endpoint/file")
    parser.add_argument("--slotted-timeout", type=_positive_int, default=150, help="seconds per slotted process")
    parser.add_argument("--slotted-jobs", type=_positive_int, default=1, help="concurrent slotted workloads")
    args = parser.parse_args(argv)
    output_dir = args.output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    report, page = output_dir / "index.jsonl", output_dir / "index.html"
    for path in (report, page):
        path.unlink(missing_ok=True)
    common = ["--report", str(report), "--detail", "files"]
    if args.rounds is not None:
        common += ["--rounds", str(args.rounds)]

    for target in TARGETS:
        for treatment in TREATMENTS:
            if _run([*_comparison(target, treatment), *common]):
                print(f"nightly: skipped {target[0]} {treatment}", file=sys.stderr)

    status = _run(
        [
            "slotted",
            "--timeout",
            str(args.slotted_timeout),
            "--jobs",
            str(args.slotted_jobs),
            "--params",
            "0",
            "1",
            "2",
            "3",
            "--report",
            str(report),
        ]
    )
    if status not in (0, 1):
        print("nightly: slotted collection failed", file=sys.stderr)
        return 1
    if status:
        print("nightly: slotted comparisons are incomplete or failed; see the report's error banner", file=sys.stderr)

    if _run([*_comparison(BRANCH, "proofs"), *common, "--open"]) or not page.is_file():
        print("nightly: benchmark did not produce a report", file=sys.stderr)
        return 1
    print(f"nightly: wrote report to {page}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
