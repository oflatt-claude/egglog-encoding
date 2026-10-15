#!/usr/bin/env python3
"""Generate the egglog-encoding nightly benchmark webpage.

Runs the public benchmark entrypoint (``bench.py``) once per backend/treatment
endpoint, on the current checkout and on the latest ``main``, accumulating every
endpoint in the ordinary report cache. eval-live's interactive report discovers
its dropdown from every cached endpoint, so the page can compare any two of
them — including branch against main. Each endpoint is labelled by target
(``branch`` / ``main``) and commit hash, so it is clear which commit each side
is.

The page includes proof comparisons and slotted timing tables. Slotted runs use
the paper's rewrite budgets and check graph equivalence against the reference
matchers. Failed or incomplete comparisons appear in the report. Collection
errors leave the published report untouched.

The egraphs-good nightly service (``nightly.cs.washington.edu``) checks out this
repository, runs ``make nightly``, and serves that directory, matching
``report=`` in the nightly configuration.

``nightly/output/`` is git-ignored, so this runs the same way locally as it does
on the host. ``make nightly-local`` is that run at ``--rounds 1``.
"""

from __future__ import annotations

import argparse
import importlib
import os
import shlex
import shutil
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

type Target = tuple[str, str]  # (label, source) for bench.py's label=source syntax
type Endpoint = tuple[str, str]  # (backend, treatment)

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))
BENCH_SCRIPT = REPO_ROOT / "bench.py"
DEFAULT_OUTPUT_DIR = REPO_ROOT / "nightly" / "output"

# bench.py's default report cache, shared with every other local invocation, and
# the page --open derives from it.
REPORT_PATH = REPO_ROOT / ".reports.jsonl"
PAGE_PATH = REPO_ROOT / ".reports.html"

# Checkouts to measure, each with a stable label so the dropdown shows which
# commit an endpoint belongs to. Endpoint identity is (binary, backend,
# treatment), so a branch matching main byte-for-byte collapses to one endpoint
# per config; the two diverge once the code differs.
BRANCH: Target = ("branch", ".")
TARGETS: tuple[Target, ...] = (BRANCH, ("main", "@origin/main"))

# Endpoints to measure on the main backend.
ENDPOINTS: tuple[Endpoint, ...] = (
    ("main", "term"),
    ("main", "proofs"),
    ("main", "proof-extraction"),
)

# Every endpoint is measured against ordinary mode on its own checkout, so the
# page opens on proof overhead of the branch.
BASELINE: Endpoint = ("main", "off")
HEADLINE: Endpoint = ("main", "proofs")

# The nightly host leaves rustup's shim directory off PATH, so cargo resolves to
# Ubuntu's, which predates rust-toolchain.toml's pin; only rustup honours that
# pin. Putting the shims first makes cargo fetch the pinned toolchain. `CARGO_HOME`
# follows the Makefile's CARGO_HOME_DIR, which is where it installs rustup.
CARGO_BIN_DIR = Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo") / "bin"


def _bench_env() -> dict[str, str]:
    """bench.py's environment: rustup's cargo first, and no browser launch."""

    # Prepend unconditionally: already being *somewhere* on PATH is not enough,
    # since a directory holding a distro cargo can precede it and still win.
    shims = str(CARGO_BIN_DIR)
    path = [entry for entry in os.environ.get("PATH", "").split(os.pathsep) if entry != shims]
    path.insert(0, shims)
    # Keep the headless nightly host from launching bench.py's best-effort browser.
    return {**os.environ, "PATH": os.pathsep.join(path), "BROWSER": "true"}


def _run(target: Target, endpoint: Endpoint, *, open_report: bool, rounds: int | None) -> int:
    """Benchmark one endpoint against the baseline on the same checkout."""

    label, source = target
    backend, treatment = endpoint
    baseline_backend, baseline_treatment = BASELINE
    command = [
        sys.executable,
        str(BENCH_SCRIPT),
        "--target",
        f"{label}={source}",
        "--backend",
        backend,
        "--treatment",
        treatment,
        "--compare-target",
        f"{label}={source}",
        "--compare-backend",
        baseline_backend,
        "--compare-treatment",
        baseline_treatment,
        # Per-file tables make a long run's progress legible.
        "--detail",
        "files",
        *(["--rounds", str(rounds)] if rounds is not None else []),
        *(["--open"] if open_report else []),
    ]
    print(f"nightly: {' '.join(shlex.quote(part) for part in command)}", file=sys.stderr)
    return subprocess.run(command, cwd=REPO_ROOT, env=_bench_env(), check=False).returncode


def _positive_int(value: str) -> int:
    """Parse a positive integer command-line argument."""

    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def _run_slotted(*, timeout: int, jobs: int) -> int:
    """Collect slotted timings and reference comparison results."""
    evaluator = importlib.import_module("slotted.slotted-eval")
    return int(evaluator.nightly(REPORT_PATH, env=_bench_env(), timeout=timeout, jobs=jobs))


def main(argv: Sequence[str] | None = None) -> int:
    """Populate the endpoint cache and publish ``<output_dir>/index.html``."""

    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "output_dir",
        nargs="?",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="directory to publish index.html and index.jsonl into",
    )
    parser.add_argument(
        "--rounds",
        type=_positive_int,
        help="rounds per endpoint/file, passed to bench.py",
    )
    parser.add_argument(
        "--slotted-timeout",
        type=_positive_int,
        default=150,
        help="seconds per slotted benchmark process (default: 150)",
    )
    parser.add_argument(
        "--slotted-jobs",
        type=_positive_int,
        default=1,
        help="concurrent slotted workloads; values above 1 contend for resources",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    output_dir = args.output_dir.expanduser().resolve()

    # Populate the dropdown with every endpoint. A combination that fails to
    # build or run drops one option instead of failing the whole nightly.
    for target in TARGETS:
        for endpoint in ENDPOINTS:
            if _run(target, endpoint, open_report=False, rounds=args.rounds) != 0:
                print(f"nightly: skipped {target[0]} {endpoint[0]}/{endpoint[1]}", file=sys.stderr)

    try:
        status = _run_slotted(timeout=args.slotted_timeout, jobs=args.slotted_jobs)
    except (OSError, SystemExit, ValueError) as error:
        print(f"nightly: slotted collection failed: {error}", file=sys.stderr)
        return 1
    if status:
        print("nightly: slotted comparisons are incomplete or failed; see the report's error banner", file=sys.stderr)

    # Finish collection before rendering so the page includes every result.
    if _run(BRANCH, HEADLINE, open_report=True, rounds=args.rounds) != 0 or not PAGE_PATH.is_file():
        print("nightly: benchmark did not produce a report", file=sys.stderr)
        return 1
    output_dir.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(REPORT_PATH, output_dir / "index.jsonl")
    shutil.copyfile(PAGE_PATH, output_dir / "index.html")
    print(f"nightly: wrote report to {output_dir / 'index.html'}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
