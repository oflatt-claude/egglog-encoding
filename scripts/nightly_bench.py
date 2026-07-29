#!/usr/bin/env python3
"""Generate the egglog-encoding nightly benchmark webpage.

Runs the public benchmark entrypoint (``bench.py``) once per backend/treatment
endpoint, on the current checkout and on the latest ``main``, accumulating every
endpoint in the ordinary report cache. eval-live's interactive report discovers
its dropdown from every cached endpoint, so the page can compare any two of
them — including branch against main. Each endpoint is labelled by target
(``branch`` / ``main``) and commit hash, so it is clear which commit each side
is.

The last run writes the page, opening on proof overhead of the current
checkout. Its cache and page are copied to ``nightly/output/`` only after that
run succeeds, so a failed run leaves the previously published page in place.

The egraphs-good nightly service (``nightly.cs.washington.edu``) checks out this
repository, runs ``make nightly``, and serves that directory, matching
``report=`` in the nightly configuration.

``--no-publish`` leaves that directory alone and reports the page where the run
already wrote it, for trying the nightly out locally; ``--branch-only``,
``--rounds`` and file arguments cut a local run down to something quick.
``make nightly-local`` is all four together.
"""

from __future__ import annotations

import argparse
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

# Every endpoint bench.py can run: dd runs only term and proofs, and
# proof-extraction is main-only.
#
# The dd endpoints are commented out while the proof encoding is reworked. Put
# them back when it lands.
ENDPOINTS: tuple[Endpoint, ...] = (
    ("main", "term"),
    ("main", "proofs"),
    ("main", "proof-extraction"),
    # ("dd", "term"),
    # ("dd", "proofs"),
)

# Every endpoint is measured against ordinary mode on its own checkout, so the
# page opens on proof overhead of the branch.
BASELINE: Endpoint = ("main", "off")
HEADLINE: Endpoint = ("main", "proofs")


def _run(
    target: Target,
    endpoint: Endpoint,
    *,
    open_report: bool,
    rounds: int | None = None,
    files: Sequence[str] = (),
) -> int:
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
        *files,
    ]
    print(f"nightly: {' '.join(shlex.quote(part) for part in command)}", file=sys.stderr)
    # Keep the headless nightly host from launching bench.py's best-effort browser.
    env = {**os.environ, "BROWSER": "true"}
    return subprocess.run(command, cwd=REPO_ROOT, env=env, check=False).returncode


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
        "--no-publish",
        action="store_true",
        help="leave the output directory alone; report the page where the run wrote it",
    )
    parser.add_argument(
        "--branch-only",
        action="store_true",
        help="measure only this checkout, skipping the build of origin/main",
    )
    parser.add_argument("--rounds", type=int, help="rounds per endpoint/file, passed to bench.py")
    # A flag rather than a second positional, which argparse would fill from
    # `output_dir` first.
    parser.add_argument(
        "--files",
        nargs="+",
        default=(),
        metavar="FILE",
        help="egglog files to benchmark, in place of bench.py's default set",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    output_dir = args.output_dir.expanduser().resolve()
    targets = (BRANCH,) if args.branch_only else TARGETS
    passthrough = {"rounds": args.rounds, "files": tuple(args.files)}

    # Populate the dropdown with every endpoint. A combination that fails to
    # build or run drops one option instead of failing the whole nightly.
    for target in targets:
        for endpoint in ENDPOINTS:
            if _run(target, endpoint, open_report=False, **passthrough) != 0:
                print(f"nightly: skipped {target[0]} {endpoint[0]}/{endpoint[1]}", file=sys.stderr)

    # The whole cache is now populated, so this last run re-renders it as the
    # page. Its rows are already cached, so it only rebuilds the report.
    if _run(BRANCH, HEADLINE, open_report=True, **passthrough) != 0 or not PAGE_PATH.is_file():
        print("nightly: benchmark did not produce a report", file=sys.stderr)
        return 1
    if args.no_publish:
        print(f"nightly: report at {PAGE_PATH} (not published)", file=sys.stderr)
        return 0
    output_dir.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(PAGE_PATH, output_dir / "index.html")
    shutil.copyfile(REPORT_PATH, output_dir / "index.jsonl")
    print(f"nightly: wrote report to {output_dir / 'index.html'}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
