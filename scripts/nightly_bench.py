#!/usr/bin/env python3
"""Generate the egglog-encoding nightly benchmark webpage.

Runs the public benchmark entrypoint (``bench.py``) once per backend/treatment
endpoint, on the current checkout and on the latest ``main``, accumulating every
endpoint in the ordinary report cache. eval-live's interactive report discovers
its dropdown from every cached endpoint, so the page can compare any two of
them — including branch against main. Each endpoint is labelled by target
(``branch`` / ``main``) and commit hash, so it is clear which commit each side
is.

The last proof run writes the interactive page, opening on proof overhead of the
current checkout. The Python slotted evaluator then collects its reference
comparisons, retaining the paper's rewrite budgets. Its two timing tables and full
report are embedded beneath the proof report and published as standalone HTML,
Markdown and JSONL files. Comparison failures remain visible in the report's error
banner; failure to produce the artifacts preserves the previous publication.

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
import tempfile
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

# Endpoints to measure, all on the main backend: proof-extraction is main-only,
# and the differential-dataflow backend's endpoints — ("dd", "term") and
# ("dd", "proofs") — are disabled for now. Re-add them here to measure dd again.
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
    """Parse ``--rounds``, which bench.py also requires to be positive."""

    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def _run_slotted(directory: Path, *, timeout: int, jobs: int) -> int:
    """Use the same collector and correctness gates as the public slotted CLI."""
    evaluator = importlib.import_module("slotted.slotted-eval")
    return int(evaluator.nightly(directory, env=_bench_env(), timeout=timeout, jobs=jobs))


def _with_slotted_report(page: str) -> str:
    """Keep the interactive proof report intact and embed the slotted tables."""
    section = """
<section id="slotted-report" style="margin:2rem">
  <h1>Slotted e-graphs — current checkout</h1>
  <p><a href="slotted.html">Open full report</a> ·
     <a href="slotted.md">Markdown</a> · <a href="slotted.jsonl">Measurements</a></p>
  <iframe src="slotted.html" title="Slotted e-graph benchmark tables"
          style="width:100%;height:70rem;border:0"></iframe>
</section>
"""
    navigation = '<nav style="margin:1rem 2rem"><a href="#slotted-report">Slotted e-graph benchmarks</a></nav>'
    # The bundled JavaScript also contains a literal "</body>". Insert at the
    # document's final closing tag without changing those embedded strings.
    body, tail = page.rsplit("</body>", 1)
    return body.replace("<body>", "<body>" + navigation, 1) + section + "</body>" + tail


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
        default=300,
        help="seconds per slotted benchmark process (default: 300)",
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

    # The whole cache is now populated, so this last run re-renders it as the
    # page. Its rows are already cached, so it only rebuilds the report.
    if _run(BRANCH, HEADLINE, open_report=True, rounds=args.rounds) != 0 or not PAGE_PATH.is_file():
        print("nightly: benchmark did not produce a report", file=sys.stderr)
        return 1
    # Stage both reports before replacing the published page. Comparison failures
    # are visible in the slotted report; failure to produce that report preserves
    # the previous publication instead of silently dropping the slotted tables.
    with tempfile.TemporaryDirectory(prefix="egglog-nightly-") as temporary:
        stage = Path(temporary)
        try:
            status = _run_slotted(stage, timeout=args.slotted_timeout, jobs=args.slotted_jobs)
        except (OSError, SystemExit) as error:
            print(f"nightly: slotted collection failed: {error}", file=sys.stderr)
            return 1
        artifacts = ("slotted.html", "slotted.md", "slotted.jsonl")
        if any(not (stage / name).is_file() for name in artifacts):
            print("nightly: slotted collection did not produce all reports", file=sys.stderr)
            return 1
        if status != 0:
            print(
                "nightly: slotted comparisons are incomplete or failed; see the report's error banner", file=sys.stderr
            )
        output_dir.mkdir(parents=True, exist_ok=True)
        for name in artifacts:
            shutil.copyfile(stage / name, output_dir / name)
        shutil.copyfile(REPORT_PATH, output_dir / "index.jsonl")
        (output_dir / "index.html").write_text(_with_slotted_report(PAGE_PATH.read_text()))
    print(f"nightly: wrote report to {output_dir / 'index.html'}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
