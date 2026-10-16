#!/usr/bin/env python3
"""Run slotted fixtures and rule libraries through the Rust CLI.

Nested-matcher fixtures run with --slotted-no-aliasing. Libraries are loaded
and counted separately from tests that contain assertions.

Usage:
    ./run-slotted-tests.py          run every fixture and library
    ./run-slotted-tests.py -k sdql  select files by name
    ./run-slotted-tests.py --proofs   compile each under the proof-compatible profile
                                      and run it natively, every claim kept a check
    ./run-slotted-tests.py --slotted-proofs  translate and verify equality claims
"""

import argparse
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC_DIR = ROOT / "slotted" / "tests"
# These fixtures expect the reference nested matcher's restricted aliasing.
NESTED = SRC_DIR / "nested"


def slotted_sources():
    """Every source fixture and language library, in path order."""
    return sorted(SRC_DIR.rglob("*.egg")) + sorted((ROOT / "slotted/languages").glob("*.egg"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-k", metavar="SUBSTRING")
    ap.add_argument(
        "--proofs",
        action="store_true",
        help="the proof-compatible profile, run natively with its claims as checks",
    )
    ap.add_argument(
        "--slotted-proofs",
        action="store_true",
        help=(
            "the proof-compatible profile under `egglog-experimental --slotted --proofs`: every positive "
            "claim is proved, translated to a slotted proof and checked (sources that use "
            "`subst` are skipped: it has no proof translation yet)"
        ),
    )
    args = ap.parse_args()
    if args.proofs and args.slotted_proofs:
        ap.error("--proofs runs the claims as checks; --slotted-proofs proves them")

    srcs = [p for p in slotted_sources() if not args.k or args.k in p.name]
    if not srcs:
        print("no slotted sources found")
        return 1
    # A source with no claim in it is a rule LIBRARY, not a test. It is still compiled
    # and run, so its rules have to load, but counting it as a passing test would
    # inflate the number with something that asserts nothing.
    libs = {p.name for p in srcs if "(check" not in p.read_text()}

    bad = []
    skipped = []
    for src in srcs:
        cmd = [str(ROOT / "target" / "debug" / "egglog-experimental"), "--slotted", str(src)]
        if NESTED in src.parents:
            cmd.append("--slotted-no-aliasing")
        if args.proofs:
            cmd.append("--slotted-proof-checks")
        if args.slotted_proofs:
            cmd.append("--proofs")
        r = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT, timeout=1800)
        if args.slotted_proofs and r.returncode != 0 and "uses subst, which has no proof translation" in r.stderr:
            skipped.append(src.name)
            print(f"  skip {src.name}: uses subst")
            continue
        print(f"  ok   {src.name}" if r.returncode == 0 else f"  FAIL {src.name}: {r.stderr.strip()[-600:]}")
        if r.returncode != 0:
            bad.append(src.name)

    tests = [p for p in srcs if p.name not in libs and p.name not in skipped]
    loaded_libs = libs.difference(skipped, bad)
    print(
        f"\n{len(tests) - len([b for b in bad if b not in libs])}/{len(tests)} slotted tests pass"
        + (f", {len(loaded_libs)} rule librar{'y loads' if len(loaded_libs) == 1 else 'ies load'}" if libs else "")
        + (f", {len(skipped)} skipped" if skipped else "")
        + (f"   FAILED: {', '.join(bad)}" if bad else "")
    )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
