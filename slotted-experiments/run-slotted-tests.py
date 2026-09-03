#!/usr/bin/env python3
"""Compile every slotted-language test and run it.

A test in `slotted-tests/` is a SLOTTED source when it includes nothing: it declares
its own constructors and the compiler supplies the core and the machinery. A test that
`(include ...)`s something is written in plain egglog against the encoding -- the
machinery tests -- and is run directly by `check-slotted.py`'s `egg-files`.

Usage:
    ./run-slotted-tests.py            compile and run each
    ./run-slotted-tests.py -k sdql    only those whose name contains `sdql`
    ./run-slotted-tests.py --emit     also write each compiled program to
                                      slotted-tests/snapshots/, so a change in the
                                      encoder shows up as a diff
"""

import argparse
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC_DIR = ROOT / "slotted-tests"
SNAPSHOTS = SRC_DIR / "snapshots"
COMPILE = ROOT / "slotted-experiments" / "slotted-compile.py"


#: The hand-written core. It includes nothing because everything else includes IT, so
#: it is the one file the rule below would otherwise misread as a slotted source.
CORE = "slotted-egraph-encoding-11.egg"


def slotted_sources():
    """The tests written in the slotted language: the ones that include nothing."""
    return [p for p in sorted(SRC_DIR.glob("*.egg")) if p.name != CORE and "(include" not in p.read_text()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-k", metavar="SUBSTRING")
    ap.add_argument("--emit", action="store_true", help="also write the snapshots")
    args = ap.parse_args()

    srcs = [p for p in slotted_sources() if not args.k or args.k in p.name]
    if not srcs:
        print("no slotted sources found")
        return 1

    if args.emit:
        SNAPSHOTS.mkdir(exist_ok=True)

    bad = []
    for src in srcs:
        cmd = [sys.executable, str(COMPILE), str(src), "--run"]
        if args.emit:
            cmd += ["-o", str(SNAPSHOTS / src.name)]
        r = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT, timeout=1800)
        line = (r.stdout.strip().splitlines() or [""])[0]
        print(f"  {line or r.stderr.strip()[:160]}")
        if r.returncode != 0:
            bad.append(src.name)

    print(f"\n{len(srcs) - len(bad)}/{len(srcs)} slotted tests pass" + (f"   FAILED: {', '.join(bad)}" if bad else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
