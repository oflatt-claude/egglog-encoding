"""Check that source rule names survive Rust compilation.

Run with `python3 slotted/checks/check-rule-names.py`.
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TESTS = ROOT / "slotted/tests"
EGGLOG = ROOT / "target/debug/egglog-experimental"

NAME = re.compile(r':name\s+"([^"]+)"')
BARE = re.compile(r":name\s+([^\s()\"]+)")


def main():
    checked = missing = 0
    bad = []
    for src in sorted(TESTS.glob("*.egg")):
        text = re.sub(r";[^\n]*", "", src.read_text())  # a name in prose is not a rule
        want = set(NAME.findall(text))
        if not want and not BARE.search(text):
            continue
        # a bare `:name x` is accepted by this compiler and rejected by egglog, so it is
        # reported rather than counted -- the corpus is meant to be written egglog's way
        loose = {n for n in BARE.findall(text) if n not in want and not n.startswith('"')}
        result = subprocess.run(
            [str(EGGLOG), "--slotted", "--mode", "desugar", str(src)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        got = set(NAME.findall(result.stdout))
        for n in sorted(want - got):
            bad.append(f"{src.name}: rule {n!r} has no `:name` in the generated egglog")
        for n in sorted(loose):
            bad.append(f"{src.name}: rule {n!r} is named without quotes, which egglog rejects")
        checked += len(want)
        missing += len(want - got)
    for line in bad:
        print(f"  FAIL {line}")
    print(f"\n{checked - missing}/{checked} rule names reach the generated egglog")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
