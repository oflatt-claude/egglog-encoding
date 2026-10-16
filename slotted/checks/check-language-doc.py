#!/usr/bin/env python3
"""Run every complete program marked ```slotted in LANGUAGE.md.

Each example must pass through both the Rust CLI and the Python oracle.
Untagged code blocks illustrate syntax and are not executed.

Run with `python3 slotted/checks/check-language-doc.py`."""

import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
DOC = ROOT / "slotted" / "LANGUAGE.md"
COMPILERS = {
    "Rust": [str(ROOT / "target/debug/egglog-experimental"), "--slotted"],
    "Python": [sys.executable, str(ROOT / "slotted/slotted-egglog.py")],
}

#: Every claim the doc names in its table, so a claim can be added there and forgotten
#: about here. Each has to appear in at least one runnable example.
CLAIMS = ("=", "!=", "renaming-=", "renaming-!=", "slots", "holds", "not-holds")


def blocks(text):
    return re.findall(r"```slotted\n(.*?)```", text, re.S)


def main():
    text = DOC.read_text()
    progs = blocks(text)
    if not progs:
        print(f"FAIL: {DOC.name} has no ```slotted blocks")
        return 1

    bad = []
    for i, src in enumerate(progs):
        first = next((ln for ln in src.splitlines() if ln.strip() and not ln.startswith(";")), "")
        with tempfile.NamedTemporaryFile("w", suffix=".egg", delete=False) as f:
            f.write(src)
            path = f.name
        try:
            for compiler, command in COMPILERS.items():
                r = subprocess.run([*command, path], capture_output=True, text=True, timeout=1800, cwd=ROOT)
                ok = r.returncode == 0
                if not ok:
                    err = [ln for ln in (r.stdout + r.stderr).splitlines() if "ERROR" in ln or "FAIL" in ln]
                    bad.append((i, f"{compiler}: " + (err[-1][:120] if err else "?")))
                print(f"  {'ok  ' if ok else 'FAIL'} {compiler}: block {i}  {first[:58]}")
        finally:
            pathlib.Path(path).unlink(missing_ok=True)

    # A claim in the table nobody ever runs is a claim nobody checked.
    unused = [c for c in CLAIMS if not any(f"({c} " in p for p in progs)]

    for i, why in bad:
        print(f"       block {i}: {why}")
    if unused:
        print(f"       claims in the table with no runnable example: {', '.join(unused)}")
    unexercised = f", {len(unused)} claims unexercised" if unused else ""
    print(f"\n{len(progs) - len({i for i, _ in bad})}/{len(progs)} examples run through both compilers{unexercised}")
    return 1 if bad or unused else 0


if __name__ == "__main__":
    sys.exit(main())
