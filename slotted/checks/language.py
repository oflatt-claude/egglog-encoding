"""Source fixtures, documentation examples, and rule-library consistency checks."""

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import reference as syntax  # noqa: E402

SRC_DIR = ROOT / "slotted" / "tests"
# These fixtures expect the reference nested matcher's restricted aliasing.
NESTED = SRC_DIR / "nested"


def slotted_sources():
    """Every source fixture and language library, in path order."""
    return (
        sorted(SRC_DIR.rglob("*.egg"))
        + sorted((ROOT / "slotted/benchmarks").rglob("*.egg"))
        + sorted((ROOT / "slotted/languages").glob("*.egg"))
    )


def sources(pattern=None):
    srcs = [p for p in slotted_sources() if not pattern or pattern in p.name]
    if not srcs:
        print("no slotted sources found")
        return 1
    # A source with no claim in it is a rule LIBRARY, not a test. It is still compiled
    # and run, so its rules have to load, but counting it as a passing test would
    # inflate the number with something that asserts nothing.
    libs = {p.name for p in srcs if "(check" not in p.read_text()}

    bad = []
    for src in srcs:
        cmd = [str(ROOT / "target" / "debug" / "egglog-experimental"), "--slotted", str(src)]
        if NESTED in src.parents:
            cmd.append("--slotted-no-aliasing")
        r = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT, timeout=1800)
        print(f"  ok   {src.name}" if r.returncode == 0 else f"  FAIL {src.name}: {r.stderr.strip()[:300]}")
        if r.returncode != 0:
            bad.append(src.name)

    tests = [p for p in srcs if p.name not in libs]
    print(
        f"\n{len(tests) - len([b for b in bad if b not in libs])}/{len(tests)} slotted tests pass"
        + (f", {len(libs)} rule librar{'y loads' if len(libs) == 1 else 'ies load'}" if libs else "")
        + (f"   FAILED: {', '.join(bad)}" if bad else "")
    )
    return 1 if bad else 0


DOC = ROOT / "egglog-experimental/src/slotted/LANGUAGE.md"
EGGLOG = ROOT / "target/debug/egglog-experimental"

# Every documented assertion form must appear in at least one executable example.
CLAIMS = ("=", "!=", "renaming-=", "renaming-!=", "slots", "holds", "not-holds")


def blocks(text):
    return re.findall(r"```slotted\n(.*?)```", text, re.S)


def docs():
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
            r = subprocess.run([str(EGGLOG), "--slotted", path], capture_output=True, text=True, timeout=1800, cwd=ROOT)
            ok = r.returncode == 0
            if not ok:
                err = [ln for ln in (r.stdout + r.stderr).splitlines() if "ERROR" in ln or "FAIL" in ln]
                bad.append((i, err[-1][:120] if err else r.stderr[-120:]))
            print(f"  {'ok  ' if ok else 'FAIL'} Rust: block {i}  {first[:58]}")
        finally:
            Path(path).unlink(missing_ok=True)

    # A claim in the table nobody ever runs is a claim nobody checked.
    unused = [c for c in CLAIMS if not any(f"({c} " in p for p in progs)]

    for i, why in bad:
        print(f"       block {i}: {why}")
    if unused:
        print(f"       claims in the table with no runnable example: {', '.join(unused)}")
    unexercised = f", {len(unused)} claims unexercised" if unused else ""
    print(f"\n{len(progs) - len({i for i, _ in bad})}/{len(progs)} examples run through the Rust CLI{unexercised}")
    return 1 if bad or unused else 0


# A `.ref` sits beside the file that declares its language, which is the slotted source
# where the language has rules and `languages/` where it does not.
LANGUAGES = ROOT / "slotted/languages"
ORACLE = ROOT / "slotted" / "xmulti" / "src" / "main.rs"


def oracle_language():
    """`{tag}` and `{variant}` from the oracle's `define_language!` block."""
    text = ORACLE.read_text()
    start = text.index("define_language! {")
    depth, i = 0, start + len("define_language!")
    while True:
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                break
        i += 1
    body = "\n".join(line.split("//")[0] for line in text[start:i].splitlines())
    tags = set(re.findall(r'=\s*"([^"]+)"', body))
    untagged = set(re.findall(r"^\s*([A-Z]\w*)\([^)]*\)\s*,\s*$", body, re.M))
    return tags, untagged


def correspondence():
    tags, untagged = oracle_language()
    if not tags:
        print(f"FAIL: no tags parsed out of {ORACLE.relative_to(ROOT)}")
        return 1
    print(f"  oracle: {len(tags)} tagged, {len(untagged)} untagged ({', '.join(sorted(untagged))})")

    bad = []
    refs = sorted(LANGUAGES.glob("*.ref"))
    for ref in refs:
        corr = syntax.read_correspondence(ref)
        spec = syntax.read_language(ref.with_suffix(".egg"))
        missing = sorted({t for t, _ in corr.values() if t and t not in tags})
        # an `=payload` operator has no tag, so the oracle must carry it as an
        # untagged variant -- otherwise the harness is writing a bare payload the
        # oracle would read as a tag
        payload_ops = sorted(op for op, (t, _) in corr.items() if t is None)
        note = f", payload ops {payload_ops}" if payload_ops else ""
        if not untagged and payload_ops:
            missing.append("(the oracle has no untagged variant to hold a payload)")
        print(
            f"  {'ok  ' if not missing else 'FAIL'} {ref.name:<12} "
            f"{len(corr)} operators over {len(spec)} constructors{note}"
            + (f"\n       tags the oracle does not answer to: {missing}" if missing else "")
        )
        if missing:
            bad.append(ref.name)

    print(
        f"\n{'OK: ' if not bad else 'FAIL: '}"
        f"{len(refs) - len(bad)}/{len(refs)}"
        " correspondence files agree with the oracle" + (f"   FAILED: {', '.join(bad)}" if bad else "")
    )
    return 1 if bad else 0


LIBRARIES = [
    ROOT / "slotted" / "languages" / "array-rules.egg",
    ROOT / "slotted" / "languages" / "sdql-rules.egg",
    ROOT / "slotted" / "tests" / "sdql-paper-batax.egg",
]


def guards():
    bad, rules = [], 0
    for path in LIBRARIES:
        # the source's own language: a library includes its declarations, a test makes them
        src = syntax.Source(path)
        lang = src.lang
        for form in syntax.parse(path.read_text()):
            if not (isinstance(form, list) and form and form[0] == "rewrite"):
                continue
            r = syntax.rewrite_parts(src, form)
            rules += 1
            lhs = syntax.rhs_of(lang, src.term(r["lhs"], ground=False))
            rhs_term = src.term(r["rhs"], ground=False)
            rhs = syntax.rhs_of(lang, rhs_term)
            missing = syntax.missing_capture_guards(lang, lhs, rhs, r["conds"])
            if missing:
                owed = " ".join(f"(not-free {s} {v})" for s, v in sorted(missing))
                print(f"  FAIL {path.name}: {r['name']} rebinds over an outside variable without {owed}")
                bad.append(r["name"])
    print(f"\n{rules - len(bad)}/{rules} rules state the capture guards they owe")
    return 1 if bad else 0


TESTS = ROOT / "slotted/tests"

NAME = re.compile(r':name\s+"([^"]+)"')
BARE = re.compile(r":name\s+([^\s()\"]+)")


def names():
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("sources", "docs", "correspondence", "guards", "names"))
    parser.add_argument("-k", metavar="SUBSTRING", help="filter source fixture names")
    args = parser.parse_args()
    if args.check == "sources":
        return sources(args.k)
    if args.k:
        parser.error("-k applies to the sources check")
    checks = {"docs": docs, "correspondence": correspondence, "guards": guards, "names": names}
    return checks[args.check]()


if __name__ == "__main__":
    sys.exit(main())
