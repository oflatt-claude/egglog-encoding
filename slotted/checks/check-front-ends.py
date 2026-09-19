#!/usr/bin/env python3
"""Two ways into the encoder must produce the same rule.

`gen-sdql-rules.py` compiles a rule from a Python table against a language SPEC file;
`slotted-egglog.py` compiles it from a slotted SOURCE that declares its own
constructors. Both call `slotted-encoder.py`, so a rule that exists on both sides is a
free cross-check on the two front-ends -- and on the claim that a slotted test is not
a second, quietly diverging encoder.

Compared up to a bijection on variable names, which is the only freedom. A generated
rule carries a `:ruleset` that a compiled one has no reason to and that is stripped; the
`:name` is on both sides and is compared, so the two front-ends have to agree on it.

Usage:  ./check-front-ends.py
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
SNAPSHOTS = ROOT / "slotted" / "tests" / "snapshots"


FIXED = {
    "rule",
    "let",
    "union",
    "delete",
    "set",
    "guard",
    "or",
    "and",
    "not",
    "true",
    "false",
    "App2",
    "App3",
    "App4",
    "Num",
    "Sym",
    "Scale",
    "Null",
    "Var",
    "ClassSlots",
    "RenamesToLeader",
    "Equated",
    "compose",
    "inverse",
}
VARIABLE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
TOKEN = re.compile(r'\(|\)|"[^"]*"|[^\s()]+')


def parse(text):
    toks = TOKEN.findall(text)
    pos = [0]

    def go():
        t = toks[pos[0]]
        pos[0] += 1
        if t != "(":
            return t
        out = []
        while toks[pos[0]] != ")":
            out.append(go())
        pos[0] += 1
        return out

    v = go()
    assert pos[0] == len(toks), f"trailing tokens in {text[:60]}"
    return v


def is_var(tok):
    return bool(VARIABLE.match(tok)) and tok not in FIXED


def alpha_eq(a, b, fwd, bwd, path="/"):
    """None if equal up to a variable bijection, else the first difference."""
    if isinstance(a, list) != isinstance(b, list):
        return f"{path}: {'a list' if isinstance(a, list) else a} vs {'a list' if isinstance(b, list) else b}"
    if isinstance(a, list):
        if len(a) != len(b):
            return f"{path}: arity {len(a)} vs {len(b)}\n       want {a}\n        got {b}"
        for i, (x, y) in enumerate(zip(a, b, strict=True)):
            why = alpha_eq(x, y, fwd, bwd, f"{path}{i}/")
            if why:
                return why
        return None
    if is_var(a) != is_var(b):
        return f"{path}: {a!r} vs {b!r} -- one is a variable, the other is not"
    if not is_var(a):
        return None if a == b else f"{path}: {a!r} vs {b!r}"
    if fwd.setdefault(a, b) != b or bwd.setdefault(b, a) != a:
        return f"{path}: {a!r} is already matched with {fwd.get(a)!r}, and {b!r} with {bwd.get(b)!r}"
    return None


def strip_comment(line):
    quoted = False
    for i, ch in enumerate(line):
        if ch == '"':
            quoted = not quoted
        elif ch == ";" and not quoted:
            return line[:i]
    return line


def top_forms(text):
    """Every balanced top-level form, comments removed."""
    out, depth, form = [], 0, []
    for raw in text.splitlines():
        line = strip_comment(raw)
        if not line.strip():
            continue
        depth += line.count("(") - line.count(")")
        form.append(line.strip())
        if depth <= 0:
            out.append(" ".join(form))
            form, depth = [], 0
    if form:
        raise SystemExit("unbalanced parens")
    return out


#: the rule each slotted test shares with a generated file, and where to find it
SHARED = [
    ("sdql-sum-sing.egg", "target/slotted/slotted-sdql-rules.egg", "sum-sing"),
]


def rules_of(path):
    return [f for f in top_forms(path.read_text()) if f.startswith("(rule")]


def main():
    bad = []
    for snap_name, gen_rel, rule in SHARED:
        gen = ROOT / gen_rel
        named = [r for r in rules_of(gen) if f':name "{rule}"' in r]
        if len(named) != 1:
            bad.append(f"{rule}: {len(named)} rules named it in {gen.name}")
            continue
        # Only the `:ruleset` belongs to the generated file alone. The `:name` is on
        # both sides now, so it is compared rather than stripped.
        from_generator = re.sub(r"\s*:ruleset \w+(?= :name )", "", named[0])

        snap = SNAPSHOTS / snap_name
        user = [r for r in rules_of(snap) if ":ruleset slotted" not in r]
        if len(user) != 1:
            bad.append(f"{snap_name}: {len(user)} user rules, expected 1")
            continue

        why = alpha_eq(parse(from_generator), parse(user[0]), {}, {})
        print(
            f"  {'ok  ' if why is None else 'FAIL'} {rule:<12} {snap_name} vs {gen.name}"
            + (f"\n       {why}" if why else "")
        )
        if why:
            bad.append(rule)

    print(
        f"\n{'OK: ' if not bad else 'FAIL: '}{len(SHARED) - len(bad)}/{len(SHARED)}"
        " rules compile the same from both front-ends" + (f"   FAILED: {', '.join(bad)}" if bad else "")
    )
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
