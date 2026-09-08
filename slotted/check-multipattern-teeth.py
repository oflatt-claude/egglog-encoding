"""Do `multipattern.egg`'s failing claims have teeth?

A `fail (check ...)` passes for two very different reasons: the rule correctly declined
to fire, or the rule could never have fired at all. The second is worthless, and it is
the easy mistake -- naming a term the rule would not produce even when misfiring, or
building the term after the `(run)`. Both happened while that file was written.

So each mutation below removes exactly one join from one rule and names the claims that
must then break. A mutation the file still passes is a claim that is not testing what
its comment says.

This is the .egg corpus's counterpart to `xdiff/mutations.py`, which puts past bugs back
into the compiler and requires the curated cases to notice. Same idea, different subject:
here the rules are mutated and the file's own claims are what must notice.

    python3 slotted/check-multipattern-teeth.py
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "slotted/tests/multipattern.egg"
MUTANT = ROOT / "target/slotted/multipattern-mutant.egg"

#: (what it breaks, text to replace, replacement, the claims that may break)
MUTATIONS = [
    (
        "beta premise unjoined from the function",
        ":when (= f (Lam $v body))\n         :name beta-guarded",
        ":when (= zz (Lam $v body))\n         :name beta-guarded",
        {"stuck"},
    ),
    (
        "load-after-store no longer joins on the address",
        ":when (= m (Store m0 p v))",
        ":when (= m (Store m0 pp v))",
        {"other"},
    ),
    (
        "double-product no longer joins the two factor pairs",
        ":when (= r (Mul a b))",
        ":when (= r (Mul aa bb))",
        {"no"},
    ),
    (
        "double-product's top pattern unjoined from the match",
        ":when (= e (Add l r))",
        ":when (= ee (Add l r))",
        # any `Root` now qualifies, so either failing claim may be the one reported
        {"no", "no2"},
    ),
    (
        "same-body no longer shares the body",
        ":when (= g (Lam $w body))",
        ":when (= g (Lam $w body2))",
        {"q"},
    ),
    (
        "eta's shape premise unjoined from the function",
        ":when (= f (Lam $w g))",
        ":when (= zz (Lam $w g))",
        {"notlam"},
    ),
    (
        "eta's slot side condition dropped",
        ":when (not-free $v f)\n         ",
        "",
        {"held"},
    ),
]

BROKE = re.compile(r"check \(RenamesToLeader \$([A-Za-z_][\w-]*)")


def broken_claim(text):
    """The term named by the claim egglog reported, or None if the file passed."""
    m = BROKE.search(text)
    return m.group(1) if m else None


def main():
    src = CORPUS.read_text()
    MUTANT.parent.mkdir(parents=True, exist_ok=True)
    bad = []
    for name, old, new, want in MUTATIONS:
        if old not in src:
            print(f"  STALE  {name}: the text it mutates is no longer in the file")
            bad.append(name)
            continue
        MUTANT.write_text(src.replace(old, new, 1))
        r = subprocess.run(
            [sys.executable, "slotted/slotted-egglog.py", str(MUTANT)],
            cwd=ROOT, capture_output=True, text=True, timeout=1800,
        )
        got = broken_claim(r.stdout + r.stderr)
        if got in want:
            print(f"  ok     {name}  ->  `{got}` breaks")
        elif got is None:
            print(f"  FAIL   {name}  ->  the file still passes, so no claim tests it")
            bad.append(name)
        else:
            print(f"  FAIL   {name}  ->  `{got}` broke, expected one of {sorted(want)}")
            bad.append(name)
    MUTANT.unlink(missing_ok=True)
    print(f"\n{len(MUTATIONS) - len(bad)}/{len(MUTATIONS)} multipattern claims have teeth")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
