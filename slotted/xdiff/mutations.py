"""Does the corpus still catch each bug it was built to catch?

Coverage is a property, so it is asserted rather than inspected. Each mutation puts a past
bug back into the compiler and the corpus must still break by the recorded amount: fewer
means the corpus has stopped testing something, more means a case newly disagrees and wants
looking at either way.

A mutation earns its place by *failing* here when reintroduced. One that stops discriminating
is not kept as decoration -- `wide-kids` and `binder-1st` were both removed once they stopped,
the first because `def4-edges.py` checks the property it stood for and the second because the
rule it violated is definitional rather than empirical.

`unordered` went the same way, for a better reason than the others: a frame is the same
whatever order its atoms are joined in, so the mutation breaks no case at all.
`order-independence.py` measures that property directly, which is where it is checked now.
`root-only`, `slot-late` and `no-unify` were bugs of the per-atom solve the frame replaced,
and went with it; `union-id` went when the frame was anchored at the rule's root, which makes
the root's renaming the identity and egglog's `union` the action itself.

    python3 slotted/xdiff/mutations.py
"""

import os
import re
import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

#: mutation -> cases of the curated corpus that must disagree with the reference
EXPECTED = {
    # A frame may identify two slots of one e-node or class: `CLQ1`, one variable over
    # two node slots inside a slotless class, and three more. With the action a plain
    # union, a root renaming that is no longer injective is asserted rather than dropped
    # by the machinery, so more of the corpus notices than when the action was `Equated`.
    "no-cliques": 4,
    # Two different slot literals are no longer two different slots: `LIT1`.
    "literals-alias": 1,
    # Only the identity refinement is offered, so a match that needs two placeholders
    # identified is never found.
    "no-refine": 3,
    # A repeated variable is compared as if its class had no symmetries.
    "no-symmetry": 2,
    # The side conditions are dropped: every guarded case fires where it should not.
    "no-guard": 6,
}


def mismatches(bugs):
    """Curated cases whose matching disagrees with the reference, under `bugs`."""
    env = dict(os.environ, XDIFF_BUGS=bugs)
    r = subprocess.run(
        [sys.executable, "slotted/xdiff/xdiff.py"],
        capture_output=True,
        text=True,
        cwd=X.ROOT,
        env=env,
        timeout=3600,
    )
    m = re.search(r"^\s*(\d+)\s+MATCHING mismatch", r.stdout, re.M)
    return int(m.group(1)) if m else None


bad = []
clean = mismatches("")
print(f"  {'(no mutation)':14} {clean} mismatches, expected 0")
if clean != 0:
    bad.append("the unmutated corpus does not agree with the reference")

for bug, want in EXPECTED.items():
    got = mismatches(bug)
    note = (
        ""
        if got == want
        else ("  <-- STOPPED DISCRIMINATING" if got is not None and got < want else "  <-- more than recorded")
    )
    print(f"  {bug:14} {got} mismatches, expected {want}{note}", flush=True)
    if got != want:
        bad.append(f"{bug}: {got} != {want}")

print(f"\n{len(EXPECTED) - len([b for b in bad if not b.startswith('the')])}/{len(EXPECTED)} mutations still caught")
for b in bad:
    print(f"  FAIL {b}")
sys.exit(1 if bad else 0)
