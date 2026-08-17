"""Does declining migration cost an answer, now that declined nodes stay visible?

`slotted-egraph-encoding-11.egg` declines to migrate a node whose child edge would
be narrowed; `-minting.egg` mints a name and always migrates. Declining leaves the
node un-canonicalised, which is only a *compression* gap so long as the node stays
findable -- and the single-parent fix is what keeps it findable.

This runs both machineries over the same corpus and compares the partitions they
produce, which is the thing a user rule can actually observe.
"""
import subprocess
import sys
sys.path.insert(0, "slotted-experiments/xdiff")
import xdiff as X

MINT = "slotted-egraph-encoding-11-minting.egg"


def run(case, machinery=None):
    prog = X.egg_program(case)
    if machinery:
        prog = prog.replace("slotted-egraph-encoding-11.egg", machinery)
    p = X.ROOT / f"gvm-{abs(hash(case.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True,
                           text=True, cwd=X.ROOT, timeout=300)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    finally:
        p.unlink(missing_ok=True)
    if r.returncode != 0:
        return f"CRASH {r.stderr.strip()[:60]}"
    return X.parse_same_class(r.stdout, len(case.probes))


same = diff = skipped = 0
for c in X.curated():
    g, m = run(c), run(c, MINT)
    if "TIMEOUT" in (g, m) or str(g).startswith("CRASH") or str(m).startswith("CRASH"):
        skipped += 1
        print(f"  {c.name:34} skipped (guarded={str(g)[:20]} minting={str(m)[:20]})")
        continue
    if g == m:
        same += 1
    else:
        diff += 1
        print(f"  {c.name:34} DIFFERS")
        print(f"      guarded {str(g)[:150]}")
        print(f"      minting {str(m)[:150]}")
print(f"\nsame {same}, differ {diff}, skipped {skipped}")
