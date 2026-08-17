"""Does the machinery reach a fixpoint of its own rules?

Open question 2 says no: two rules derive a class-level self-loop from a node's
edges, and the shrinking rule deletes the too-wide result, so the pair oscillates.
Semi-naive hides it -- the derivation never re-runs -- but `saturate` asks the
question directly, and a run that will not terminate is the oscillation.
"""
import subprocess
import sys
sys.path.insert(0, "slotted-experiments/xdiff")
import xdiff as X

TAIL = "(run-schedule (saturate (run)))\n(print-size App2)\n"

for name in ("X1", "X2", "C5", "S2", "B2"):
    case = next((c for c in X.curated() if c.name.startswith(name)), None)
    if case is None:
        continue
    prog = X.egg_program(case).replace("(print-function SameClass 100000)", TAIL)
    p = X.ROOT / f"sat-{name}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True,
                           text=True, cwd=X.ROOT, timeout=90)
        verdict = "reaches a fixpoint" if r.returncode == 0 else \
                  f"error: {r.stderr.strip()[:70]}"
    except subprocess.TimeoutExpired:
        verdict = "DOES NOT TERMINATE under saturate"
    finally:
        p.unlink(missing_ok=True)
    print(f"  {case.name:34} {verdict}", flush=True)
