"""Are the unchecked invariants the primitives rely on actually maintained?

`inverse` is total and only meaningful on a one-to-one map; nothing checks that its
input is one-to-one. A composition of one-to-one maps is one-to-one, so it is
enough to ask whether every renaming the machinery *stores* is one-to-one.

Non-injectivity is detectable without a new primitive: for one-to-one `m`,
`(compose m (inverse m))` is the identity on `im(m)` and so has as many keys as `m`.
For non-injective `m` the image is smaller, so the lengths differ.

Also reports malformed App edges -- an edge whose domain is not its child's slot
set, which Def. 4 forbids and which is what the migration bug produced.

CAUTION: the edge check OVER-REPORTS as things stand. It reads a child's slot count
off the length of a self-loop, and a class can carry a too-wide identity self-loop
(open question 2 in the doc), which makes the comparison fail on a perfectly good
edge. On `X1` most of what it flags is that, not a bad edge: an edge `{0->0}` to
`(Var 0)` is correct and only looks wrong beside a self-loop `{0->0, 2->2}` that
`(Var 0)` should never have had. Read the rows, do not trust the count. Fixing
question 2 would turn this into a real well-formedness check.

The injectivity check has no such caveat -- it is self-contained.
"""
import subprocess
import sys
sys.path.insert(0, "slotted-experiments/xdiff")
import xdiff as X

OBS = """
;; a stored renaming that is not one-to-one
(relation NotInjective (Renaming))
(rule ((RenamesToLeader a m b)
       (!= (map-length m) (map-length (compose m (inverse m)))))
      ((NotInjective m)))
(rule ((= n (App f m1 c1 m2 c2))
       (!= (map-length m1) (map-length (compose m1 (inverse m1)))))
      ((NotInjective m1)))
(rule ((= n (App f m1 c1 m2 c2))
       (!= (map-length m2) (map-length (compose m2 (inverse m2)))))
      ((NotInjective m2)))

;; an edge whose domain is not its child's slot set (Def. 4)
(relation BadEdge (String Renaming U))
(rule ((= n (App f m1 c1 m2 c2))
       (RenamesToLeader c1 s c1)
       (!= (map-length m1) (map-length s)))
      ((BadEdge f m1 c1)))
(rule ((= n (App f m1 c1 m2 c2))
       (RenamesToLeader c2 s c2)
       (!= (map-length m2) (map-length s)))
      ((BadEdge f m2 c2)))

(run 4)
(print-size NotInjective)
(print-size BadEdge)
"""


def probe(case):
    prog = X.egg_program(case).replace("(print-function SameClass 100000)", OBS)
    p = X.ROOT / f"inv-{abs(hash(case.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True,
                           text=True, cwd=X.ROOT, timeout=300)
    except subprocess.TimeoutExpired:
        return None
    finally:
        p.unlink(missing_ok=True)
    n = [int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()]
    return tuple(n[-2:]) if len(n) >= 2 else None


tot_ni = tot_be = 0
for c in X.curated():
    got = probe(c)
    if got is None:
        print(f"  {c.name:34} timeout")
        continue
    ni, be = got
    tot_ni += ni
    tot_be += be
    if ni or be:
        print(f"  {c.name:34} non-injective {ni}  malformed edges {be}")
print(f"\ntotals across the curated corpus: non-injective {tot_ni}, "
      f"malformed edges {tot_be}")
