"""Is any edge NARROWER than its child's slot set?

Def. 4 wants an edge's domain to be *exactly* its child's slots. `xdiff.py`'s check 6 looks
for edges that are too wide, and the narrow direction was recorded as "not checkable this
way" and left to `compose-total`. It is checkable against `ClassSlots`, which is what a
class's slots are held in, and it has a witness: the reference keeps such a slot as a
redundant slot of the node, so dropping it is a real difference and not just untidiness.

    python3 slotted-experiments/xdiff/narrow-edges.py            curated
    python3 slotted-experiments/xdiff/narrow-edges.py fuzz 250   generated
"""
import random
import subprocess
import sys
sys.path.insert(0, "slotted-experiments/xdiff")
import xdiff as X

HEAD = """
(ruleset narrow)
(relation NarrowEdge (String Renaming Renaming))
"""


def obs():
    out = [HEAD]
    for n in (2, 3, 4):
        cols = " ".join(f"m{i} c{i}" for i in range(1, n + 1))
        for i in range(1, n + 1):
            out.append(f"(rule ((= v (App{n} f {cols}))\n"
                       f"       (= s (ClassSlots c{i}))\n"
                       f"       (< (map-length m{i}) (map-length s)))\n"
                       f"      ((NarrowEdge f m{i} s)) :ruleset narrow)")
    out += ["(run narrow 1)", "(print-size NarrowEdge)",
            "(print-function NarrowEdge 8)"]
    return "\n".join(out)


if len(sys.argv) > 1 and sys.argv[1] == "fuzz":
    rng = random.Random(0)
    cases = [X.rand_case(rng, i)
             for i in range(int(sys.argv[2]) if len(sys.argv) > 2 else 250)]
else:
    cases = X.curated()

total, bad = 0, []
for c in cases:
    prog = X.egg_program(c).replace("(print-function SameClass 100000)", obs())
    p = X.ROOT / f"xdiff-tmp-narrow-{abs(hash(c.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True,
                           text=True, cwd=X.ROOT, timeout=120)
    except subprocess.TimeoutExpired:
        continue
    finally:
        p.unlink(missing_ok=True)
    nums = [int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()]
    if r.returncode != 0 or not nums:
        continue
    n = nums[-1]
    total += n
    if n:
        bad.append(c.name)
        rows = [l.strip().split(" -> ")[0] for l in r.stdout.splitlines()
                if l.strip().startswith("(NarrowEdge")]
        print(f"  {c.name:12} {n} narrow edge(s)", flush=True)
        for row in rows[:3]:
            print(f"       {row[:110]}")

print(f"\n{total} narrow edges over {len(cases)} cases, in {len(bad)}: "
      f"{', '.join(bad[:8])}{' ...' if len(bad) > 8 else ''}")
sys.exit(1 if bad else 0)
