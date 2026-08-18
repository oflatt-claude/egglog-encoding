"""Compare the two things migration can do when a node outgrows its leader's frame.

A node can use a slot its leader's frame cannot name -- one the class does not depend
on. `MIGRATION` in `slotted-experiments/gen-node-rules.py` says what happens then:

  decline  leave the node where it is, so follower classes are not emptied
  mint     invent a name and move it, as the reference's `compose_fresh` does

Both agree with the reference on partitions and node counts, so the choice is about the
encoding's own consistency, and neither dominates:

  decline   0 wide edges (43 curated, 250 generated), 3 follower classes holding a node
  mint      1 wide-edge case in 250 generated,         1 follower class holding a node

Minting used to cost about 150x the rows on `X2`, which is why declining was chosen.
That is no longer true -- the corpus totals 189 e-node rows either way -- because the
fan-out was `ClassSlots` and the alpha-finder tie-break manufacturing alpha-variants,
both since fixed.

Run this after regenerating in one mode, then the other; it reports the totals the
comparison above is made of. There used to be a hand-maintained copy of the whole
machinery for this, which drifted until it had none of `ClassSlots`, `compose-total` or
the current tie-break. Generating the variant is what stops that recurring.

    sed -i 's/^MIGRATION = .*/MIGRATION = "mint"/' slotted-experiments/gen-node-rules.py
    python3 slotted-experiments/gen-node-rules.py
    python3 slotted-experiments/xdiff/migration-modes.py
"""
import subprocess
import sys
sys.path.insert(0, "slotted-experiments/xdiff")
import xdiff as X

MODE = "\n".join(f"(print-size App{n})" for n in (2, 3, 4))


def rows(case):
    prog = X.egg_program(case).replace("(print-function SameClass 100000)", MODE)
    p = X.ROOT / f"mm-{abs(hash(case.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True,
                           text=True, timeout=300, cwd=X.ROOT)
    except subprocess.TimeoutExpired:
        return None
    finally:
        p.unlink(missing_ok=True)
    nums = [int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()]
    return sum(nums[-3:]) if len(nums) >= 3 else None


total = 0
biggest = []
for c in X.curated():
    n = rows(c)
    if n is None:
        print(f"  {c.name:38} timeout")
        continue
    total += n
    biggest.append((n, c.name))

biggest.sort(reverse=True)
print(f"total e-node rows across the corpus: {total}")
for n, name in biggest[:5]:
    print(f"  {n:5}  {name}")
