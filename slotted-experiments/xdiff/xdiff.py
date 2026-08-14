#!/usr/bin/env python3
"""Differential tester: the egglog slotted encoding's multipattern matching
against the reference `slotted-egraphs` implementation.

For each generated case it builds one spec, runs it through both sides, and
compares the resulting partition of the probe terms:

  reference   slotted-experiments/xmulti  (reads the spec on stdin)
  encoding    a generated .egg file run through target/debug/egglog

It also checks two things that need no cross-system comparison:

  order independence  the encoding's answer must not depend on the order the
                      atoms are compiled in (the reference's does not)
  machinery baseline  with no rule at all, both sides must already agree, so a
                      mismatch is attributed to matching rather than to the
                      encoding of union/congruence/redundancy

Usage:
    ./xdiff.py            run the curated cases
    ./xdiff.py fuzz 200   run 200 random cases
"""

import itertools
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EGGLOG = ROOT / "target" / "debug" / "egglog"
XMULTI = ROOT / "slotted-experiments" / "xmulti"
MACHINERY = "tests/slotted-egraph-encoding-11.egg"

BINOPS = ["f", "g", "h", "k", "sub", "sub2", "add"]

# Permutations tried per case in the order-independence check. Each costs a full
# saturation on both sides, so this is the main knob on runtime.
PERM_CAP = 4

# Some generated e-graphs blow the machinery up, so every run is bounded and a
# timeout is reported as its own category rather than stalling the sweep.
RUN_TIMEOUT = 25

# ---------------------------------------------------------------- neutral terms
# term := ('var', n) | ('null',) | (op, t1, t2)


def slots(t):
    if t[0] == "var":
        return {t[1]}
    if t[0] == "null":
        return set()
    return slots(t[1]) | slots(t[2])


def sexpr(t):
    """Reference/spec syntax."""
    if t[0] == "var":
        return f"(var ${t[1]})"
    if t[0] == "null":
        return "null"
    return f"({t[0]} {sexpr(t[1])} {sexpr(t[2])})"


def mapof(d):
    if not d:
        return "(map-empty)"
    body = " ".join(f"{k} {v}" for k, v in sorted(d.items()))
    return f"(map-of {body})"


def edge(t):
    """The stored renaming from a child's slots into its parent's slot space.

    A leaf is stored as the canonical `(Var 0)`, so its edge names slot 0; any
    other subterm is built at its own slot names, so its edge is the identity.
    """
    if t[0] == "var":
        return {0: t[1]}
    if t[0] == "null":
        return {}
    return {s: s for s in slots(t)}


def enc(t):
    """Encoding syntax."""
    if t[0] == "var":
        return "(Var 0)"
    if t[0] == "null":
        return "(Null)"
    op, a, b = t
    return f'(App "{op}" {mapof(edge(a))} {enc(a)} {mapof(edge(b))} {enc(b)})'


# ------------------------------------------------------------------------ specs


class Case:
    def __init__(self, name, terms, unions, atoms, action, probes, rounds=10):
        self.name = name
        self.terms = terms          # [term]
        self.unions = unions        # [(term, term)]
        self.atoms = atoms          # [(root, op, c1, c2)] pvar names
        self.action = action        # (root, op, a, b) or None
        self.probes = probes        # [term]
        self.rounds = rounds

    def spec(self, atoms=None):
        atoms = self.atoms if atoms is None else atoms
        out = [f"rounds {self.rounds}"]
        out += [f"term {sexpr(t)}" for t in self.terms]
        out += [f"union {sexpr(a)} {sexpr(b)}" for a, b in self.unions]
        out += [f"atom {r} {o} {c1} {c2}" for (r, o, c1, c2) in atoms]
        if self.action:
            out.append("action {} {} {} {}".format(*self.action))
        out += [f"probe {sexpr(t)}" for t in self.probes]
        return "\n".join(out) + "\n"


# -------------------------------------------------------------- rule compiler
def compile_rule(atoms, action):
    """Compile a flattened multipattern into an egglog rule body + action.

    Atoms are processed in the given order. Each atom's `mp` is solved from
    EVERY constraint available at that point -- its root if already bound, and
    every child bound by an earlier atom -- with `find-mapping-total` so slots
    the constraints do not reach are minted rather than dropped.
    """
    body, uid = [], [0]

    def fresh(p):
        uid[0] += 1
        return f"{p}{uid[0]}"

    mp_of = {}      # pvar -> egglog var holding its renaming into slots(pattern)
    cls_of = {}     # pvar -> egglog var holding its leader
    pat = None      # identity on slots(pattern)

    for idx, (root, op, c1, c2) in enumerate(atoms):
        e1, e2 = fresh("p"), fresh("p")
        rv = cls_of.setdefault(root, fresh("V"))
        kids = []
        for cp in (c1, c2):
            kids.append(cls_of.setdefault(cp, fresh("C")))
        body.append(f'(= {rv} (App "{op}" {e1} {kids[0]} {e2} {kids[1]}))')

        dom = fresh("dom")
        body.append(f"(= {dom} (find-mapping {e1} {e2} {e1} {e2}))")

        firsts, seconds = [], []

        # the root, if an earlier atom already named its slots
        if root in mp_of:
            mv = mp_of[root]
            sym = fresh("sym")
            body.append(f"(RenamesToLeader {rv} {sym} {rv})")
            firsts.append(f"(compose {mv} {sym})")
            seconds.append(f"(compose (inverse {mv}) {mv})")

        # every child an earlier atom already named
        bound_before = set(mp_of)
        for cp, e in ((c1, e1), (c2, e2)):
            if cp in bound_before:
                mx = mp_of[cp]
                sym = fresh("sym")
                body.append(f"(RenamesToLeader {cls_of[cp]} {sym} {cls_of[cp]})")
                firsts.append(f"(compose {mx} {sym})")
                seconds.append(e)

        mp = fresh("mp")
        if idx == 0:
            # the initial atom fixes slots(pattern); its mp is the identity
            body.append(f"(= {mp} {dom})")
            pat = mp
        elif firsts:
            args = " ".join(firsts + seconds)
            body.append(f"(= {mp} (find-mapping-total {pat} {dom} {args}))")
        else:
            # nothing constrains this atom: every slot is minted
            body.append(
                f"(= {mp} (find-mapping-total {pat} {dom} (map-empty) (map-empty)))"
            )

        # walk the children: bind the new ones, check the ones bound in THIS atom
        for cp, e in ((c1, e1), (c2, e2)):
            if cp in mp_of:
                if cp not in bound_before:
                    # second occurrence within this atom: post-hoc Def. 6 check
                    sym = fresh("sym")
                    body.append(
                        f"(= {sym} (compose (inverse {mp_of[cp]}) (compose {mp} {e})))"
                    )
                    body.append(f"(RenamesToLeader {cls_of[cp]} {sym} {cls_of[cp]})")
            else:
                m = fresh("m")
                body.append(f"(= {m} (compose {mp} {e}))")
                mp_of[cp] = m
        if root not in mp_of:
            mp_of[root] = mp

    root, op, a, b = action
    # egglog's `union` equates e-classes, i.e. it can only assert an equation
    # whose two renamings are the identity. The root's renaming `mp_of[root]`
    # generally is NOT: it carries the matched node's slots into the pattern's.
    # Unioning the built node with the root as-is therefore asserts a *false*
    # equation whenever they differ, which shows up as spurious redundancy.
    #
    # So build the node in the root's own slot space instead, by pulling every
    # child renaming back through `inverse mp_root`, and guard that doing so
    # keeps all of the child's slots -- `compose` truncates silently, and a
    # dropped slot asserts that slot is redundant.
    # The built node lives in pattern slots, so the equation to assert is
    # `built = mp_root * X_root` -- a union over *renamed ids*, which egglog's
    # `union` cannot express (it equates e-classes, i.e. only the case where
    # both renamings are the identity). Insert the RenamesToLeader fact instead
    # and let the machinery's transitivity / single-parent rules re-orient it.
    mr = mp_of[root]
    act = (
        f'(let _hn (App "{op}" {mp_of[a]} {cls_of[a]} {mp_of[b]} {cls_of[b]}))\n'
        f"       (RenamesToLeader _hn {mr} {cls_of[root]})"
    )
    return "(rule (" + "\n       ".join(body) + f")\n      ({act}))"


# -------------------------------------------------------------- egg generation
def egg_program(case, atoms=None):
    atoms = case.atoms if atoms is None else atoms
    out = [f'(include "{MACHINERY}")']
    # A slotted e-class is NOT one egglog e-class: the alpha-finder relates
    # equal-up-to-renaming nodes with `RenamesToLeader` and deletes one, rather
    # than unioning them. So two probes are in the same slotted class when they
    # reach a common leader, which is also what the machinery's own tests check.
    out.append("(relation ProbeId (U i64))")
    out.append("(relation SameClass (i64 i64))")
    out.append("(rule ((ProbeId a i) (ProbeId b j)\n"
               "       (RenamesToLeader a m1 l) (RenamesToLeader b m2 l))\n"
               "      ((SameClass i j)))")
    if atoms:
        out.append(compile_rule(atoms, case.action))
    for i, t in enumerate(case.terms):
        out.append(f"(let _t{i} {enc(t)})")
    for i, (a, b) in enumerate(case.unions):
        out.append(f"(let _ua{i} {enc(a)})")
        out.append(f"(let _ub{i} {enc(b)})")
        out.append(f"(union _ua{i} _ub{i})")
    for i, t in enumerate(case.probes):
        out.append(f"(let _p{i} {enc(t)})")
    out.append(f"(run {case.rounds * 3})")
    for i, _ in enumerate(case.probes):
        out.append(f"(ProbeId _p{i} {i})")
    out.append(f"(run {case.rounds * 3})")
    out.append("(print-function SameClass 100000)")
    return "\n".join(out) + "\n"


def parse_same_class(stdout, n):
    """Turn the printed SameClass rows into the same canonical string the
    reference prints."""
    pairs = set()
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("(SameClass "):
            continue
        nums = line[len("(SameClass "):].split(")")[0].split()
        pairs.add((int(nums[0]), int(nums[1])))
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    for i, j in pairs:
        a, b = find(i), find(j)
        if a != b:
            parent[max(a, b)] = min(a, b)
    groups = {}
    for i in range(n):
        groups.setdefault(find(i), []).append(i)
    gs = sorted("[" + ",".join(str(i) for i in sorted(v)) + "]" for v in groups.values())
    # every probe is added, so nothing is ever missing on this side
    return "".join(gs) + " missing[[]]"


# ------------------------------------------------------------------ the runners
def run_reference(case, atoms=None):
    try:
        r = subprocess.run(
            [str(XMULTI / "target" / "debug" / "xmulti")],
            input=case.spec(atoms),
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s")
    if r.returncode != 0:
        return ("ERROR", r.stderr.strip().splitlines()[-1] if r.stderr else "?")
    for line in r.stdout.splitlines():
        if line.startswith("PARTITION "):
            return ("OK", line[len("PARTITION "):].strip())
    return ("ERROR", "no PARTITION line")


def run_encoding(case, atoms=None, keep=None):
    prog = egg_program(case, atoms)
    path = keep or (ROOT / "xdiff-tmp.egg")
    path.write_text(prog)
    try:
        r = subprocess.run(
            [str(EGGLOG), str(path)],
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT,
            cwd=ROOT,
        )
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s (program kept at {path})")
    if r.returncode != 0:
        err = [l for l in r.stderr.splitlines() if "ERROR" in l]
        msg = err[-1] if err else r.stderr.strip()[:400]
        return ("ERROR", f"{msg}\n    (program kept at {path})")
    return ("OK", parse_same_class(r.stdout, len(case.probes)))


# ------------------------------------------------------------------ the checks
def check_case(case, verbose=False, stats=None):
    """Returns a list of failure strings (empty when the case agrees).

    `stats` accumulates counters: how many cases had a usable baseline, and of
    those, how many had the rule actually change something -- a case where the
    rule never fires tests nothing about matching.
    """
    fails = []
    if stats is None:
        stats = {}

    # 1. machinery baseline: no rule, both sides must already agree
    bare = Case(case.name, case.terms, case.unions, [], None, case.probes, case.rounds)
    rs, rv = run_reference(bare, atoms=[])
    es, ev = run_encoding(bare, atoms=[])
    if rs == "TIMEOUT" or es == "TIMEOUT":
        return [f"{case.name}: baseline timeout ref={rs} enc={es}"]
    if rs != "OK" or es != "OK":
        return [f"{case.name}: baseline crashed ref={rs}:{rv} enc={es}:{ev}"]
    if rv != ev:
        return [f"{case.name}: BASELINE differs (machinery, not matching)\n"
                f"    ref {rv}\n    enc {ev}"]

    stats["baseline_ok"] = stats.get("baseline_ok", 0) + 1
    baseline = rv

    # 2. the rule, in the written atom order
    rs, rv = run_reference(case)
    es, ev = run_encoding(case)
    if rs == "OK" and rv != baseline:
        stats["fired"] = stats.get("fired", 0) + 1
    if rs == "TIMEOUT" or es == "TIMEOUT":
        return [f"{case.name}: rule timeout ref={rs} enc={es}"]
    if rs != "OK":
        return [f"{case.name}: reference crashed: {rv}"]
    if es != "OK":
        fails.append(f"{case.name}: encoding crashed: {ev}")
        return fails
    if rv != ev:
        fails.append(f"{case.name}: MISMATCH vs reference\n"
                     f"    ref {rv}\n    enc {ev}")

    # 3. order independence, both sides. Every permutation for 2-3 atoms; a
    # sample beyond that, since each one costs a full saturation on both sides.
    if len(case.atoms) > 1:
        perms = list(itertools.permutations(case.atoms))
        if len(perms) > PERM_CAP:
            perms = random.Random(0).sample(perms, PERM_CAP)
        ref_vals, enc_vals = {rv}, {ev}
        for p in perms:
            xs, x = run_reference(case, atoms=list(p))
            ys, y = run_encoding(case, atoms=list(p))
            # A timeout or crash is not a partition; folding it into the value
            # set would report spurious order dependence.
            if xs == "OK":
                ref_vals.add(x)
            if ys == "OK":
                enc_vals.add(y)
        if len(ref_vals) > 1:
            fails.append(f"{case.name}: REFERENCE is order dependent: {sorted(ref_vals)}")
        if len(enc_vals) > 1:
            fails.append(f"{case.name}: ENCODING is order dependent: {sorted(enc_vals)}")

    if verbose and not fails:
        print(f"  ok  {case.name}  {rv}")
    return fails


# ------------------------------------------------------------- curated corpus
V0, V1, V2 = ("var", 0), ("var", 1), ("var", 2)
NUL = ("null",)


def curated():
    cs = []

    # C1 -- plain repeated variable, live slots
    cs.append(Case(
        "C1-repeat-live",
        [("f", V0, V1), ("f", V0, V0)],
        [],
        [("p", "f", "x", "x")],
        ("p", "h", "x", "x"),
        [("f", V0, V1), ("f", V0, V0), ("h", V0, V0)],
    ))

    # C2 -- chain
    cs.append(Case(
        "C2-chain",
        [("f", V0, ("g", V0, V1))],
        [],
        [("p", "f", "a", "b"), ("b", "g", "c", "d")],
        ("p", "h", "c", "d"),
        [("f", V0, ("g", V0, V1)), ("h", V0, V1), ("h", V1, V0)],
    ))

    # C3 -- join on two shared variables
    cs.append(Case(
        "C3-join",
        [("f", V0, V1), ("g", V0, V1)],
        [],
        [("p", "f", "x", "y"), ("q", "g", "x", "y")],
        ("p", "h", "x", "y"),
        [("f", V0, V1), ("g", V0, V1), ("h", V0, V1)],
    ))

    # C4 -- symmetry: the two occurrences agree only through a swap
    cs.append(Case(
        "C4-symmetry",
        [("f", ("k", V0, V1), ("k", V1, V0))],
        [(("k", V0, V1), ("k", V1, V0))],
        [("p", "f", "x", "x")],
        ("p", "h", "x", "x"),
        [("f", ("k", V0, V1), ("k", V1, V0)), ("h", ("k", V0, V1), ("k", V0, V1))],
    ))

    # C5 -- R1: one redundant-slot node reached through two atoms
    cs.append(Case(
        "C5-redundant-same-node",
        [("add", NUL, NUL)],
        [(("sub", V0, V0), NUL)],
        [("p", "add", "a", "b"), ("a", "sub", "u", "u"), ("b", "sub", "u", "u")],
        ("p", "h", "u", "u"),
        [("add", NUL, NUL), ("h", V0, V0), NUL],
    ))

    # C6 -- R2: two different redundant-slot nodes, ?u forced across them
    cs.append(Case(
        "C6-redundant-two-nodes",
        [("add", NUL, NUL)],
        [(("sub", V0, V0), NUL), (("sub2", V1, V1), NUL)],
        [("p", "add", "a", "b"), ("a", "sub", "u", "u"), ("b", "sub2", "u", "u")],
        ("p", "h", "u", "u"),
        [("add", NUL, NUL), ("h", V0, V0), NUL],
    ))

    # C7 -- same, but the two atoms use DISTINCT variables
    cs.append(Case(
        "C7-redundant-distinct-vars",
        [("add", NUL, NUL)],
        [(("sub", V0, V0), NUL), (("sub2", V1, V1), NUL)],
        [("p", "add", "a", "b"), ("a", "sub", "u", "u"), ("b", "sub2", "v", "v")],
        ("p", "h", "u", "v"),
        [("add", NUL, NUL), ("h", V0, V0), ("h", V0, V1), NUL],
    ))

    # C8 -- a variable reached by two different paths, no redundancy
    cs.append(Case(
        "C8-two-paths",
        [("f", ("g", V0, V1), ("k", V0, V1))],
        [],
        [("p", "f", "a", "b"), ("a", "g", "x", "y"), ("b", "k", "x", "y")],
        ("p", "h", "x", "y"),
        [("f", ("g", V0, V1), ("k", V0, V1)), ("h", V0, V1), ("h", V1, V0)],
    ))

    # C9 -- redundancy meeting a live slot
    cs.append(Case(
        "C9-redundancy-and-live",
        [("f", V0, V1)],
        [(("g", V0, V1), ("g", V0, V2))],
        [("p", "f", "x", "y"), ("q", "g", "x", "y")],
        ("p", "h", "x", "y"),
        [("f", V0, V1), ("g", V0, V1), ("h", V0, V1)],
    ))

    # C10 -- three atoms, chain then join (the M5 shape)
    cs.append(Case(
        "C10-chain-then-join",
        [("f", V0, ("g", V0, V1)), ("k", V0, V0)],
        [],
        [("p", "f", "a", "b"), ("b", "g", "c", "d"), ("q", "k", "c", "a")],
        ("p", "h", "c", "d"),
        [("f", V0, ("g", V0, V1)), ("k", V0, V0), ("h", V0, V1)],
    ))

    # C11 -- regression for the action bug, found by `fuzz 150 2024` as fuzz56.
    #
    # The compiled action used to emit a plain `(union root built)`, which
    # asserts an equation whose two renamings are the identity. The root's
    # renaming here is {0->3, 2->2}, so that equation was false: it conflated
    # slot 0 with slot 3. The e-graph absorbed it as spurious redundancy -- the
    # `(Var 0)` class went from 1 live slot to 0 -- and child-update then emptied
    # every edge, collapsing h(x,y) with h(x,x). The reference refuses that, and
    # is right to: Def. 8 makes each lookup's renaming injective, so a node with
    # two distinct slots cannot represent h(x,x) (the crate pins this as
    # `regress::same_node_redundant_slots_stay_distinct`).
    #
    # It was also the only order-dependent case in 150, which fits: the two atoms
    # share no variable, so one of them mints, and the root's renaming -- hence
    # how wrong the union was -- depended on which atom went first.
    #
    # Worth knowing for the next such hunt: a `BadEdge` width check does NOT
    # catch this, because by the end the children's classes have gone slotless
    # too and the widths agree again.
    cs.append(Case(
        "C11-action-renamed-id-union",
        [NUL],
        [(("g", ("sub2", NUL, NUL), ("sub", V1, V0)), NUL),
         (("add", ("k", V2, NUL), ("k", V0, NUL)), V0)],
        [("x3", "k", "x1", "x2"), ("x6", "k", "x4", "x5"), ("x7", "add", "x3", "x6")],
        ("x7", "h", "x3", "x6"),
        [NUL, ("g", ("sub2", NUL, NUL), ("sub", V1, V0)),
         ("add", ("k", V2, NUL), ("k", V0, NUL)),
         ("h", V0, V1), ("h", V0, V0), NUL, V0],
        rounds=6,
    ))

    return cs


# ------------------------------------------------------------------- the fuzzer
def rand_term(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return rng.choice([("var", rng.randrange(3)), ("null",)])
    op = rng.choice(BINOPS)
    return (op, rand_term(rng, depth - 1), rand_term(rng, depth - 1))


def flatten_to_atoms(t, ctr):
    """Flatten a term into depth-1 atoms with fresh pvars, so the resulting
    multipattern is guaranteed to match that term. Leaves become bare pvars,
    which is what a multipattern does with them anyway."""
    if t[0] in ("var", "null"):
        ctr[0] += 1
        return f"x{ctr[0]}", []
    op, a, b = t
    pa, aa = flatten_to_atoms(a, ctr)
    pb, ab = flatten_to_atoms(b, ctr)
    ctr[0] += 1
    root = f"x{ctr[0]}"
    return root, aa + ab + [(root, op, pa, pb)]


def rand_case(rng, i):
    # A small term set over few ops, so patterns and terms collide often.
    terms = [rand_term(rng, rng.randrange(1, 3)) for _ in range(rng.randrange(1, 3))]

    # Unions biased towards creating redundancy: equating a term that has slots
    # with one that has fewer forces the difference to become redundant, which
    # is where matching gets interesting.
    unions = []
    for _ in range(rng.randrange(0, 3)):
        a = rand_term(rng, rng.randrange(1, 3))
        if rng.random() < 0.5 and slots(a):
            b = ("null",) if rng.random() < 0.5 else ("var", 0)
        else:
            b = rand_term(rng, rng.randrange(0, 2))
        unions.append((a, b))

    # The pattern is read off a term that is actually in the e-graph, so it
    # matches by construction; then it is perturbed.
    seed_term = rng.choice(terms + [a for a, _ in unions])
    _, atoms = flatten_to_atoms(seed_term, [0])
    if not atoms:
        atoms = [("r0", rng.choice(BINOPS), "u", "v")]

    pvs = sorted({v for at in atoms for v in (at[2], at[3])})
    # perturb: identify two child pvars (tests repeated-variable semantics)
    if pvs and rng.random() < 0.6:
        keep, drop = rng.choice(pvs), rng.choice(pvs)
        atoms = [(r, o, keep if c1 == drop else c1, keep if c2 == drop else c2)
                 for (r, o, c1, c2) in atoms]
    # perturb: drop a trailing atom (leaves a pvar unconstrained)
    if len(atoms) > 1 and rng.random() < 0.3:
        atoms = atoms[:-1]
    # perturb: swap an atom's children
    if rng.random() < 0.3:
        j = rng.randrange(len(atoms))
        r, o, c1, c2 = atoms[j]
        atoms[j] = (r, o, c2, c1)

    allv = sorted({v for at in atoms for v in (at[0], at[2], at[3])})
    # the action's root must be an atom root, so it is bound
    action = (atoms[-1][0], "h", rng.choice(allv), rng.choice(allv))

    probes = terms + [a for a, _ in unions] + [
        ("h", V0, V1), ("h", V0, V0), ("null",), ("var", 0)]
    return Case(f"fuzz{i}", terms, unions, atoms, action, probes, rounds=6)


# ------------------------------------------------------------------------ main
def main():
    args = sys.argv[1:]
    if args and args[0] == "show":
        # ./xdiff.py show <index> <seed> [perm...]  -- dump one fuzz case
        i, seed = int(args[1]), int(args[2] if len(args) > 2 else 0)
        rng = random.Random(seed)
        case = [rand_case(rng, k) for k in range(i + 1)][i]
        order = [int(x) for x in args[3:]] or list(range(len(case.atoms)))
        atoms = [case.atoms[k] for k in order]
        print("=== spec ===")
        print(case.spec(atoms), end="")
        # its own scratch file, so `show` can be used while a sweep is running
        keep = ROOT / f"xdiff-show-{i}.egg"
        print("=== reference ===", run_reference(case, atoms))
        print("=== encoding  ===", run_encoding(case, atoms, keep=keep))
        print("=== rule ===")
        print(compile_rule(atoms, case.action))
        return 0
    if args and args[0] == "fuzz":
        n = int(args[1]) if len(args) > 1 else 100
        seed = int(args[2]) if len(args) > 2 else 0
        rng = random.Random(seed)
        cases = [rand_case(rng, i) for i in range(n)]
    else:
        cases = curated()

    # Categories, most-interesting last: a baseline difference is the machinery
    # disagreeing before any rule runs, so it says nothing about matching.
    cats = {
        "timeout (excluded)": ["timeout"],
        "harness/crash": ["crashed"],
        "machinery baseline": ["BASELINE differs"],
        "order dependence": ["order dependent"],
        "MATCHING mismatch": ["MISMATCH vs reference"],
    }
    counts = {k: 0 for k in cats}
    stats = {}
    all_fails, ok = [], 0
    for c in cases:
        fs = check_case(c, verbose=True, stats=stats)
        if fs:
            all_fails += fs
            for f in fs:
                print("FAIL " + f)
                for k, pats in cats.items():
                    if any(p in f for p in pats):
                        counts[k] += 1
                        break
        else:
            ok += 1

    print(f"\n{ok}/{len(cases)} cases agree")
    for k in cats:
        print(f"  {counts[k]:>4}  {k}")
    b, f = stats.get("baseline_ok", 0), stats.get("fired", 0)
    print(f"\n  {b}/{len(cases)} had a usable baseline (matching was compared)")
    print(f"  {f}/{b} of those had the rule actually change the partition")
    if all_fails:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
