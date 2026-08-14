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
import os
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

# Past bugs, re-introducible so the corpus can be checked for still catching
# them. A bug nothing fails under is a bug that could come back unnoticed.
#   XDIFF_BUGS=root-only   an atom's renaming solved from its root alone
#   XDIFF_BUGS=slot-late   a slot literal checked after the renaming, not with it
#   XDIFF_BUGS=unordered   atoms compiled in the order written
#   XDIFF_BUGS=binder-1st  the first atom is allowed to be a binder
#   XDIFF_BUGS=union-id    the action unions classes instead of invocations
BUGS = {b for b in os.environ.get("XDIFF_BUGS", "").split(",") if b}

# How often a generated subterm is a binder. Raise it to search binder-heavy
# ground: XDIFF_LAM=0.55
LAM_PROB = float(os.environ.get("XDIFF_LAM", "0.2"))

# ---------------------------------------------------------------- neutral terms
# term := ('var', n) | ('null',) | (op, t1, t2)


def slots(t):
    if t[0] == "var":
        return {t[1]}
    if t[0] == "null":
        return set()
    if t[0] == "lam":
        return slots(t[2]) - {t[1][1]}      # the bound slot is not free
    return slots(t[1]) | slots(t[2])


def sexpr(t):
    """Reference/spec syntax."""
    if t[0] == "var":
        return f"(var ${t[1]})"
    if t[0] == "null":
        return "null"
    if t[0] == "lam":
        return f"(lam ${t[1][1]} {sexpr(t[2])})"
    return f"({t[0]} {sexpr(t[1])} {sexpr(t[2])})"


def enc_op(op):
    """The operator name the encoding uses. The machinery's alpha-equivalence
    rule is written against the literal string "lambda", so the binder has a
    different name on each side."""
    return "lambda" if op == "lam" else op


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
    if t[0] == "lam":
        # The body's edge is the identity on the body's slots -- which still
        # contains the bound slot, since the lambda *node* carries it and only
        # the class drops it.
        x, body = t[1][1], t[2]
        return (f'(App "lambda" {mapof({0: x})} (Var 0) '
                f"{mapof(edge(body))} {enc(body)})")
    op, a, b = t
    return f'(App "{enc_op(op)}" {mapof(edge(a))} {enc(a)} {mapof(edge(b))} {enc(b)})'


def shift_term(t, k):
    """Add `k` to every slot in a term."""
    if t[0] == "var":
        return ("var", t[1] + k)
    if t[0] == "null":
        return t
    if t[0] == "lam":
        return ("lam", shift_term(t[1], k), shift_term(t[2], k))
    return (t[0], shift_term(t[1], k), shift_term(t[2], k))


def shift_case(case, k):
    """The same case with every slot in the program renamed by `+k`.

    Slot names carry no meaning, so this must not change any answer. It is a
    per-side property, needing no cross-system comparison, and it is a different
    question from agreeing with the reference: a side could be consistently wrong
    and still shift-invariant, or right on one naming and wrong on another. The
    reference's own suite checks it (`props.rs`).
    """
    return Case(case.name, [shift_term(t, k) for t in case.terms],
                [(shift_term(a, k), shift_term(b, k)) for a, b in case.unions],
                case.atoms, case.action,
                [shift_term(t, k) for t in case.probes], case.rounds)


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


def check_encodable(case):
    """Reject a case the encoding cannot represent faithfully.

    A `U` value is an e-node, not an invocation, so a bare `(var $k)` at top level
    encodes as `(Var 0)` for every k -- the slot is lost. Such a case is not a
    faithful translation, and it is not shift-equivalent either, since shifting
    changes what it means on one side only. Slots inside a compound term ride in
    the stored edges and are fine; `null` has no slot to lose.

    This has been mistaken for a machinery bug twice. Use a compound term with the
    same slots instead -- `LEAF0` below.
    """
    tops = list(case.terms) + list(case.probes)
    for a, b in case.unions:
        tops += [a, b]
    bad = [t for t in tops if t[0] == "var"]
    if bad:
        raise AssertionError(
            f"{case.name}: bare leaf at top level {bad} -- the encoding cannot "
            f"carry its slot; use a compound term with the same slots")


# -------------------------------------------------------------- rule compiler
def order_atoms(atoms):
    """Reorder so every atom after the first shares a variable with the prefix.

    Required, not an optimisation. An atom sharing nothing has no constraint on
    its `mp`, so every slot it needs is *minted* -- and the mint is a commitment
    the encoding cannot revisit. If a later atom then shows that a minted slot is
    really one the pattern already named, the two disagree and `find-mapping`
    fails, losing a match the reference finds. `multi_ematch` does not have this
    problem: it keeps such a slot flexible and lets `unify` merge it later.

    The first atom fixes slots(pattern), so it must not be a binder: a binder's
    node carries the *bound* slot, which would put a bound slot into the pattern's
    slot space and stop the rule firing. `C13` is the case. Otherwise the caller's
    preference is kept, since callers vary the first atom deliberately.
    """
    atoms = list(atoms)
    if "unordered" in BUGS:
        return atoms
    if "binder-1st" not in BUGS:
        first = next((j for j, a in enumerate(atoms) if a[1] != "lam"), 0)
        atoms = [atoms[first]] + atoms[:first] + atoms[first + 1:]

    rest = list(atoms[1:])
    out = [atoms[0]]
    seen = pvars_of(atoms[0])
    while rest:
        i = next((j for j, a in enumerate(rest)
                  if pvars_of(a) & seen), 0)
        a = rest.pop(i)
        out.append(a)
        seen |= pvars_of(a)
    return out


def pvars_of(atom):
    """An atom's pattern variables. A slot literal is excluded: its constraint is
    an equality on one slot, applied after `mp` is solved, so it does not help
    pin `mp` down and does not count as connectivity."""
    return {v for v in (atom[0], atom[2], atom[3]) if not v.startswith("$")}


def compile_rule(atoms, action):
    """Compile a flattened multipattern into an egglog rule body + action.

    Atoms are processed in the given order. Each atom's `mp` is solved from
    EVERY constraint available at that point -- its root if already bound, and
    every child bound by an earlier atom -- with `find-mapping-total` so slots
    the constraints do not reach are minted rather than dropped.
    """
    atoms = order_atoms(atoms)
    body, uid = [], [0]

    def fresh(p):
        uid[0] += 1
        return f"{p}{uid[0]}"

    mp_of = {}      # pvar -> egglog var holding its renaming into slots(pattern)
    cls_of = {}     # pvar -> egglog var holding its leader
    slot_of = {}    # "$v" -> egglog i64 var holding that pattern slot
    pat = None      # identity on slots(pattern)

    for idx, (root, op, c1, c2) in enumerate(atoms):
        e1, e2 = fresh("p"), fresh("p")
        rv = cls_of.setdefault(root, fresh("V"))
        # A child written `$v` is a slot literal, not a pattern variable. The
        # encoding stores a binder's slot as an edge to `(Var 0)`, so the child
        # position is that literal class and the slot itself is read out of the
        # edge below.
        kids = []
        for cp in (c1, c2):
            kids.append("(Var 0)" if cp.startswith("$")
                        else cls_of.setdefault(cp, fresh("C")))
        body.append(f'(= {rv} (App "{enc_op(op)}" {e1} {kids[0]} {e2} {kids[1]}))')

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
            if cp.startswith("$"):
                continue
            if "root-only" in BUGS:
                continue
            if cp in bound_before:
                mx = mp_of[cp]
                sym = fresh("sym")
                body.append(f"(RenamesToLeader {cls_of[cp]} {sym} {cls_of[cp]})")
                firsts.append(f"(compose {mx} {sym})")
                seconds.append(e)

        # A slot literal an earlier atom already pinned constrains this atom's mp
        # too: `mp . edge = {0 -> that slot}`. Checking it afterwards instead is
        # too late -- mp would already have minted a different slot for the same
        # binder, and nothing can revise a mint.
        for cp, e in ((c1, e1), (c2, e2)):
            if cp.startswith("$") and cp in slot_of and "slot-late" not in BUGS:
                firsts.append(f"(map-insert (map-empty) 0 {slot_of[cp]})")
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

        # Accumulate the avoid-set. Passing only the initial atom's slots would
        # let two atoms that both mint choose the same slot, since the primitive
        # is pure and sees one atom at a time. `compose m (inverse m)` is the
        # identity on im(m), and identity maps never conflict under map-union, so
        # the running union is always well defined.
        idm = fresh("idm")
        body.append(f"(= {idm} (compose {mp} (inverse {mp})))")
        if idx == 0:
            pat = idm
        else:
            nxt = fresh("av")
            body.append(f"(= {nxt} (map-union {pat} {idm}))")
            pat = nxt

        # A slot literal names one slot in pattern space. `(= v ...)` binds it on
        # first use and constrains it on every later one, which is how the same
        # `$v` written twice forces the two slots to agree.
        for cp, e in ((c1, e1), (c2, e2)):
            if cp.startswith("$"):
                sv = slot_of.setdefault(cp, "s" + cp[1:])
                body.append(f"(= {sv} (map-get (compose {mp} {e}) 0))")

        # walk the children: bind the new ones, check the ones bound in THIS atom
        for cp, e in ((c1, e1), (c2, e2)):
            if cp.startswith("$"):
                continue
            if cp in mp_of:
                # A child bound by an EARLIER atom is already handled: it went
                # into the renaming as a constraint, so the equation holds by
                # construction. One bound in THIS atom still needs checking.
                # Under `root-only` the constraint was skipped, so the check is
                # what the original bug had in its place -- emitting neither
                # would be a different, more permissive mutant.
                if cp not in bound_before or "root-only" in BUGS:
                    sym = fresh("sym")
                    body.append(
                        f"(= {sym} (compose (inverse {mp_of[cp]}) (compose {mp} {e})))"
                    )
                    body.append(f"(RenamesToLeader {cls_of[cp]} {sym} {cls_of[cp]})")
                    # A redundant slot is recorded as a *partial* self-loop, so
                    # the stored set is an inverse monoid, not a group. If the
                    # composition above truncated, the short map could match one
                    # of those partial loops and be accepted wrongly. Requiring
                    # the width to be unchanged rules that out without depending
                    # on the e-graph being saturated -- which matters here,
                    # because user rules share a ruleset with the machinery and
                    # so can match mid-repair.
                    body.append(
                        f"(= (map-length {sym}) (map-length {mp_of[cp]}))"
                    )
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
    if op == "=":
        # Equate two variables. Both carry a renaming into pattern slots and
        # neither need be the identity, which is the one action egglog's `union`
        # cannot express: it would assert the equation at the identity. Solve
        # instead -- from mr*Root = ma*A follows Root = (mr^-1 . ma) * A.
        return ("(rule (" + "\n       ".join(body) + ")\n"
                f"      ((RenamesToLeader {cls_of[root]} "
                f"(compose (inverse {mr}) {mp_of[a]}) {cls_of[a]})))")
    if "union-id" in BUGS:
        act = (f'(union {cls_of[root]} (App "{enc_op(op)}" '
               f"{mp_of[a]} {cls_of[a]} {mp_of[b]} {cls_of[b]}))")
    else:
        act = (
            f'(let _hn (App "{enc_op(op)}" {mp_of[a]} {cls_of[a]} {mp_of[b]} {cls_of[b]}))\n'
            f"       (RenamesToLeader _hn {mr} {cls_of[root]})"
        )
    return "(rule (" + "\n       ".join(body) + f")\n      ({act}))"


# -------------------------------------------------------------- egg generation
def egg_program(case, atoms=None, mult=3):
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
    out.append(f"(run {case.rounds * mult})")
    for i, _ in enumerate(case.probes):
        out.append(f"(ProbeId _p{i} {i})")
    out.append(f"(run {case.rounds * mult})")
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
    part, sat = None, True
    for line in r.stdout.splitlines():
        if line.startswith("PARTITION "):
            part = line[len("PARTITION "):].strip()
        elif line.startswith("SATURATED "):
            sat = line.split()[1] == "yes"
    if part is None:
        return ("ERROR", "no PARTITION line")
    return ("OK" if sat else "UNSATURATED", part)


def run_encoding(case, atoms=None, keep=None, mult=3):
    prog = egg_program(case, atoms, mult)
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
    check_encodable(case)

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
    if rs == "UNSATURATED":
        return [f"{case.name}: unsaturated, excluded (reference hit its round cap)"]
    if rs != "OK":
        return [f"{case.name}: reference crashed: {rv}"]
    if es != "OK":
        fails.append(f"{case.name}: encoding crashed: {ev}")
        return fails
    if rv != ev:
        fails.append(f"{case.name}: MISMATCH vs reference\n"
                     f"    ref {rv}\n    enc {ev}")

    # 3. did both sides reach a fixpoint? If not, they ran different amounts of
    # work and comparing them says nothing, so the case is excluded. The
    # reference reports this itself; the encoding is checked by running twice as
    # many iterations and requiring the same answer -- which doubles as a
    # determinism check.
    ds, dv = run_encoding(case, mult=6)
    if rs == "UNSATURATED" or ds == "UNSATURATED":
        return [f"{case.name}: unsaturated, excluded (ref={rs} enc={ds})"]
    if ds == "OK" and dv != ev:
        return [f"{case.name}: unsaturated or nondeterministic in the encoding\n"
                f"    {case.rounds * 3} iterations {ev}\n"
                f"    {case.rounds * 6} iterations {dv}"]

    # 4. order independence, both sides. Every distinct reordering for 2-3 atoms;
    # a sample beyond that, since each costs a full saturation on both sides. The
    # original order is excluded -- rerunning it would test determinism, not order.
    if len(case.atoms) > 1:
        perms = [p for p in itertools.permutations(case.atoms)
                 if list(p) != list(case.atoms)]
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

    # 5. slot-renaming invariance: shifting every slot in the program must not
    # change either side's answer.
    shifted = shift_case(case, 40)
    xs, xv = run_reference(shifted)
    ys, yv = run_encoding(shifted)
    if xs == "OK" and xv != rv:
        fails.append(f"{case.name}: REFERENCE is not slot-renaming invariant\n"
                     f"    as written {rv}\n    slots +40  {xv}")
    if ys == "OK" and yv != ev:
        fails.append(f"{case.name}: ENCODING is not slot-renaming invariant\n"
                     f"    as written {ev}\n    slots +40  {yv}")

    if verbose and not fails:
        print(f"  ok  {case.name}  {rv}")
    return fails


# ------------------------------------------------------------- curated corpus
V0, V1, V2 = ("var", 0), ("var", 1), ("var", 2)
# A compound term whose only slot is V0, for the top-level positions
# where a bare leaf would lose its slot (see check_encodable).
LEAF0 = ("sub", V0, V0)
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
         (("add", ("k", V2, NUL), ("k", V0, NUL)), LEAF0)],
        [("x3", "k", "x1", "x2"), ("x6", "k", "x4", "x5"), ("x7", "add", "x3", "x6")],
        ("x7", "h", "x3", "x6"),
        [NUL, ("g", ("sub2", NUL, NUL), ("sub", V1, V0)),
         ("add", ("k", V2, NUL), ("k", V0, NUL)),
         ("h", V0, V1), ("h", V0, V0), NUL, LEAF0],
        rounds=6,
    ))

    # C12 -- regression for atom ordering, found by `fuzz 250 555` as fuzz61.
    #
    # As written, atom 2 shares no variable with atom 1, so nothing constrains
    # its mp and every slot it needs is minted. Atom 3 then shows that k2's slot
    # 0 and k1's slot 0 are the *same* slot of the h node, while the mint had
    # already sent them to different pattern slots -- the constraints conflict,
    # find-mapping fails, and a match the reference finds is lost.
    #
    # Reordering to atom 1, atom 3, atom 2 keeps every atom connected to the
    # prefix, so nothing is minted and the match comes back. `multi_ematch` never
    # had the problem: it keeps such a slot flexible and lets `unify` merge it.
    cs.append(Case(
        "C12-atom-order-must-stay-connected",
        [("h", ("k", V0, V0), ("k", V2, V0))],
        [],
        [("x3", "k", "x1", "x2"), ("x6", "k", "x4", "x5"), ("x7", "h", "x3", "x6")],
        ("x7", "h", "x2", "x4"),
        [("h", ("k", V0, V0), ("k", V2, V0)), ("h", V0, V1), ("h", V0, V0),
         NUL, LEAF0],
        rounds=6,
    ))

    # C13 -- a three-atom body mixing a binder, a chain and a join.
    #
    # Found as a witness that the first atom must not be a binder, and
    # `order_atoms` still avoids choosing one. It is NOT that witness any more,
    # and probably never was a clean one: its discrimination came from a union
    # whose operand was a bare leaf, which the encoding cannot represent
    # faithfully. With the leaf replaced no ordering disagrees, and 200
    # binder-dense generated cases with the restriction lifted found nothing. The
    # restriction is kept as conservative -- a bound slot in the pattern's slot
    # space is a real oddity, see open question 3 -- but it is unwitnessed.
    cs.append(Case(
        "C13-binder-chain-and-join",
        [("h", ("k", V2, NUL), ("lam", V0, V1))],
        [(("g", ("h", V2, NUL), ("lam", V2, V1)), LEAF0),
         (("h", NUL, V2), ("add", NUL, NUL))],
        [("x3", "k", "x1", "x2"), ("x5", "lam", "$s5", "x4"),
         ("x6", "h", "x3", "x5")],
        ("x6", "h", "x4", "x4"),
        [("h", ("k", V2, NUL), ("lam", V0, V1)),
         ("g", ("h", V2, NUL), ("lam", V2, V1)),
         ("h", NUL, V2), ("h", V0, V1), ("h", V0, V0), NUL, LEAF0],
        rounds=6,
    ))

    # ---- ported from the reference's own test suite (tests/multipat) ----------
    # Where a test is not portable, it is listed under "Not ported" in
    # slotted-user-rules.md rather than approximated here.

    # regress::same_node_redundant_slots_stay_distinct. Unioning f's two-slot
    # term into a slotless one makes both slots redundant. A pattern that would
    # have to identify them must not match; one that keeps them apart must.
    red = [(("f", V0, V1), NUL)]
    cs.append(Case(
        "P1a-redundant-slots-may-not-collapse",
        [NUL], red,
        [("p", "f", "a", "a")], ("p", "h", "a", "a"),
        [NUL, ("f", V0, V1), ("h", V0, V0), ("h", V0, V1)],
    ))
    cs.append(Case(
        "P1b-redundant-slots-kept-apart",
        [NUL], red,
        [("p", "f", "a", "b")], ("p", "h", "a", "b"),
        [NUL, ("f", V0, V1), ("h", V0, V0), ("h", V0, V1)],
    ))

    # regress::live_slots_of_one_class_stay_distinct. Same question with no
    # redundancy at all: a class's own live slots are distinct.
    cs.append(Case(
        "P2a-live-slots-may-not-collapse",
        [("k", V0, V1)], [],
        [("p", "k", "u", "u")], ("p", "h", "u", "u"),
        [("k", V0, V1), ("h", V0, V0), ("h", V0, V1)],
    ))
    cs.append(Case(
        "P2b-live-slots-kept-apart",
        [("k", V0, V1)], [],
        [("p", "k", "u", "v")], ("p", "h", "u", "v"),
        [("k", V0, V1), ("h", V0, V0), ("h", V0, V1)],
    ))

    # C14 -- regression for `union-id`, found by mutation testing after C11
    # stopped catching it. The action's root is a CHILD variable, so its renaming
    # is the stored edge {$0 -> $2} rather than the identity, and unioning
    # classes instead of invocations asserts a different equation.
    #
    # C11 was the original witness for this and no longer discriminates: after
    # minting changed to smallest-unused, C11's root renaming came out as the
    # identity, where the two spellings agree. Kept as a lesson -- a case written
    # against one policy can quietly stop testing what it was written for.
    cs.append(Case(
        "C14-action-root-with-a-nonidentity-renaming",
        [("f", V2, NUL), ("k", V2, NUL)],
        [(("g", V1, NUL), ("k", NUL, V0))],
        [("x3", "f", "x1", "x2")],
        ("x1", "h", "x3", "x2"),
        [("f", V2, NUL), ("k", V2, NUL), ("g", V1, NUL),
         ("h", V0, V1), ("h", V0, V0), NUL, LEAF0],
        rounds=6,
    ))

    # X1 -- KNOWN FAILING. Found by `fuzz 250 6161` as fuzz85, in the
    # over-deriving direction: the encoding merges h(x,y) with h(x,x), which the
    # reference refuses because a node whose two slots are distinct cannot
    # represent h(x,x) (Def. 8's per-lookup injectivity).
    #
    # The action asserts ?x1 = h(?x3, ?x1) -- a node equal to its own child --
    # which merges the h class into the variable class. BOTH sides assert that
    # and both merge; the difference is only that the reference still keeps
    # h(x,x) apart afterwards. The encoding finishes with an h node whose two
    # edges are identical, `{2->2}` and `{2->2}`, to the same child class.
    #
    # Not yet localised to either the action or the machinery's redundancy
    # handling. The baseline agrees, so the rule triggers it, but both sides make
    # the same assertion -- which points at how the e-graph absorbs it rather
    # than at how the rule was compiled.
    cs.append(Case(
        "X1-KNOWN-FAIL-over-merges-h-x-x",
        [("add", ("sub2", V0, V0), NUL)],
        [(("h", V0, V2), NUL)],
        [("x3", "h", "x1", "x2")],
        ("x1", "h", "x3", "x1"),
        [("add", ("sub2", V0, V0), NUL), ("h", V0, V2), ("h", V0, V1),
         ("h", V0, V0), NUL, ("sub", V0, V0)],
        rounds=6,
    ))

    # ---- branching in unify --------------------------------------------------
    # The reference's `unify` returns SEVERAL states when two invocations of one
    # class differ in two or more slots and more than one pairing is legal. A
    # primitive returns one answer and `find-mapping` takes the least, so this is
    # where the encoding could lose a match.
    #
    # `f(k(v0,v1), g(v0,v1))` unioned into `null` makes both of f's slots
    # redundant, so every lookup mints new names for them; two atoms over that
    # node see two different pairs, and `?x` must be unified across them with two
    # candidate pairings. The second children are bound to DIFFERENT variables so
    # which pairing was taken is visible in the action.
    #
    # Both sides agree here, so this does not force the difference -- see the
    # doc. Kept because it exercises the shape.
    BR = ("f", ("k", V0, V1), ("g", V0, V1))
    cs.append(Case(
        "U1-two-pairings-across-two-lookups",
        [BR], [(BR, NUL)],
        [("p", "f", "x", "y"), ("q", "f", "x", "z")],
        ("p", "h", "y", "z"),
        [BR, NUL, ("h", ("g", V0, V1), ("g", V0, V1)),
         ("h", ("g", V0, V1), ("g", V1, V0))],
    ))

    # ---- actions that equate two invocations ---------------------------------
    # `action <root> = <x> <x>` equates two pattern variables rather than building
    # a node, so both sides carry a renaming and neither need be the identity.

    # E1 -- equate the two CHILDREN of one node, so both are stored edges. This
    # asserts (var $1) = (var $2) -- the statement a top-level term cannot express
    # in the encoding, since a `U` value is a node rather than an invocation, but
    # an action can. It makes the variable class slotless.
    cs.append(Case(
        "E1-equate-two-children",
        [("f", V1, V2), ("f", V1, V1)], [],
        [("p", "f", "a", "b")], ("a", "=", "b", "b"),
        [("f", V1, V2), ("f", V1, V1), ("h", V0, V1), ("h", V0, V0)],
    ))

    # E2 -- the same, one atom deeper, through a chain.
    cs.append(Case(
        "E2-equate-through-a-chain",
        [("f", V0, ("k", V1, V2)), ("k", V1, V1)], [],
        [("p", "f", "a", "b"), ("b", "k", "c", "d")], ("c", "=", "d", "d"),
        [("f", V0, ("k", V1, V2)), ("k", V1, V1), ("k", V1, V2), ("h", V0, V0)],
    ))

    # E3 -- eta's shape: equate a binder with its own body, so one side is the
    # identity and the other carries the bound slot. Unsound as maths; the point
    # is that both sides derive the same thing from it.
    cs.append(Case(
        "E3-equate-binder-with-body",
        [("lam", V0, V0), ("f", V0, V1)], [],
        [("p", "lam", "$v", "b")], ("p", "=", "b", "b"),
        [("lam", V0, V0), ("f", V0, V1), ("f", V0, V0), ("h", V0, V0)],
    ))

    # ---- symmetries ----------------------------------------------------------
    # The encoding keeps a class's symmetries as self-loops in RenamesToLeader,
    # and a repeated variable is checked by computing the symmetry it would need
    # and looking it up. That only works if the stored set is CLOSED, not just a
    # set of generators: a lookup for a composite element has to succeed.
    #
    # `a` below has three slots and is given one 3-cycle. The parent then holds
    # `a` at the identity beside `a` at the cycle's SQUARE, which is never
    # unioned in, so `(f ?x ?x)` matches only if the square is stored too.
    A3 = ("k", ("g", V0, V1), V2)            # a, at the identity
    A3s = ("k", ("g", V1, V2), V0)           # a, under 0->1->2->0
    A3ss = ("k", ("g", V2, V0), V1)          # a, under the square of that
    cs.append(Case(
        "S1-symmetry-group-is-closed",
        [("f", A3, A3ss)], [(A3, A3s)],
        [("p", "f", "x", "x")], ("p", "h", "x", "x"),
        [("f", A3, A3ss), ("h", A3, A3), ("h", A3, A3s)],
    ))
    # control: without the 3-cycle there is no symmetry to find, so no match
    cs.append(Case(
        "S1b-no-symmetry-no-match",
        [("f", A3, A3ss)], [],
        [("p", "f", "x", "x")], ("p", "h", "x", "x"),
        [("f", A3, A3ss), ("h", A3, A3), ("h", A3, A3s)],
    ))

    # S2 -- symmetry and redundancy at once. A redundant slot is recorded as a
    # *partial* self-loop, so the self-loops are not a group but an inverse
    # monoid. The worry is a computed symmetry that came out short (composition
    # truncates) matching one of those partial maps and being accepted wrongly.
    # `a` keeps two live slots with a swap between them, and a third slot that a
    # union has made redundant. The parent holds `a` at the identity beside `a`
    # under the swap, so the match needs the real symmetry while a partial
    # self-loop is also present to be confused with it.
    Ar = ("k", ("g", V0, V1), V2)
    Arsw = ("k", ("g", V1, V0), V2)
    cs.append(Case(
        "S2-symmetry-beside-redundancy",
        [("f", Ar, Arsw)],
        [(Ar, Arsw), (Ar, ("k", ("g", V0, V1), NUL))],
        [("p", "f", "x", "x")], ("p", "h", "x", "x"),
        [("f", Ar, Arsw), ("h", Ar, Ar), ("h", Ar, Arsw)],
    ))

    # ---- binders -------------------------------------------------------------
    # The point of slotted e-graphs, and untested until now. `$v` is a slot
    # literal: the reference's `Bind` has no room for a pattern variable there.

    # B1 -- reading a binder's body, and chaining through it.
    cs.append(Case(
        "B1-binder-chain",
        [("lam", V0, ("f", V0, V1))], [],
        [("p", "lam", "$v", "b"), ("b", "f", "x", "y")],
        ("p", "h", "x", "y"),
        [("lam", V0, ("f", V0, V1)), ("h", V0, V1), ("h", V0, V0)],
    ))

    # B2 -- alpha-equivalence: two spellings of the identity function are one
    # class, so a rule matching one must fire for both.
    cs.append(Case(
        "B2-alpha-equivalent-binders",
        [("lam", V0, V0), ("lam", V1, V1)], [],
        [("p", "lam", "$v", "b")], ("p", "h", "b", "b"),
        [("lam", V0, V0), ("lam", V1, V1), ("h", V0, V0), ("h", V0, V1)],
    ))

    # B3 -- known_bugs::lambda_bug_reaches_the_goal_under_multipat. The pattern
    # writes `$x` for two binders that have nothing to do with each other. Each
    # equation looks its node up separately and gets its own name for that node's
    # bound slot, so setting both to `$x` constrains nothing and it matches --
    # which the nested matcher does not do.
    cs.append(Case(
        "B3-same-slot-literal-two-binders",
        [("f", ("lam", V0, V0), ("lam", V0, V0))], [],
        [("p", "f", "a", "b"), ("a", "lam", "$x", "c"), ("b", "lam", "$x", "d")],
        ("p", "h", "c", "d"),
        [("f", ("lam", V0, V0), ("lam", V0, V0)), ("h", V0, V0), ("h", V0, V1)],
    ))

    # B4 -- the same, with the two binders over different bodies.
    cs.append(Case(
        "B4-same-slot-literal-different-bodies",
        [("f", ("lam", V0, V0), ("lam", V0, ("f", V0, V1)))], [],
        [("p", "f", "a", "b"), ("a", "lam", "$x", "c"), ("b", "lam", "$x", "d")],
        ("p", "h", "c", "d"),
        [("f", ("lam", V0, V0), ("lam", V0, ("f", V0, V1))),
         ("h", V0, V0), ("h", V0, V1)],
    ))

    return cs


# ------------------------------------------------------------------- the fuzzer
def rand_term(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return rng.choice([("var", rng.randrange(3)), ("null",)])
    if rng.random() < LAM_PROB:
        return ("lam", ("var", rng.randrange(3)), rand_term(rng, depth - 1))
    op = rng.choice(BINOPS)
    return (op, rand_term(rng, depth - 1), rand_term(rng, depth - 1))


def flatten_to_atoms(t, ctr, rng=None):
    """Flatten a term into depth-1 atoms with fresh pvars, so the resulting
    multipattern is guaranteed to match that term. Leaves become bare pvars,
    which is what a multipattern does with them anyway."""
    if t[0] in ("var", "null"):
        ctr[0] += 1
        return f"x{ctr[0]}", []
    if t[0] == "lam":
        pb, ab = flatten_to_atoms(t[2], ctr, rng)
        ctr[0] += 1
        root = f"x{ctr[0]}"
        # a binder's slot must be a literal; reuse one sometimes, so that two
        # binders written with the same slot get exercised
        if rng is not None and rng.random() < 0.3:
            sl = "$s0"
        else:
            sl = f"$s{ctr[0]}"
        return root, ab + [(root, "lam", sl, pb)]
    op, a, b = t
    pa, aa = flatten_to_atoms(a, ctr, rng)
    pb, ab = flatten_to_atoms(b, ctr, rng)
    ctr[0] += 1
    root = f"x{ctr[0]}"
    return root, aa + ab + [(root, op, pa, pb)]


def rand_top(rng, depth):
    """A term safe to use at top level.

    A bare leaf cannot be encoded faithfully: an encoding `U` value is a *node*,
    not an invocation, so `(var $n)` collapses to `(Var 0)` and loses `n`. Then
    `union (var $0) (var $2)` -- a real statement about the variable class in the
    reference -- becomes a no-op in the encoding, and the two sides diverge for
    reasons that have nothing to do with matching. Slots inside a compound term
    ride in the stored edges and survive.
    """
    t = rand_term(rng, depth)
    if t[0] in ("var", "null"):
        t = (rng.choice(BINOPS), t, rand_term(rng, 0))
    return t


def rand_case(rng, i):
    # A small term set over few ops, so patterns and terms collide often.
    terms = [rand_top(rng, rng.randrange(1, 3)) for _ in range(rng.randrange(1, 3))]

    # Unions biased towards creating redundancy: equating a term that has slots
    # with one that has fewer forces the difference to become redundant, which
    # is where matching gets interesting.
    unions = []
    for _ in range(rng.randrange(0, 3)):
        a = rand_top(rng, rng.randrange(1, 3))
        if rng.random() < 0.5 and slots(a):
            # `LEAF0` rather than a bare `(var $0)`: a bare leaf loses its slot
            # (see check_encodable), and although slot 0 happens to survive, the
            # slot-renaming check shifts it to one that would not.
            b = ("null",) if rng.random() < 0.5 else LEAF0
        else:
            b = rand_top(rng, rng.randrange(0, 2))
        unions.append((a, b))

    # The pattern is read off a term that is actually in the e-graph, so it
    # matches by construction; then it is perturbed.
    seed_term = rng.choice(terms + [a for a, _ in unions])
    _, atoms = flatten_to_atoms(seed_term, [0], rng)
    if not atoms:
        atoms = [("r0", rng.choice(BINOPS), "u", "v")]

    # Perturbations make the pattern more interesting but often stop it matching
    # at all, and a case that never fires tests nothing. Half are left alone so
    # the sweep keeps a healthy share of firing cases.
    if rng.random() < 0.5:
        pvs = sorted({v for at in atoms for v in (at[2], at[3])
                      if not v.startswith("$")})
        # identify two child pvars (tests repeated-variable semantics)
        if pvs and rng.random() < 0.5:
            keep, drop = rng.choice(pvs), rng.choice(pvs)
            atoms = [(r, o, keep if c1 == drop else c1, keep if c2 == drop else c2)
                     for (r, o, c1, c2) in atoms]
        # drop a trailing atom (leaves a pvar unconstrained)
        if len(atoms) > 1 and rng.random() < 0.3:
            atoms = atoms[:-1]
        # swap an atom's children -- never a binder's, whose slot has to stay
        # first: `(lam ?x $s)` is not valid syntax on the reference side.
        swappable = [j for j, a in enumerate(atoms) if a[1] != "lam"]
        if swappable and rng.random() < 0.4:
            j = rng.choice(swappable)
            r, o, c1, c2 = atoms[j]
            atoms[j] = (r, o, c2, c1)

    allv = sorted({v for at in atoms for v in (at[0], at[2], at[3])
                   if not v.startswith("$")})
    # Any bound variable can be the action's root, and it matters which: an atom
    # ROOT often has the identity for its renaming, so an action rooted there
    # cannot tell a union of classes from a union of invocations. A CHILD's
    # renaming is its stored edge, which generally is not the identity.
    if rng.random() < 0.3:
        x, y = rng.choice(allv), rng.choice(allv)
        action = (x, "=", y, y)          # equate two invocations
    else:
        action = (rng.choice(allv), "h", rng.choice(allv), rng.choice(allv))

    probes = terms + [a for a, _ in unions] + [
        ("h", V0, V1), ("h", V0, V0), ("null",), LEAF0]
    return Case(f"fuzz{i}", terms, unions, atoms, action, probes, rounds=6)


# ------------------------------------------------------------------------ main
def main():
    args = sys.argv[1:]
    if args and args[0] == "show":
        # ./xdiff.py show <index> <seed> [perm...]  -- dump one fuzz case
        if not args[1].isdigit():
            # a curated case, by name prefix
            case = next(c for c in curated() if c.name.startswith(args[1]))
            i = case.name
        else:
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
        "unsaturated (excluded)": ["unsaturated"],
        "harness/crash": ["crashed"],
        "machinery baseline": ["BASELINE differs"],
        "nondeterminism": ["nondeterministic"],
        "order dependence": ["order dependent"],
        "slot-renaming": ["not slot-renaming invariant"],
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
