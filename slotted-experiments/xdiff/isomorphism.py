"""Is the encoding's final e-graph *isomorphic* to the reference's?

Everything else here compares a projection -- the probe partition, node counts per
operator, one invariant. Two different e-graphs can agree on all of those. This
constructs a witness instead: a bijection between the two sides' e-classes, plus a
bijection between each matched pair's slots, under which the node sets are equal. If one
is found it is checked, so success is a proof; failure only means none was found within
the search cap, and is reported as such rather than as a difference.

Three things make the comparison non-trivial, and each is handled rather than assumed
away:

* **Slot names are unrelated.** The reference mints `$f0, $f1, ...` from a global
  counter; the encoding mints the smallest unused integer. So the per-class slot
  bijection is part of what is searched for, not read off.
* **A class's symmetry group is not in its node set.** A commutative class holds *one*
  node and a swap; a class without the swap holds the same one node. Comparing node sets
  alone cannot tell them apart, so the group is compared too -- recovered from the
  reference with `eq` on two invocations, and from the encoding as the idempotent-free
  self-loops `(RenamesToLeader c p c)` whose `p` permutes the class's slots.
* **A node is only defined up to those groups.** `k($0,$1)` and `k($1,$0)` are the same
  node of a commutative class, and the two sides need not store the same representative.
  So node equality quantifies over the parent's group and each child's group -- the
  reference's "strong shape" -- and over renamings of slots the node carries but its
  class does not, which is alpha-equivalence for a binder's bound slot.

Run: `python3 slotted-experiments/xdiff/isomorphism.py [name-prefix|fuzz N [seed]]`
"""
import itertools
import random
import re
import subprocess
import sys
sys.path.insert(0, "slotted-experiments/xdiff")
import xdiff as X

TABLES = ["IsVarClass", "IsNullClass", "ClassSlots", "RenamesToLeader",
          "App2", "App3", "App4", "Num", "Sym", "Scale"]

# `Var` and `Null` are constructors, not rows, so which class holds one cannot be read
# off the tables -- and it cannot be recovered from the printed name either: a value
# prints as *some* term of its class, so once `(Var 0)` is unioned with `(Null)` the var
# class prints as `(Null)` and its `var` node silently disappears. Asking egglog which
# class each one landed in is the only reliable way.
MARKERS = """
(relation IsVarClass (U))
(relation IsNullClass (U))
(IsVarClass (Var 0))
(IsNullClass (Null))
"""
SEARCH_CAP = 200_000

#: cases compared at a database fixpoint because the rules never stop firing
UNSATURATED = []


# --------------------------------------------------------------- s-expressions
def parse_sexpr(s, i=0):
    """Parse one s-expression, returning (tree, next index). Atoms stay strings."""
    while i < len(s) and s[i].isspace():
        i += 1
    if s[i] == "(":
        i += 1
        out = []
        while True:
            while i < len(s) and s[i].isspace():
                i += 1
            if s[i] == ")":
                return tuple(out), i + 1
            child, i = parse_sexpr(s, i)
            out.append(child)
    if s[i] == '"':
        j = s.index('"', i + 1)
        return s[i:j + 1], j + 1
    j = i
    while j < len(s) and not s[j].isspace() and s[j] not in "()":
        j += 1
    return s[i:j], j


def unparse(t):
    if isinstance(t, str):
        return t
    return "(" + " ".join(unparse(k) for k in t) + ")"


def as_map(t):
    """`(map-of 0 1 2 3)` / `(map-empty)` -> {0: 1, 2: 3}."""
    if isinstance(t, str) or t[0] == "map-empty":
        return {}
    xs = [int(v) for v in t[1:]]
    return dict(zip(xs[0::2], xs[1::2]))


# ------------------------------------------------------------------ the graphs
class Graph:
    """Classes, each with slots, a symmetry group, and a set of nodes.

    A node is `(op, elems)`; an elem is `("slot", s)` for a slot the node names
    directly, or `("child", cid, ((child_slot, parent_slot), ...))`.
    """

    def __init__(self):
        self.slots = {}      # cid -> tuple of slot names
        self.group = {}      # cid -> set of permutations, each a frozenset of pairs
        self.nodes = {}      # cid -> list of nodes

    def add_class(self, cid, slots):
        self.slots.setdefault(cid, tuple(slots))
        self.group.setdefault(cid, set())
        self.nodes.setdefault(cid, [])

    def close_groups(self):
        """Put the identity in every group.

        A group always contains it, but a slotless class's identity is the *empty*
        permutation, which the reference prints as an empty field -- indistinguishable
        from "no permutations" unless this is made explicit.
        """
        for cid, slots in self.slots.items():
            self.group[cid].add(frozenset((s, s) for s in slots))

    def ids(self):
        return sorted(self.slots)

    def summary(self):
        return (len(self.slots), sum(len(v) for v in self.nodes.values()))


def parse_reference(out):
    g = Graph()
    for line in out.splitlines():
        p = line.split()
        if not p:
            continue
        if p[0] == "CLASS":
            slots = p[3].split(",") if len(p) > 3 and p[3] else []
            g.add_class(p[1], [s for s in slots if s])
        elif p[0] == "GROUP":
            cid = p[1]
            g.add_class(cid, g.slots.get(cid, ()))
            if len(p) > 2 and p[2] != "?":
                for perm in p[2].split(";"):
                    if not perm:
                        continue
                    pairs = [tuple(x.split(">")) for x in perm.split("|")]
                    g.group[cid].add(frozenset(pairs))
            elif len(p) > 2:
                raise ValueError("group too large to enumerate")
        elif p[0] == "NODE":
            cid, op, elems = p[1], None, []
            for e in p[2:]:
                kind, _, rest = e.partition(":")
                if kind == "o":
                    op = rest if op is None else f"{op}/{rest}"
                elif kind == "s":
                    elems.append(("slot", rest))
                elif kind == "c":
                    child, _, mtext = rest.partition(":")
                    m = tuple(sorted(tuple(x.split(">"))
                                     for x in mtext.split("|") if x))
                    elems.append(("child", child, m))
            g.nodes[cid].append((op, tuple(elems)))
    g.close_groups()
    return g


def parse_encoding(out, tables):
    """Read the printed tables into a Graph, resolving followers onto leaders."""
    slots_of, loops, rows = {}, [], []
    leaf = {}
    for name, block in tables.items():
        for line in block:
            lhs, _, rhs = line.partition(" -> ")
            t, _ = parse_sexpr(lhs.strip())
            if name in ("IsVarClass", "IsNullClass"):
                leaf["var" if name == "IsVarClass" else "null"] = unparse(t[1])
            elif name == "ClassSlots":
                slots_of[unparse(t[1])] = tuple(sorted(as_map(parse_sexpr(rhs)[0])))
            elif name == "RenamesToLeader":
                loops.append((unparse(t[1]), as_map(t[2]), unparse(t[3])))
            else:
                rows.append((name, t, unparse(parse_sexpr(rhs)[0])))

    # `Unextractable` is what a value with no extractable term prints as, and it is
    # contagious: a class holding a row whose *child* is unextractable cannot be printed
    # either. Several distinct classes then share that one name, and nothing in the
    # printed output tells them apart -- so the graph cannot be rebuilt from it. That is a
    # limit of reading the encoding through extraction, not a difference from the
    # reference, and it is reported as its own outcome.
    unextractable = sum(1 for line in tables.get("ClassSlots", [])
                        if line.split(" -> ")[0].strip() == "(ClassSlots Unextractable)")

    # A slotted class spans several U values, and only one of them holds its rows now
    # that followers are empty -- that one is the class. An empty follower needs a
    # representative only if some edge points *at* it; one that nothing references
    # contributes nothing and is dropped, which matters because several of them print
    # as the same `Unextractable` and so cannot be told apart.
    holds = {cid for _, _, cid in rows}
    holds |= set(leaf.values())
    referenced = set()
    for _, t, _ in rows:
        for i in range(1, len(t) - 1):
            # a child column is a renaming followed by the child itself
            if not isinstance(t[i], str) and t[i] and t[i][0] in ("map-of", "map-empty"):
                referenced.add(unparse(t[i + 1]))
    rep, ren = {}, {}
    for v in holds:
        rep[v], ren[v] = v, {s: s for s in slots_of.get(v, ())}
    # Collected rather than assigned, because a value printing as `Unextractable` --
    # which is what a value with no rows of its own prints as -- is not a unique name:
    # two distinct empty followers share it. Redirecting on the last one seen would be a
    # silent guess, so a value offered two different representatives is reported instead.
    proposals = {}
    for a, m, b in loops:
        if a == b:
            continue
        # `a = m*b`: m takes b's slots to a's
        if a not in holds and b in holds:
            proposals.setdefault(a, {})[b] = m
        elif b not in holds and a in holds:
            inv = {v: k for k, v in m.items()}
            if len(inv) == len(m):
                proposals.setdefault(b, {})[a] = inv
    # only a referenced follower has to be placed, and then unambiguously
    need = referenced - holds
    ambiguous = [v for v in need if len(proposals.get(v, {})) != 1]
    for v in need - set(ambiguous):
        (rep[v], ren[v]), = proposals[v].items()
    # Two values of one slotted class both holding rows. Modelling them as two classes
    # would be a difference invented here rather than a real one, and merging them means
    # translating one frame into the other and deduplicating what then coincides -- which
    # this does not do. Reported, not guessed at. Note this is *not* the same as a follower
    # holding a node: the var class always holds one, so it fires whenever the var class
    # shares a slotted class with a row-holding one, whichever of them is the leader.
    split = [(a, b) for a, m, b in loops
             if a != b and a in holds and b in holds and a in slots_of]

    g = Graph()
    for v in sorted(holds):
        g.add_class(v, slots_of.get(v, ()))
    # the group: a self-loop whose renaming permutes the class's slots
    for a, m, b in loops:
        if a == b and rep.get(a, a) == a and a in g.slots:
            dom, im = set(m), set(m.values())
            if dom == im == set(g.slots[a]):
                g.group[a].add(frozenset(m.items()))
    # `Var`/`Null` are constructors rather than rows, so their nodes are added here --
    # into whichever class each one actually landed in, which is what the markers say
    if "var" in leaf and leaf["var"] in g.slots:
        g.nodes[leaf["var"]].append(("var", (("slot", 0),)))
    if "null" in leaf and leaf["null"] in g.slots:
        g.nodes[leaf["null"]].append(("null", ()))

    for name, t, cid in rows:
        cid = rep.get(cid, cid)
        if cid not in g.slots:
            continue
        op, elems, i = None, [], 1
        while i < len(t):
            a = t[i]
            if isinstance(a, str) and a.startswith('"'):
                lit = a.strip('"')
                op = lit if op is None else f"{op}/{lit}"
                i += 1
            elif isinstance(a, str):
                op = f"{name}/{a}" if op is None else f"{op}/{a}"
                i += 1
            else:
                m, child = as_map(a), unparse(t[i + 1])
                r = rep.get(child, child)
                if r != child:
                    # express the edge in the representative's frame: e' = e . ren
                    m = {k: m[v] for k, v in ren[child].items() if v in m}
                    child = r
                elems.append(("child", child, m))
                i += 2
        if op is None:
            op = name
        g.nodes[cid].append((op, tuple(elems)))
    g.close_groups()
    return g, ambiguous, leaf, unextractable, split


# ------------------------------------------------------- the encoding's own ops
def to_reference_shape(g, var_class=None):
    """Rewrite the encoding's node forms into the reference's.

    Two operators are spelled differently by construction, and both are documented
    where they are built (`enc` in xdiff.py, `define_language!` in xmulti):

      * `lambda` is `lam`, and its bound slot rides in a child edge to the var class
        rather than being a slot literal on the node.
      * a child edge is a dict here and a sorted pair tuple there.
    """
    out = Graph()
    for cid in g.ids():
        out.add_class(cid, g.slots[cid])
        out.group[cid] = g.group[cid]
    fresh = itertools.count()
    unfaithful = []
    for cid in g.ids():
        for op, elems in g.nodes[cid]:
            if op == "lambda" and elems and elems[0][0] == "child":
                child, m = elems[0][1], dict(elems[0][2])
                # The bound slot rides in this edge. It can have been dropped -- a
                # binder whose slot nothing uses -- and then there is no name left to
                # carry over; any fresh one does, because a slot the node's class does
                # not have is renamed freely when nodes are matched.
                if 0 in m:
                    bound = m[0]
                elif len(m) == 1:
                    bound = next(iter(m.values()))
                else:
                    bound = f"_b{next(fresh)}"
                # the position is the binder by the encoding's convention, but it still
                # has to be the variable class, or the convention is not being followed
                if var_class is not None and child != var_class:
                    unfaithful.append((cid, child))
                elems = (("slot", bound),) + elems[1:]
                op = "lam"
            fixed = []
            for e in elems:
                if e[0] == "child":
                    fixed.append(("child", e[1],
                                  tuple(sorted(e[2].items()))
                                  if isinstance(e[2], dict) else e[2]))
                else:
                    fixed.append(e)
            out.nodes[cid].append((op, tuple(fixed)))
    return out, unfaithful


# ------------------------------------------------------------- node equivalence
def node_slots(node, class_slots):
    """The parent-frame slots a node names, and which of them its class does not."""
    used = []
    for e in node[1]:
        if e[0] == "slot":
            used.append(e[1])
        else:
            used += [p for _, p in e[2]]
    seen, ordered = set(), []
    for s in used:
        if s not in seen:
            seen.add(s)
            ordered.append(s)
    return ordered, [s for s in ordered if s not in class_slots]


def apply_node(node, pmap, cmap, smap):
    """Rewrite a node: parent slots by `pmap`, child ids by `cmap`, child slots by
    `smap[cid]`. A slot `pmap` does not mention is left alone."""
    out = []
    for e in node[1]:
        if e[0] == "slot":
            out.append(("slot", pmap.get(e[1], e[1])))
        else:
            cid = cmap[e[1]]
            sm = smap[e[1]]
            out.append(("child", cid,
                        tuple(sorted((sm.get(cs, cs), pmap.get(ps, ps))
                                     for cs, ps in e[2]))))
    return (node[0], tuple(out))


def group_variants(node, gp, groups):
    """Every node equal to this one under the parent's group and the children's.

    This is the reference's "strong shape": an invocation `m` of a child class denotes
    the same thing as `m . h` for any `h` in that child's group, and the parent class
    asserting a permutation `g` means its node set is closed under applying `g`.
    """
    child_ids = [e[1] for e in node[1] if e[0] == "child"]
    # `sorted` on frozensets would use subset order, which is partial; sort by contents
    # so the enumeration is deterministic run to run
    per_child = [sorted(groups.get(c) or {frozenset()}, key=lambda p: sorted(map(str, p)))
                 for c in child_ids]
    for g in sorted(gp or {frozenset()}, key=lambda p: sorted(map(str, p))):
        gd = dict(g)
        for combo in itertools.product(*per_child) if per_child else [()]:
            out, k = [], 0
            for e in node[1]:
                if e[0] == "slot":
                    out.append(("slot", gd.get(e[1], e[1])))
                else:
                    h = dict(combo[k])
                    k += 1
                    # m . h, then g on the parent side
                    inv = {v: kk for kk, v in h.items()}
                    m = {inv.get(cs, cs): gd.get(ps, ps) for cs, ps in e[2]}
                    out.append(("child", e[1], tuple(sorted(m.items()))))
            yield (node[0], tuple(out))


def match_nodes(src, dst, src_slots, dst_slots, pmap, cmap, smap, dst_groups):
    """Can `src`'s nodes be matched one-to-one onto `dst`'s?

    `pmap` fixes the class slots; slots the node carries but the class does not are
    existentially quantified, so every bijection between the two sides' extras is
    tried -- that is alpha-equivalence for a bound slot.
    """
    if len(src) != len(dst):
        return False
    variants = [set(group_variants(n, dst_groups[1], dst_groups[0])) for n in dst]

    def compatible(n, j):
        _, extra = node_slots(n, src_slots)
        _, dextra = node_slots(dst[j], dst_slots)
        if len(extra) != len(dextra):
            return False
        for perm in itertools.permutations(dextra):
            full = dict(pmap)
            full.update(dict(zip(extra, perm)))
            if apply_node(n, full, cmap, smap) in variants[j]:
                return True
        return False

    # small bipartite matching
    pair = {}

    def augment(i, seen):
        for j in range(len(dst)):
            if j in seen or not compatible(src[i], j):
                continue
            seen.add(j)
            if j not in pair or augment(pair[j], seen):
                pair[j] = i
                return True
        return False

    for i in range(len(src)):
        if not augment(i, set()):
            return False
    return True


# --------------------------------------------------------------- the refinement
def colors(g, rounds=6):
    col = {c: (len(g.slots[c]), len(g.group[c]),
               tuple(sorted((n[0], tuple(e[0] for e in n[1])) for n in g.nodes[c])))
           for c in g.ids()}
    for _ in range(rounds):
        nxt = {}
        for c in g.ids():
            sig = []
            for op, elems in g.nodes[c]:
                sig.append((op, tuple(e[0] if e[0] == "slot" else col[e[1]]
                                      for e in elems)))
            nxt[c] = (col[c], tuple(sorted(sig)))
        if all(len({nxt[a] for a in g.ids() if col[a] == col[c]})
               == len({col[a] for a in g.ids() if col[a] == col[c]})
               for c in g.ids()):
            return nxt
        col = nxt
    return col


# ---------------------------------------------------------------- the isomorphism
def find_isomorphism(ga, gb):
    """A (class bijection, per-class slot bijection) pair, or a reason there is none."""
    if len(ga.ids()) != len(gb.ids()):
        return None, (f"class count {len(ga.ids())} vs {len(gb.ids())}")
    ca, cb = colors(ga), colors(gb)
    from collections import Counter
    if Counter(ca.values()) != Counter(cb.values()):
        only_a = Counter(ca.values()) - Counter(cb.values())
        return None, f"refinement colors differ ({len(only_a)} class shapes unmatched)"

    cand = {a: [b for b in gb.ids() if cb[b] == ca[a]] for a in ga.ids()}
    order = sorted(ga.ids(), key=lambda a: len(cand[a]))
    budget = [SEARCH_CAP]

    def slot_bijections(a, b):
        sa, sb = ga.slots[a], gb.slots[b]
        if len(sa) != len(sb):
            return
        for perm in itertools.permutations(sb):
            m = dict(zip(sa, perm))
            # the group has to correspond too, not just the slot count
            mapped = {frozenset((m[x], m[y]) for x, y in p) for p in ga.group[a]}
            if mapped == gb.group[b]:
                yield m

    phi, sig = {}, {}

    def rec(k):
        if budget[0] <= 0:
            return False
        if k == len(order):
            return verify(ga, gb, phi, sig) is None
        a = order[k]
        for b in cand[a]:
            if b in phi.values():
                continue
            for m in slot_bijections(a, b):
                budget[0] -= 1
                if budget[0] <= 0:
                    return False
                phi[a], sig[a] = b, m
                # check now if every child of every node of `a` is already assigned
                ready = all(e[0] == "slot" or e[1] in phi
                            for n in ga.nodes[a] for e in n[1])
                if not ready or match_nodes(
                        ga.nodes[a], gb.nodes[b], ga.slots[a], gb.slots[b], m, phi,
                        sig, (gb.group, gb.group[b])):
                    if rec(k + 1):
                        return True
                del phi[a], sig[a]
        return False

    if rec(0):
        return (dict(phi), dict(sig)), None
    if budget[0] <= 0:
        return None, f"search cap ({SEARCH_CAP}) reached -- inconclusive"
    return None, "no isomorphism exists (search exhausted)"


def verify(ga, gb, phi, sig):
    """None if (phi, sig) really is an isomorphism, else the first thing wrong."""
    if sorted(phi) != ga.ids() or sorted(phi.values()) != gb.ids():
        return "not a bijection on classes"
    for a in ga.ids():
        b = phi[a]
        if len(ga.slots[a]) != len(gb.slots[b]):
            return f"{a}: slot count"
        mapped = {frozenset((sig[a][x], sig[a][y]) for x, y in p)
                  for p in ga.group[a]}
        if mapped != gb.group[b]:
            return f"{a}: symmetry group ({len(ga.group[a])} vs {len(gb.group[b])})"
        if not match_nodes(ga.nodes[a], gb.nodes[b], ga.slots[a], gb.slots[b],
                           sig[a], phi, sig, (gb.group, gb.group[b])):
            return (f"{a}: node sets ({len(ga.nodes[a])} vs {len(gb.nodes[b])})")
    return None


# ------------------------------------------------------------------- the runners
#: The machinery seeds `(Var 0)` and `(Null)` unconditionally, so those two classes
#: exist on the encoding side whether or not the case mentions them. Adding the same two
#: terms to the reference makes the two graphs comparable as wholes, rather than needing
#: classes to be dropped from one side by a rule about which ones "do not count". They
#: are ordinary terms to the reference, so any rule that fires on them fires on the
#: encoding's copies too.
SEED = "term (null)\nterm (var $0)\n"


def reference_graph(case):
    spec = case.spec() + SEED + "dump\n"
    r = subprocess.run([str(X.XMULTI / "target" / "debug" / "xmulti")],
                       input=spec, capture_output=True, text=True,
                       timeout=X.RUN_TIMEOUT)
    if r.returncode != 0:
        return None, f"reference error: {(r.stderr or '?').strip().splitlines()[-1]}"
    if any(l.startswith("SATURATED no") for l in r.stdout.splitlines()):
        return None, "reference did not saturate"
    return parse_reference(r.stdout), None


def canonical(g):
    """A string that determines the graph, for comparing two runs of one case."""
    return repr([(c, g.slots[c], sorted(map(sorted, g.group[c])), sorted(map(str, g.nodes[c])))
                 for c in g.ids()])


def _dump(case, mult, timeout):
    dump = MARKERS + "\n".join(f"(print-function {t} 100000)" for t in TABLES)
    prog = X.egg_program(case, mult=mult)
    prog = prog.replace("(print-function SameClass 100000)", dump)
    p = X.ROOT / f"xdiff-tmp-iso-{abs(hash(case.name)) % 99999}-{mult}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True,
                           text=True, cwd=X.ROOT, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, "timeout"
    finally:
        p.unlink(missing_ok=True)
    if r.returncode != 0:
        err = [l for l in r.stderr.splitlines() if "ERROR" in l]
        return None, f"encoding error: {err[-1] if err else r.stderr[:120]}"
    # the printed blocks come back in the order the prints were issued
    blocks, cur, depth, order = {}, None, 0, list(TABLES)
    for line in r.stdout.splitlines():
        t = line.strip()
        if t == "(":
            cur = order.pop(0) if order else None
            blocks[cur] = []
            depth = 1
            continue
        if t == ")" and depth:
            depth = 0
            continue
        if cur and depth and t:
            blocks[cur].append(t)
    g, ambiguous, leaf, unextractable, split = parse_encoding(r.stdout, blocks)
    # The name collision is checked first because it *manufactures* the other symptom:
    # several classes sharing one name look like one class linked to itself, which is
    # indistinguishable here from a class whose nodes really do sit on two values.
    if unextractable > 1 and (split or ambiguous):
        return None, ("limit", f"{unextractable} classes share the name "
                               "`Unextractable`, so they cannot be told apart")
    if split:
        return None, ("limit", "one slotted class spans two values that both hold rows"
                               " -- merging their frames is not done here")
    if ambiguous:
        return None, f"could not place {len(ambiguous)} follower value(s): {ambiguous[:2]}"
    g, unfaithful = to_reference_shape(g, leaf.get("var"))
    if unfaithful:
        return None, f"binder position is not the variable class: {unfaithful[:2]}"
    return g, None


def encoding_graph(case):
    """The encoding's final graph, at the strongest fixpoint available to it.

    The harness's schedule saturates the `slotted` invariants between user-rule steps and
    gives the user rules a finite step count, since user rules are not expected to
    terminate. If that does not finish, the state is taken at a fixpoint of the *database*
    instead, established by two different step counts producing the same graph -- the same
    standard the partition comparison uses -- and reported separately.
    """
    g, err = _dump(case, 3, timeout=60)
    if err != "timeout":
        return g, err
    a, e1 = _dump(case, 6, timeout=180)
    if e1:
        return None, ("limit" if e1 == "timeout" else "FAIL",
                      "encoding too slow to settle") if e1 == "timeout" else e1
    b, e2 = _dump(case, 12, timeout=180)
    if e2:
        return None, e2 if e2 != "timeout" else ("limit", "encoding too slow to settle")
    if canonical(a) != canonical(b):
        return None, "encoding has not settled: doubling the rounds changes the graph"
    UNSATURATED.append(case.name)
    return a, None


def check(case):
    # A reference that errors or will not settle gives nothing to compare against, so
    # the case is skipped. The encoding failing the same way is not a skip: the
    # reference reached a fixpoint, so not reaching one is itself a difference.
    ref, err = reference_graph(case)
    if err:
        return "skip", err
    enc, err = encoding_graph(case)
    if isinstance(err, tuple):
        return err[0], err[1]
    if err:
        return "FAIL", err
    iso, why = find_isomorphism(ref, enc)
    if iso is None:
        return "FAIL", f"{why}  [ref {ref.summary()} enc {enc.summary()}]"
    bad = verify(ref, enc, iso[0], iso[1])
    if bad:
        return "FAIL", f"witness rejected: {bad}"
    n, m = ref.summary()
    groups = sum(len(v) for v in ref.group.values())
    return "ok", (n, m, groups)


def selftest():
    """Hand-built graphs, exercising what the mutations may not reach.

    A checker that always answers "isomorphic" would pass every corpus, so the three
    answers that matter are pinned here: a pure relabelling must be *accepted*, and the
    two subtlest ways to differ -- a missing symmetry, and one edge moved -- must be
    *rejected*. No egglog and no reference, so this stays honest if either changes.
    """
    def build(spec):
        g = Graph()
        for cid, (slots, perms, nodes) in spec.items():
            g.add_class(cid, slots)
            for p in perms:
                g.group[cid].add(frozenset(p))
            g.nodes[cid] = nodes
        g.close_groups()
        return g

    def kn(child, *pairs):
        return ("k", tuple(("child", child, (p,)) for p in pairs))

    swap = [[("a", "b"), ("b", "a")]]
    base = build({"v": (("x",), [], [("var", (("slot", "x"),))]),
                  "K": (("a", "b"), swap, [kn("v", ("x", "a"), ("x", "b"))])})
    cases = [
        # the same graph with every slot renamed
        ("relabelled", True,
         build({"w": (("q",), [], [("var", (("slot", "q"),))]),
                "J": (("m", "n"), [[("m", "n"), ("n", "m")]],
                      [kn("w", ("q", "m"), ("q", "n"))])})),
        # identical nodes, but the class does not prove the swap
        ("symmetry dropped", False,
         build({"w": (("q",), [], [("var", (("slot", "q"),))]),
                "J": (("m", "n"), [], [kn("w", ("q", "m"), ("q", "n"))])})),
        # the swap, but both edges land on one slot
        ("edge moved", False,
         build({"w": (("q",), [], [("var", (("slot", "q"),))]),
                "J": (("m", "n"), [[("m", "n"), ("n", "m")]],
                      [kn("w", ("q", "m"), ("q", "m"))])})),
    ]
    bad = 0
    for name, want, other in cases:
        got, why = find_isomorphism(base, other)
        ok = (got is not None) == want
        if got is not None and verify(base, other, got[0], got[1]) is not None:
            ok = False
        bad += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} {name:20} "
              f"isomorphic={got is not None}, expected={want}"
              f"{'' if got else '  (' + (why or '') + ')'}")
    print(f"\n{len(cases) - bad}/{len(cases)} self-tests pass")
    return 1 if bad else 0


def main():
    args = sys.argv[1:]
    if args and args[0] == "selftest":
        return selftest()
    if args and args[0] == "fuzz":
        n = int(args[1]) if len(args) > 1 else 100
        rng = random.Random(int(args[2]) if len(args) > 2 else 0)
        cases = [X.rand_case(rng, i) for i in range(n)]
    elif args:
        cases = [c for c in X.curated() if c.name.startswith(args[0])]
    else:
        cases = X.curated()

    tally = {"ok": 0, "FAIL": 0, "skip": 0, "limit": 0}
    totals = [0, 0, 0]
    for c in cases:
        verdict, detail = check(c)
        tally[verdict] += 1
        if verdict == "ok":
            totals = [a + b for a, b in zip(totals, detail)]
        else:
            print(f"  {verdict:4} {c.name:44} {detail}", flush=True)
    # the sizes are part of the result: a checker comparing nothing would also pass
    print(f"\n{tally['ok']}/{len(cases)} isomorphic"
          f"   ({tally['FAIL']} differ, {tally['skip']} skipped,"
          f" {tally['limit']} not comparable)")
    print(f"matched {totals[0]} e-classes, {totals[1]} e-nodes, "
          f"{totals[2]} symmetries")
    if UNSATURATED:
        print(f"{len(UNSATURATED)} compared at a database fixpoint, not a rule "
              f"fixpoint: {', '.join(UNSATURATED[:6])}"
              f"{' ...' if len(UNSATURATED) > 6 else ''}")
    return 1 if tally["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
