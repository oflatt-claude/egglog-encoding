#!/usr/bin/env python3
"""Generate the arity-dependent half of the slotted machinery.

Every rule that pattern-matches an e-node has to name each column, so it cannot be
written once for all shapes in egglog. It *can* be written once here. This emits
two kinds of output. GENERIC is the string-headed encoding included by
`tests/slotted-egraph-encoding-11.egg`, where the operator is a payload column so any
operator can be written without regenerating. LANGUAGES holds per-language encodings
with one constructor per operator, the shape the reference crate's `define_language!`
produces. The constructor-independent half -- the sorts, the union-find rules, `Var`
normalisation -- stays hand-written in `slotted-egraph-encoding-11.egg`, which the
per-language files include.

A constructor's signature is a list of columns, each either

  * `CHILD`  -- a slotted child, which occupies two egglog columns, `Renaming U`,
               because reaching it requires a renaming; or
  * a sort   -- `"i64"`, `"String"`, ... a payload, one column, no renaming, since
               a payload carries no slots.

So a node's slots come from its `CHILD` columns alone, and payloads ride along
untouched. `(Num i64)` is then just the zero-child case rather than a special kind
of leaf, and mixed shapes like `(Index i64 CHILD)` work with no indirection.

Add a constructor to GENERIC or a language to LANGUAGES, and re-run. Do not edit
the output.

    python3 slotted-experiments/gen-node-rules.py
"""

import pathlib
import re

CHILD = object()          # a slotted child: `Renaming U`
BINDER = object()         # a slotted child that also binds its slot

# What migration does when a node uses a slot its leader's frame cannot name:
# "decline" leaves the node on the follower, "mint" invents a name and moves it, which
# is what the reference does and what empties follower classes. Both agree with the
# reference on partitions and node counts; `mint` is the default because it is the only
# one that empties followers, and the fan-out that once ruled it out is gone.
# `slotted-experiments/xdiff/migration-modes.py` measures the difference.
MIGRATION = "mint"

# The generic, string-headed encoding: what `slotted-egraph-encoding-11.egg` and the
# differential harness use. One constructor per arity with the operator in a payload
# column, so any operator can be written without regenerating anything.
GENERIC = {
    "App2": ["String", CHILD, CHILD],
    "App3": ["String", CHILD, CHILD, CHILD],
    "App4": ["String", CHILD, CHILD, CHILD, CHILD],
    "Num": ["i64"],
    "Sym": ["String"],
    "Scale": ["i64", CHILD],       # keeps the mixed payload/child case exercised
}

# There the operator is in the head, so a binder cannot be declared structurally and
# has to name the string: (head, constructor).
GENERIC_BINDERS = (("lambda", "App2"), ("let", "App3"))

# Per-language encodings are read from `slotted-experiments/languages/*.egg`, one
# constructor per operator -- the shape the reference crate's `define_language!`
# produces, with no head to indirect through.
LANG_DIR = pathlib.Path("slotted-experiments/languages")


def read_language(path):
    """Parse annotated constructor declarations.

        (constructor Lam (U U) U :binder 0)
        (constructor Sum (U U U U) U :binder 1 2)
        (constructor Num (i64) U)

    A `U` column is a slotted child and expands to `Renaming U`; anything else is a
    payload and passes through. `:binder` names the child positions -- counted over
    children, not over columns -- whose slot the node binds. This is the syntax the
    encoder recognises today; the intent is for egglog-experimental to accept it and
    strip it on the way down to core egglog, where nothing about a binder is
    primitive.
    """
    language = {}
    for raw in path.read_text().splitlines():
        line = raw.split(";")[0].strip()
        if not line.startswith("(constructor "):
            continue
        head, _, rest = line[len("(constructor "):].partition("(")
        name = head.strip()
        cols_text, _, tail = rest.partition(")")
        binders = []
        if ":binder" in tail:
            # the closing paren sticks to the last index, so scan for integers
            binders = [int(x) for x in re.findall(r"\d+", tail.split(":binder")[1])]
        sig, seen_kids = [], 0
        for col in cols_text.split():
            if col == "U":
                sig.append(BINDER if seen_kids in binders else CHILD)
                seen_kids += 1
            else:
                sig.append(col)
        language[name] = sig
    return language


LANGUAGES = {p.stem: read_language(p)
             for p in sorted(LANG_DIR.glob("*.egg"))} if LANG_DIR.is_dir() else {}


def cols_of(sig):
    """Column names for a signature: payload vars, and (edge, child) per CHILD."""
    payloads, edges, kids, order = [], [], [], []
    for i, col in enumerate(sig):
        if col in (CHILD, BINDER):
            e, k = f"m{len(kids) + 1}", f"c{len(kids) + 1}"
            edges.append(e)
            kids.append(k)
            order.append((e, k))
        else:
            p = f"p{len(payloads) + 1}"
            payloads.append(p)
            order.append((p,))
    return payloads, edges, kids, order


def pattern(name, sig, edges=None, kids=None, payloads=None):
    """`(Name p1 m1 c1 ...)`, with any column list overridden."""
    dp, de, dk, order = cols_of(sig)
    payloads, edges, kids = payloads or dp, edges or de, kids or dk
    out, pi, ci = [], 0, 0
    for slot in order:
        if len(slot) == 2:
            out += [edges[ci], kids[ci]]
            ci += 1
        else:
            out.append(payloads[pi])
            pi += 1
    return f"({name} {' '.join(out)})"


def declare(name, sig):
    cols = " ".join("Renaming U" if c in (CHILD, BINDER) else c for c in sig)
    return f"(constructor {name} ({cols}) U)\n"


def fold(op, xs, empty):
    if not xs:
        return empty
    out = xs[-1]
    for x in reversed(xs[:-1]):
        out = f"({op} {x} {out})"
    return out


def lex_greater(a, b, i=0):
    """`b` lexicographically greater than `a`, as tuples of renamings.

    The alpha-finder fires in one direction only, so that of two symmetric matches
    exactly one node is eliminated.
    """
    gt = f"(and (bool= (ordering-max {a[i]} {b[i]}) {b[i]}) (bool-!= {a[i]} {b[i]}))"
    if i == len(a) - 1:
        return gt
    return (f"(or {gt}\n              (and (bool= {a[i]} {b[i]})\n"
            f"                   {lex_greater(a, b, i + 1)}))")


def class_slots(name, sig):
    """A node's own slots, offered as an upper bound on its class's.

    `ClassSlots` intersects on merge, so a class ends up with the slots *every* one of
    its nodes has -- anything only some of them carry is redundant. That is the
    reference's `c.slots`, which starts as the creating node's slots and afterwards
    only shrinks. Deriving it from a node is safe here precisely because the merge can
    only narrow, unlike the self-loop rule, which asserts the node's slots outright.
    """
    _, edges, _, _ = cols_of(sig)
    slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    return f"""\
(rule ((= e1 {pattern(name, sig)}))
      ((set (ClassSlots e1) {slots})))
"""


def self_loop(name, sig):
    """A node's class gets the identity on the node's own slots."""
    _, edges, _, _ = cols_of(sig)
    slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    return f"""\
(rule ((= e1 {pattern(name, sig)})
       (= m {slots}))
      ((RenamesToLeader e1 m e1)))
"""


def alpha_finder(name, sig):
    """Two nodes equal up to renaming: keep one, record how the other renames to it.

    Payload columns are named by the same variable on both sides, so a difference
    there simply does not match -- no separate check needed.
    """
    payloads, edges, kids, _ = cols_of(sig)
    a_o = [f"{e}_o" for e in edges]
    a, b = list(edges), [f"b{i + 1}" for i in range(len(edges))]
    syms = [f"sym{i + 1}" for i in range(len(kids))]
    loops = "\n       ".join(
        f"(RenamesToLeader {kids[i]} {syms[i]} {kids[i]})" for i in range(len(kids)))
    composed = "\n       ".join(
        f"(= {a[i]} (compose {a_o[i]} {syms[i]}))" for i in range(len(edges)))
    return f"""\
(rule ((= e1 {pattern(name, sig, edges=a_o)})
       (= e2 {pattern(name, sig, edges=b)})
       (= e1 (ordering-max e1 e2))
       {loops}
       {composed}
       (= m (find-mapping {' '.join(a)} {' '.join(b)}))
       (guard
         (or (bool-!= e1 e2)
             (and (bool= e1 e2)
                  {lex_greater(a_o, b)}))))
      ((RenamesToLeader e1 m e2)
       (delete {pattern(name, sig, edges=a_o)})))
"""


def symmetry_finder(name, sig):
    """The same solve, kept non-destructively as a symmetry of the class."""
    _, edges, kids, _ = cols_of(sig)
    a_o = [f"{e}_o" for e in edges]
    a = list(edges)
    syms = [f"sym{i + 1}" for i in range(len(kids))]
    loops = "\n       ".join(
        f"(RenamesToLeader {kids[i]} {syms[i]} {kids[i]})" for i in range(len(kids)))
    composed = "\n       ".join(
        f"(= {a[i]} (compose {a_o[i]} {syms[i]}))" for i in range(len(edges)))
    return f"""\
(rule ((= e {pattern(name, sig, edges=a_o)})
       {loops}
       {composed}
       (= sym_out (find-mapping {' '.join(a_o)} {' '.join(a)})))
      ((RenamesToLeader e sym_out e)))
"""


def migration(name, sig):
    """Rewrite a follower's node into its leader's frame.

    A node can use a slot its leader's frame cannot name -- a slot the class does not
    depend on. MIGRATION says what to do then: `decline` leaves the node where it is,
    so followers are not emptied; `mint` invents a name, as the reference's
    `compose_fresh` does, so they are.
    """
    _, edges, _, _ = cols_of(sig)
    ns = [f"n{i + 1}" for i in range(len(edges))]
    if MIGRATION == "mint":
        node_slots = fold("map-union", [f"(map-image {m})" for m in edges],
                          "(map-empty)")
        pulled = "\n       ".join(
            [f"(= nodeslots {node_slots})",
             "; R takes the node's slots to the leader's, agreeing with m inverse where",
             "; that is defined and minting a name where it is not",
             "(= R (find-mapping-total (map-domain m) nodeslots (map-domain m) m))"]
            + [f"(= {ns[i]} (compose R {edges[i]}))" for i in range(len(edges))])
    else:
        pulled = "\n       ".join(
            [";; narrowing would understate the child's slots, so decline instead"]
            + [f"(= {ns[i]} (compose-total (inverse m) {edges[i]}))"
               for i in range(len(edges))])
    return f"""\
(rule ((RenamesToLeader e2 m e1)
       (= e2 {pattern(name, sig)})
       (!= e1 e2)
       {pulled})
      ((union e1 {pattern(name, sig, edges=ns)})
       (delete {pattern(name, sig)})))
"""


def child_update(name, sig, pos):
    """Replace child `pos` with its more canonical `m*c'`."""
    _, edges, kids, _ = cols_of(sig)
    new_e, new_k = list(edges), list(kids)
    new_e[pos] = f"(compose {edges[pos]} m)"
    new_k[pos] = "c'"
    return f"""\
(rule ((RenamesToLeader {kids[pos]} m c')
       (= node {pattern(name, sig)})
       ; if the class is unchanged then m must be idempotent: no self-symmetries
       (guard (or (bool-!= {kids[pos]} c') (bool= (compose m m) m)))
       ; and the new node must differ from the old one
       (guard (or (bool-!= {kids[pos]} c')
                  (bool-!= (compose {edges[pos]} m) {edges[pos]}))))
      ((union node {pattern(name, sig, edges=new_e, kids=new_k)})
       (delete {pattern(name, sig)})))
"""


def binder(name, sig, positions, head=None):
    """Take the bound slots out of the node's class's slot set.

    A bound slot rides in its child's edge, so it is a slot of the *node* but must
    not be one of the class: removing it from the edge to the leader is what makes
    two spellings of the same binder alpha-equivalent. A node that binds several
    slots -- `sdql`'s `Sum` -- removes each of them. `head` pins the operator string
    for the generic encoding, where the operator is a payload rather than the
    constructor.
    """
    _, edges, kids, _ = cols_of(sig)
    e, k = list(edges), list(kids)
    for n, pos in enumerate(positions):
        e[pos], k[pos] = f"mvar{n}", "(Var 0)"
    payloads = [f'"{head}"'] if head is not None else None
    node = pattern(name, sig, edges=e, kids=k, payloads=payloads)
    gets = "\n       ".join(
        f"(= v{n} (map-get mvar{n} 0))" for n in range(len(positions)))
    stripped = "(inverse ml)"
    for n in range(len(positions)):
        stripped = f"(map-remove {stripped} v{n})"
    return f"""\
(rule ((RenamesToLeader {node} ml l)
       {gets})
      ((RenamesToLeader {node} (inverse {stripped}) l)))
"""


def banner(text):
    bar = ";" * 78
    return [bar, f";;; {text}", bar, ""]


def shape_of(col):
    return {CHILD: "child", BINDER: "binder"}.get(col, str(col))


def emit(language, binders=()):
    """All the rules for one language: `{constructor: signature}`.

    `binders` pins binders by operator string, for the generic encoding where the
    operator is a payload rather than the constructor. A `BINDER` column declares
    one structurally and needs no entry.
    """
    out = []
    for name, sig in language.items():
        _, edges, kids, _ = cols_of(sig)
        out += banner(f"{name} :: {' '.join(shape_of(c) for c in sig)}")
        out += [declare(name, sig),
                ";; an upper bound on the class's slots; the merge narrows it",
                class_slots(name, sig),
                ";; every class holding a node has a self-loop, so a query can reach it",
                self_loop(name, sig)]
        if not kids:
            continue          # nothing below touches a child
        out += [";; alpha-finder: two nodes equal up to renaming, one eliminated",
                alpha_finder(name, sig),
                ";; the same solve kept as a symmetry, non-destructively",
                symmetry_finder(name, sig),
                ";; migration: move a follower's node into the leader's frame",
                migration(name, sig)]
        for pos in range(len(kids)):
            out += [f";; child-update, child {pos + 1}", child_update(name, sig, pos)]

    binder_rules = []
    for name, sig in language.items():
        kid_cols = [c for c in sig if c in (CHILD, BINDER)]
        bound = [i for i, c in enumerate(kid_cols) if c is BINDER]
        if bound:
            which = ", ".join(str(i + 1) for i in bound)
            binder_rules.append(
                (f";; `{name}` binds child {which}", binder(name, sig, bound)))
    for head, name in binders:
        binder_rules.append((f';; `{head}` binds its first child\'s slot',
                             binder(name, language[name], [0], head=head)))
    if binder_rules:
        out += banner("binders")
        for comment, rule in binder_rules:
            out += [comment, rule]
    return out


SHARED = """\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; a class's slot set, held once
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The slots a class actually depends on, as an identity renaming. Held directly
;; rather than read off a self-loop: a self-loop is derived from a node, so it can
;; name more slots than the class has, and a rule that picks one to mean "the class's
;; slots" gets whichever the join happened to bind. This narrows on merge and so can
;; only ever shrink, which is what the reference's `c.slots` does.
(function ClassSlots (U) Renaming :merge (map-intersect old new))

;; the leaves, whose slots are known outright
(set (ClassSlots (Var 0)) (map-of 0 0))
(set (ClassSlots (Null)) (map-empty))

;; Carry a slot set along a `RenamesToLeader` edge, in both directions: `a = m*b`, so
;; `m` takes b's slots to a's. Transporting a set S through a renaming is the image of
;; the renaming restricted to S.
(rule ((RenamesToLeader a m b) (= S (ClassSlots a)))
      ((set (ClassSlots b) (map-image (compose (inverse m) S)))))
(rule ((RenamesToLeader a m b) (= S (ClassSlots b)))
      ((set (ClassSlots a) (map-image (compose m S)))))
"""

HEADER = """\
;;; GENERATED by slotted-experiments/gen-node-rules.py -- do not edit.
;;;
;;; One block per constructor. A `child` column occupies `Renaming U` and
;;; contributes its slots; a payload column is one column and contributes none, so a
;;; zero-child constructor is just a payload leaf. A `binder` is a child whose slot
;;; the node binds.
"""


def main():
    generic = pathlib.Path("tests/slotted-node-rules.egg")
    generic.write_text(HEADER + "\n" + SHARED + "\n" + "\n".join(emit(GENERIC, GENERIC_BINDERS)))
    print(f"wrote {generic} ({len(GENERIC)} constructors, string-headed)")

    for lang, spec in LANGUAGES.items():
        p = pathlib.Path(f"tests/slotted-lang-{lang}.egg")
        body = HEADER + f';;;\n;;; Language: {lang}\n\n' \
            '(include "tests/slotted-egraph-encoding-11.egg")\n\n' \
            + "\n".join(emit(spec))
        p.write_text(body)
        print(f"wrote {p} ({len(spec)} constructors, one per operator)")


if __name__ == "__main__":
    main()
