#!/usr/bin/env python3
"""Generate the arity-dependent half of the slotted machinery.

Every rule that pattern-matches an e-node has to name each column, so it cannot be
written once for all shapes in egglog. It *can* be written once here. This emits
`tests/slotted-node-rules.egg`; the arity-independent half -- the sorts, the
union-find rules, `Var` normalisation, the tests -- stays hand-written in
`tests/slotted-egraph-encoding-11.egg`.

A constructor's signature is a list of columns, each either

  * `CHILD`  -- a slotted child, which occupies two egglog columns, `Renaming U`,
               because reaching it requires a renaming; or
  * a sort   -- `"i64"`, `"String"`, ... a payload, one column, no renaming, since
               a payload carries no slots.

So a node's slots come from its `CHILD` columns alone, and payloads ride along
untouched. `(Num i64)` is then just the zero-child case rather than a special kind
of leaf, and mixed shapes like `(Index i64 CHILD)` work with no indirection.

Add a constructor to LANGUAGE, a binder to BINDERS, and re-run. Do not edit output.

    python3 slotted-experiments/gen-node-rules.py
"""

import pathlib

CHILD = object()          # a slotted child: `Renaming U`
OUT = pathlib.Path("tests/slotted-node-rules.egg")

LANGUAGE = {
    # String-headed constructors, one per arity: what the differential harness and
    # the hand-written rules use. The head is an ordinary payload column.
    "App2": ["String", CHILD, CHILD],
    "App3": ["String", CHILD, CHILD, CHILD],
    "App4": ["String", CHILD, CHILD, CHILD, CHILD],
    # payloads from the paper's arith / rise / array languages
    "Num": ["i64"],
    "Sym": ["String"],
    # a payload beside a slotted child, to keep the mixed case exercised
    "Scale": ["i64", CHILD],
}

# String-headed operators that bind their first child's slot: (head, constructor).
# The slot rides in an edge to `(Var 0)`, and this is what takes it out of the
# class's slot set -- without it a bound slot stays free.
BINDERS = (("lambda", "App2"), ("let", "App3"))


def cols_of(sig):
    """Column names for a signature: payload vars, and (edge, child) per CHILD."""
    payloads, edges, kids, order = [], [], [], []
    for i, col in enumerate(sig):
        if col is CHILD:
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
    cols = " ".join("Renaming U" if c is CHILD else c for c in sig)
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
                  {lex_greater(a, b)}))))
      ((RenamesToLeader e1 m e2)
       (delete {pattern(name, sig, edges=a)})))
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
    """Rewrite a follower's node into its leader's frame, or decline."""
    _, edges, _, _ = cols_of(sig)
    ns = [f"n{i + 1}" for i in range(len(edges))]
    pulled = "\n       ".join(
        f"(= {ns[i]} (compose-total (inverse m) {edges[i]}))" for i in range(len(edges)))
    return f"""\
(rule ((RenamesToLeader e2 m e1)
       (= e2 {pattern(name, sig)})
       (!= e1 e2)
       ; narrowing would understate the child's slots, so decline instead
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


def binder(head, name):
    """Take a binder's bound slot out of its class's slot set."""
    sig = LANGUAGE[name]
    _, edges, kids, _ = cols_of(sig)
    e = list(edges)
    k = list(kids)
    e[0], k[0] = "mvar", "(Var 0)"
    node = pattern(name, sig, edges=e, kids=k, payloads=[f'"{head}"'])
    return f"""\
(rule ((RenamesToLeader {node} ml l)
       (= v (map-get mvar 0)))
      ((RenamesToLeader {node} (inverse (map-remove (inverse ml) v)) l)))
"""


def banner(text):
    bar = ";" * 78
    return [bar, f";;; {text}", bar, ""]


def main():
    out = [
        ";;; GENERATED by slotted-experiments/gen-node-rules.py -- do not edit.",
        ";;;",
        ";;; One block per constructor. A CHILD column occupies `Renaming U` and",
        ";;; contributes its slots; a payload column is one column and contributes",
        ";;; none, so a zero-child constructor is just a payload leaf.",
        "",
    ]
    for name, sig in LANGUAGE.items():
        _, edges, kids, _ = cols_of(sig)
        shape = " ".join("child" if c is CHILD else str(c) for c in sig)
        out += banner(f"{name} :: {shape}")
        out += [declare(name, sig),
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

    out += banner("binders")
    for head, name in BINDERS:
        out += [f';; `{head}` binds its first child\'s slot', binder(head, name)]

    OUT.write_text("\n".join(out))
    print(f"wrote {OUT} ({len(OUT.read_text().splitlines())} lines, "
          f"{len(LANGUAGE)} constructors)")


if __name__ == "__main__":
    main()
