#!/usr/bin/env python3
"""Generate the arity-dependent half of the slotted machinery.

Every rule that pattern-matches an e-node has to name each child position, so it
cannot be written once for all arities in egglog. It *can* be written once here.
This emits `tests/slotted-node-rules.egg` for each arity in ARITIES; the rest of
the machinery -- the sorts, the union-find rules, `Var` normalisation, the tests --
is arity-independent and stays hand-written in
`tests/slotted-egraph-encoding-11.egg`.

Add an arity by putting it in ARITIES, or a binder by putting it in BINDERS, and
re-run. Do not edit the output.

    python3 slotted-experiments/gen-node-rules.py
"""

import pathlib

ARITIES = (2, 3, 4)          # app/lam, let, sdql's double binder
OUT = pathlib.Path("tests/slotted-node-rules.egg")

# Operators that bind their first child's slot: (op, arity). A binder's slot rides
# in an edge to `(Var 0)`, and the rule below is what takes it out of the class's
# slot set -- without it the bound slot stays free.
BINDERS = (("lambda", 2), ("let", 3))


def app(n, edges, kids):
    """`(Appn f e1 k1 ... en kn)`."""
    body = " ".join(f"{edges[i]} {kids[i]}" for i in range(n))
    return f'(App{n} f {body})'


def fold(op, xs):
    """Right-fold a binary operator over `xs`."""
    out = xs[-1]
    for x in reversed(xs[:-1]):
        out = f"({op} {x} {out})"
    return out


def lex_greater(a, b, i=0):
    """`b` is lexicographically greater than `a`, both tuples of renamings.

    Mirrors the hand-written arity-2 guard: the pair is ordered by the first
    position where they differ, and the rule only fires in the greater direction so
    that one of the two symmetric matches is dropped.
    """
    greater = f"(and (bool= (ordering-max {a[i]} {b[i]}) {b[i]}) (bool-!= {a[i]} {b[i]}))"
    if i == len(a) - 1:
        return greater
    return f"(or {greater}\n              (and (bool= {a[i]} {b[i]})\n                   {lex_greater(a, b, i + 1)}))"


def constructor(n):
    cols = " ".join(["Renaming U"] * n)
    return f"(constructor App{n} (String {cols}) U)\n"


def self_loop(n):
    """A node's class gets the identity on the node's own slots."""
    ms = [f"m{i}" for i in range(1, n + 1)]
    cs = [f"c{i}" for i in range(1, n + 1)]
    slots = fold("map-union", [f"(map-image {m})" for m in ms])
    return f"""\
(rule ((= e1 {app(n, ms, cs)})
       (= m {slots}))
      ((RenamesToLeader e1 m e1)))
"""


def alpha_finder(n):
    """Two nodes equal up to renaming: keep one, record how the other renames to it."""
    a_o = [f"a{i}_o" for i in range(1, n + 1)]
    a = [f"a{i}" for i in range(1, n + 1)]
    b = [f"b{i}" for i in range(1, n + 1)]
    cs = [f"c{i}" for i in range(1, n + 1)]
    syms = [f"sym{i}" for i in range(1, n + 1)]
    loops = "\n       ".join(
        f"(RenamesToLeader {cs[i]} {syms[i]} {cs[i]})" for i in range(n))
    composed = "\n       ".join(
        f"(= {a[i]} (compose {a_o[i]} {syms[i]}))" for i in range(n))
    return f"""\
(rule ((= e1 {app(n, a_o, cs)})
       (= e2 {app(n, b, cs)})
       (= e1 (ordering-max e1 e2))
       {loops}
       {composed}
       (= m (find-mapping {' '.join(a)} {' '.join(b)}))
       (guard
         (or (bool-!= e1 e2)
             (and (bool= e1 e2)
                  {lex_greater(a, b)}))))
      ((RenamesToLeader e1 m e2)
       (delete {app(n, a, cs)})))
"""


def symmetry_finder(n):
    """The same solve, kept non-destructively as a symmetry of the class."""
    a_o = [f"a{i}_o" for i in range(1, n + 1)]
    a = [f"a{i}" for i in range(1, n + 1)]
    cs = [f"c{i}" for i in range(1, n + 1)]
    syms = [f"sym{i}" for i in range(1, n + 1)]
    loops = "\n       ".join(
        f"(RenamesToLeader {cs[i]} {syms[i]} {cs[i]})" for i in range(n))
    composed = "\n       ".join(
        f"(= {a[i]} (compose {a_o[i]} {syms[i]}))" for i in range(n))
    return f"""\
(rule ((= e {app(n, a_o, cs)})
       {loops}
       {composed}
       (= sym_out (find-mapping {' '.join(a_o)} {' '.join(a)})))
      ((RenamesToLeader e sym_out e)))
"""


def migration(n):
    """Rewrite a follower's node into its leader's frame, or decline."""
    ms = [f"m{i}" for i in range(1, n + 1)]
    ns = [f"n{i}" for i in range(1, n + 1)]
    cs = [f"c{i}" for i in range(1, n + 1)]
    pulled = "\n       ".join(
        f"(= {ns[i]} (compose-total (inverse m) {ms[i]}))" for i in range(n))
    return f"""\
(rule ((RenamesToLeader e2 m e1)
       (= e2 {app(n, ms, cs)})
       (!= e1 e2)
       ; narrowing would understate the child's slots, so decline instead
       {pulled})
      ((union e1 {app(n, ns, cs)})
       (delete {app(n, ms, cs)})))
"""


def child_update(n, pos):
    """Replace child `pos` with its more canonical `m*c'`."""
    ms = [f"m{i}" for i in range(1, n + 1)]
    cs = [f"c{i}" for i in range(1, n + 1)]
    new_ms = list(ms)
    new_cs = list(cs)
    new_ms[pos] = f"(compose {ms[pos]} m)"
    new_cs[pos] = "c'"
    return f"""\
(rule ((RenamesToLeader {cs[pos]} m c')
       (= node {app(n, ms, cs)})
       ; if the class is unchanged then m must be idempotent: no self-symmetries
       (guard (or (bool-!= {cs[pos]} c') (bool= (compose m m) m)))
       ; and the new node must differ from the old one
       (guard (or (bool-!= {cs[pos]} c') (bool-!= (compose {ms[pos]} m) {ms[pos]}))))
      ((union node {app(n, new_ms, new_cs)})
       (delete {app(n, ms, cs)})))
"""


def binder(op, n):
    """Take a binder's bound slot out of its class's slot set.

    The slot rides in the first child's edge, so it is a slot of the *node* but must
    not be one of the class: removing it from the edge to the leader is what makes
    two spellings of the same binder alpha-equivalent.
    """
    rest = " ".join(f"m{i} c{i}" for i in range(2, n + 1))
    node = f'(App{n} "{op}" mvar (Var 0) {rest})'
    return f"""\
(rule ((RenamesToLeader {node} ml l)
       (= v (map-get mvar 0)))
      ((RenamesToLeader {node} (inverse (map-remove (inverse ml) v)) l)))
"""


def main():
    out = [
        ";;; GENERATED by slotted-experiments/gen-node-rules.py -- do not edit.",
        ";;;",
        ";;; The rules that name each child position, emitted once per arity. Add an",
        ";;; arity to ARITIES in the generator and re-run.",
        f";;; Arities: {', '.join(map(str, ARITIES))}",
        "",
    ]
    for n in ARITIES:
        out += [
            f";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
            f";;; arity {n}",
            f";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
            "",
            constructor(n),
            ";; every class holding a node has a self-loop, so a query can reach it",
            self_loop(n),
            ";; alpha-finder: two nodes equal up to renaming, one eliminated",
            alpha_finder(n),
            ";; the same solve kept as a symmetry, non-destructively",
            symmetry_finder(n),
            ";; migration: move a follower's node into the leader's frame",
            migration(n),
        ]
        for pos in range(n):
            out += [f";; child-update, position {pos + 1}", child_update(n, pos)]

    out += [
        ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
        ";;; binders",
        ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
        "",
    ]
    for op, n in BINDERS:
        out += [f';; `{op}` binds its first child\'s slot (arity {n})', binder(op, n)]

    OUT.write_text("\n".join(out))
    print(f"wrote {OUT} ({len(OUT.read_text().splitlines())} lines, "
          f"arities {', '.join(map(str, ARITIES))})")


if __name__ == "__main__":
    main()
