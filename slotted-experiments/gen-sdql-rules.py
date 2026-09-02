#!/usr/bin/env python3
"""Compile the reference `sdql` rewrite rules into the slotted encoding.

The rules are the table below; the recipe that compiles them is
`slotted-experiments/slotted-encoder.py`, which `tests/slotted-user-rules.egg`
documents.  What `sdql` adds over the differential harness's two-child `App2`/`App3`
atoms is the per-language constructors of `slotted-experiments/languages/sdql.egg`,
which have one to six children and payload columns, and with them four cases the
harness's corpus does not reach:

  * a PAYLOAD LEAF in a child position -- `0`, `mult`.  Its row is never deleted
    or migrated, so it is a stable handle, but its class's canonical value need
    not be that row, so the atom joins `(RenamesToLeader (Num 0) _ C)` and uses
    `C` for the child rather than writing the leaf into the column;
  * a BUILT BINDER node.  Its slots are its edges' images MINUS what it binds,
    or the parent's edge to it names slots the child's class does not have;
  * an RHS slot the LHS never pinned -- `get-to-sum`'s `$k`, `$v`.  One
    `find-mapping-total` over a domain of that size mints them, avoiding every
    slot the pattern named;
  * an arity other than two, everywhere.

Atoms are compiled in pre-order from the LHS root, which is already the
connectivity the recipe requires.  `connected_order`'s further preference -- a
binder is not the atom that fixes slots(pattern) -- is not followed: most `sdql`
rules are rooted at a binder, and taking the root first pins each bound slot off
its own edge instead of minting a name for it.  M7 in
`tests/slotted-user-rules.egg` is the same shape.

Terms in the table below:

    "?x"            a pattern variable
    "$x"            a slot literal -- a binder column, or the reference's
                    `(var $x)` in an ordinary child column.  Both are the class
                    `(Var 0)` reached by an edge `0 -> $x`
    ("Op", ...)     a node; payload columns take Python literals, so `("Num", 0)`
                    and `("Symbol", "mult")` are the reference's `0` and `mult`

    python3 slotted-experiments/gen-sdql-rules.py
"""

import os
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
enc = __import__("slotted-encoder")

LANG = enc.TermLang.from_language(enc.read_language(pathlib.Path("slotted-experiments/languages/sdql.egg")))

OUT = pathlib.Path(os.environ.get("SDQL_OUT", "tests/slotted-sdql-rules.egg"))

# Re-introducible bugs, so the checks in `tests/slotted-sdql-rewrites.egg` can be
# shown to test what they were written for.  The encoder's flags, under the same
# names `XDIFF_BUGS` takes in `slotted-experiments/xdiff/xdiff.py`.
#   SDQL_BUGS=slot-late   a slot literal checked after the renaming, not with it
#   SDQL_BUGS=root-only   an atom's renaming solved from its root alone
#   SDQL_BUGS=wide-kids   a variable used at the matched node's slots, not its class's
#   SDQL_BUGS=no-guard    the slot side conditions dropped
# Set SDQL_OUT to keep a mutant out of the tree.
BUGS = {b for b in os.environ.get("SDQL_BUGS", "").split(",") if b}


# ------------------------------------------------------------------- the rules
# `(name, lhs, rhs)`, optionally `conds` and `fresh`.  Each `conds` entry is
# `(slot, pvar)` reading "that slot is not among the variable's slots", the
# reference's `!subst[v].slots().contains(&Slot::named(s))`.  `fresh` names RHS
# slots the LHS never pinned, which have to be minted.
#
# Ported from `sdql_rules()` in `slotted-egraphs/benches/sdql.rs`, minus `beta`.
RULES = [
    ("mult-assoc1", ("Mult", ("Mult", "?a", "?b"), "?c"), ("Mult", "?a", ("Mult", "?b", "?c"))),
    ("mult-assoc2", ("Mult", "?a", ("Mult", "?b", "?c")), ("Mult", ("Mult", "?a", "?b"), "?c")),
    ("sub-identity", ("Sub", "?e", "?e"), ("Num", 0)),
    ("add-zero", ("Add", "?e", ("Num", 0)), "?e"),
    ("sub-zero", ("Sub", "?e", ("Num", 0)), "?e"),
    ("eq-comm", ("Equality", "?a", "?b"), ("Equality", "?b", "?a")),
    ("mult-app1", ("Mult", "?a", "?b"), ("Binop", ("Symbol", "mult"), "?a", "?b")),
    ("mult-app2", ("Binop", ("Symbol", "mult"), "?a", "?b"), ("Mult", "?a", "?b")),
    ("add-app1", ("Add", "?a", "?b"), ("Binop", ("Symbol", "add"), "?a", "?b")),
    ("add-app2", ("Binop", ("Symbol", "add"), "?a", "?b"), ("Add", "?a", "?b")),
    ("sub-app1", ("Sub", "?a", "?b"), ("Binop", ("Symbol", "sub"), "?a", "?b")),
    ("sub-app2", ("Binop", ("Symbol", "sub"), "?a", "?b"), ("Sub", "?a", "?b")),
    ("get-app1", ("Get", "?a", "?b"), ("Binop", ("Symbol", "getf"), "?a", "?b")),
    ("get-app2", ("Binop", ("Symbol", "getf"), "?a", "?b"), ("Get", "?a", "?b")),
    ("sing-app1", ("Sing", "?a", "?b"), ("Binop", ("Symbol", "singf"), "?a", "?b")),
    ("sing-app2", ("Binop", ("Symbol", "singf"), "?a", "?b"), ("Sing", "?a", "?b")),
    ("unique-app1", ("Unique", "?a"), ("App", ("Symbol", "uniquef"), "?a")),
    ("unique-app2", ("App", ("Symbol", "uniquef"), "?a"), ("Unique", "?a")),
    (
        "let-binop3",
        ("Let", "?e1", "$x", ("Binop", "?f", "?e2", "?e3")),
        ("Binop", "?f", ("Let", "?e1", "$x", "?e2"), ("Let", "?e1", "$x", "?e3")),
    ),
    (
        "let-binop4",
        ("Binop", "?f", ("Let", "?e1", "$x", "?e2"), ("Let", "?e1", "$x", "?e3")),
        ("Let", "?e1", "$x", ("Binop", "?f", "?e2", "?e3")),
    ),
    ("let-apply1", ("Let", "?e1", "$x", ("App", "?e2", "?e3")), ("App", "?e2", ("Let", "?e1", "$x", "?e3"))),
    ("let-apply2", ("App", "?e2", ("Let", "?e1", "$x", "?e3")), ("Let", "?e1", "$x", ("App", "?e2", "?e3"))),
    ("if-mult2", ("Mult", "?e1", ("IfThen", "?e2", "?e3")), ("IfThen", "?e2", ("Mult", "?e1", "?e3"))),
    ("if-to-mult", ("IfThen", "?e1", "?e2"), ("Mult", "?e1", "?e2")),
    ("mult-to-if", ("Mult", ("Equality", "?e1_1", "?e1_2"), "?e2"), ("IfThen", ("Equality", "?e1_1", "?e1_2"), "?e2")),
    (
        "sum-fact-1",
        ("Sum", "?R", "$x", "$y", ("Mult", "?e1", "?e2")),
        ("Mult", "?e1", ("Sum", "?R", "$x", "$y", "?e2")),
        [("$x", "?e1"), ("$y", "?e1")],
    ),
    (
        "sum-fact-2",
        ("Sum", "?R", "$x", "$y", ("Mult", "?e1", "?e2")),
        ("Mult", ("Sum", "?R", "$x", "$y", "?e1"), "?e2"),
        [("$x", "?e2"), ("$y", "?e2")],
    ),
    (
        "sum-fact-3",
        ("Sum", "?R", "$x", "$y", ("Sing", "?e1", "?e2")),
        ("Sing", "?e1", ("Sum", "?R", "$x", "$y", "?e2")),
        [("$x", "?e1"), ("$y", "?e1")],
    ),
    ("sing-mult-1", ("Sing", "?e1", ("Mult", "?e2", "?e3")), ("Mult", ("Sing", "?e1", "?e2"), "?e3")),
    ("sing-mult-2", ("Sing", "?e1", ("Mult", "?e2", "?e3")), ("Mult", "?e2", ("Sing", "?e1", "?e3"))),
    ("sing-mult-3", ("Mult", ("Sing", "?e1", "?e2"), "?e3"), ("Sing", "?e1", ("Mult", "?e2", "?e3"))),
    ("sing-mult-4", ("Mult", "?e2", ("Sing", "?e1", "?e3")), ("Sing", "?e1", ("Mult", "?e2", "?e3"))),
    (
        "sum-fact-inv-1",
        ("Mult", "?e1", ("Sum", "?R", "$k", "$v", "?e2")),
        ("Sum", "?R", "$k", "$v", ("Mult", "?e1", "?e2")),
    ),
    (
        "sum-fact-inv-3",
        ("Sing", "?e1", ("Sum", "?R", "$k", "$v", "?e2")),
        ("Sum", "?R", "$k", "$v", ("Sing", "?e1", "?e2")),
    ),
    (
        "sum-sum-vert-fuse-1",
        ("Sum", ("Sum", "?R", "$k2", "$v2", ("Sing", "$k2", "?body1")), "$k1", "$v1", "?body2"),
        ("Sum", "?R", "$k2", "$v2", ("Let", "$k2", "$k1", ("Let", "?body1", "$v1", "?body2"))),
    ),
    (
        "sum-sum-vert-fuse-2",
        ("Sum", ("Sum", "?R", "$k2", "$v2", ("Sing", ("Unique", "?key"), "?body1")), "$k1", "$v1", "?body2"),
        ("Sum", "?R", "$k2", "$v2", ("Let", ("Unique", "?key"), "$k1", ("Let", "?body1", "$v1", "?body2"))),
    ),
    (
        "sum-range-1",
        ("Sum", ("Range", "?st", "?en"), "$k", "$v", ("IfThen", ("Equality", "$v", "?key"), "?body")),
        (
            "Sum",
            ("Range", "?st", "?en"),
            "$k",
            "$v",
            ("IfThen", ("Equality", "$k", ("Sub", "?key", ("Sub", "?st", ("Num", 1)))), "?body"),
        ),
    ),
    (
        "sum-merge",
        ("Sum", "?R", "$k1", "$v1", ("Sum", "?S", "$k2", "$v2", ("IfThen", ("Equality", "$v1", "$v2"), "?body"))),
        ("Merge", "?R", "?S", "$k1", "$k2", "$v1", ("Let", "$v1", "$v2", "?body")),
    ),
    (
        "get-to-sum",
        ("Get", "?dict", "?key"),
        ("Sum", "?dict", "$k", "$v", ("IfThen", ("Equality", "$k", "?key"), "$v")),
        [],
        ["$k", "$v"],
    ),
    (
        "sum-to-get",
        ("Sum", "?dict", "$k", "$v", ("IfThen", ("Equality", "$k", "?key"), "?body")),
        ("Let", "?key", "$k", ("Let", ("Get", "?dict", "$k"), "$v", "?body")),
        [("$k", "?key"), ("$v", "?key")],
    ),
    ("get-range", ("Get", ("Range", "?st", "?en"), "?idx"), ("Add", "?idx", ("Sub", "?st", ("Num", 1)))),
    ("sum-sing", ("Sum", "?e1", "$k", "$v", ("Sing", "$k", "$v")), "?e1"),
    ("unique-rm", ("Unique", "?e"), "?e"),
]


HEADER = """\
;;; GENERATED by slotted-experiments/gen-sdql-rules.py -- do not edit.
;;;
;;; The reference `sdql` rewrite rules -- `sdql_rules()` in
;;; `slotted-egraphs/benches/sdql.rs` -- compiled into the slotted encoding by the
;;; recipe in `tests/slotted-user-rules.egg`.
;;;
;;; `beta` is NOT here: it substitutes, which needs `slotted-subst` and frame
;;; plumbing rather than this compiler.  The other 43 are.
;;;
;;; These are USER rules, so they go in their own ruleset and the machinery is
;;; saturated between finite steps of them:
;;;
;;;     (run-schedule (saturate (run slotted))
;;;                   (repeat N (seq (run sdql 1) (saturate (run slotted)))))
;;;
;;; `tests/slotted-sdql-rewrites.egg` is what checks them.

(include "tests/slotted-lang-sdql.egg")

(ruleset sdql)
"""


# ---------------------------------------------------------------- the compiler
def compile_rule(name, lhs, rhs, conds=(), fresh=()):
    """One rule, through the encoder.  Every `sdql` side condition is negative and
    names one variable, which is the only shape of the encoder's `(want, slot,
    pvars)` this needs."""
    root, atoms = enc.flatten(LANG, lhs)
    atoms = enc.connected_order(LANG, atoms, first=0)
    return enc.compile_rule(
        LANG,
        atoms,
        ("build", root, enc.rhs_of(LANG, rhs)),
        conds=[(False, slot, [pvar]) for slot, pvar in conds],
        fresh=fresh,
        bugs=BUGS,
        tail=f'\n      :ruleset sdql :name "{name}")',
    )


def main():
    out = [HEADER]
    for spec in RULES:
        name, lhs, rhs = spec[0], spec[1], spec[2]
        conds = spec[3] if len(spec) > 3 else ()
        fresh = spec[4] if len(spec) > 4 else ()
        out.append(f"\n;; {name}\n" + compile_rule(name, lhs, rhs, conds, fresh))
    OUT.write_text("\n".join(out) + "\n")
    print(f"wrote {OUT} ({len(RULES)} rules)")


if __name__ == "__main__":
    main()
