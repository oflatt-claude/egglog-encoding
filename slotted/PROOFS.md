Proofs for the slotted encoding: the proof format over surface terms, the checker
that verifies it against the slotted source program, and how a proof is obtained
from the egglog proof encoding.

# Overview

A slotted program compiled with `slotted-egglog.py --proofs` runs under egglog's
term/proof encoding (`egglog/src/proofs/proof_encoding.md`). Every `=` and
`renaming-=` claim becomes a `(prove ...)`, and egglog extracts a proof of it over
the *encoded* program: terms like `(Add (map-of 0 1) (SlottedVar_0 0) ...)`, rows of
`RenamesToLeader`, firings of the maintenance rules. That proof is sound but
unreadable, and it is a proof about the encoding, not about the program a person
wrote. So it is translated into the format below, whose terms are the surface
terms of `slotted/LANGUAGE.md` and whose rules are the program's own rewrites and
unions, and the translated proof is checked by an independent checker that knows
nothing about the encoding.

```
source.egg --proofs-->  encoded.egg --egglog --proofs--> egglog proof
                                                             |  translate
                                                             v
                                        slotted proof --check--> surface claim
```

# Terms

A term is what the language writes: a constructor applied to children, a payload
literal, or a slot `$n`. A binder column holds the bound slot as a plain `$n`.
Terms are compared syntactically. There is no alpha-equivalence in the checker:
`(Lam $0 $0)` and `(Lam $1 $1)` are different terms, and a proof that relates them
says how (see *Shift*).

# Propositions

A proposition is `t1 = m·t2`: the term `t1` equals the term `t2` with its slots
renamed by `m`. `m` is a finite bijection on slot names, the identity outside its
support, and `m·t2` renames *every* slot occurrence in `t2`, bound and free alike.
This is the term-level reading of the paper's applied e-class `m * c` and of the
encoding's `RenamesToLeader f m l`, which reads `f = m * l`.

`t1 = id·t2` with the identity renaming is plain equality.

What a proposition claims is `m` on the slots of `t2`: two propositions whose
renamings agree there say the same thing, and the checker compares a derived step
with the stated one after restricting both. The stored renaming is nevertheless
kept whole. Trans and Shift compose it with others whose images leave the slots
of `t2` -- `t2 = n·t3` may send a slot of `t3` to one `t2` does not have, when
that slot is redundant -- and the whole permutation says what the composite means
there. Any extension of `m` beyond the slots of `t2` is sound (renaming respects
equality), so a proof is free to carry the one its derivation needs.

# Justifications

The egglog proof format's justifications, with the renaming threaded through, plus
one new step.

**Fiat.** `t = id·t` for a term the program built -- a slot, a payload literal, or a
subterm of a `let` or a `union` -- and `a = id·b` for a source `(union a b)`, in
either direction. Reflexivity is not assumed for terms the program never built.

**Rule.** `(rewrite L R :name n :when (...))` instantiated by a substitution σ from
the rule's variables to terms. A pattern variable maps to a term; a slot literal
`$x` maps to a slot. Premises, in order: a proof `t = m·L[σ]` for the root pattern
(any `m`: the rule is renaming-invariant), then for each `:when` pattern
`(= v call)` a proof `σ(v) = id·call[σ]`. Each `free`/`not-free` condition is
evaluated on σ, which needs the binder positions of the constructors; `!=` holds
when the two terms differ. A slot literal that occurs only on the right-hand side
is *minted*: σ binds it to a slot that occurs nowhere in any other binding. The
conclusion is `L[σ] = id·R[σ]` or its reverse, or `s = id·s` for a subterm `s` of
either side. A right-hand side `subst` is not supported.

**Sym.** From `t1 = m·t2`, `t2 = m⁻¹·t1`. This carries the slotted e-graph's closure
under renaming: renaming both sides of an equation by `m⁻¹` is sound, and that is
what moves the renaming to the other side.

**Trans.** From `t1 = m·t2` and `t2 = n·t3`, `t1 = (m∘n)·t3`, where `(m∘n)·t` is
`m·(n·t)`. The middle term must be syntactically the same in both.

**Congr.** From `t1 = m·F(..., c, ...)` and `c = n·c'`, `t1 = m·F(..., n·c', ...)`:
the child at the given position is replaced by the renamed term the child proof
equates it with.

**Shift.** From `t1 = m·t2`, `t1 = (m∘σ⁻¹)·(σ·t2)` for any finite bijection σ. It
renames one side and adjusts the renaming to match, so it changes spelling only.
Applied to bound slots it is alpha-renaming: `(Lam $0 $0) = {1↦0}·(Lam $1 $1)` is
one Shift from reflexivity, and the checker never had to know that `$1` was bound.

Closure under renaming of both sides is derivable: Sym, Shift, Sym.

# Claims

`(check (= a b))` is proved by `a = m·b` with `m` the identity on the free slots of
`b`. `(check (renaming-= a b))` is proved by `a = m·b` for any `m`. Negative claims
and the other claim forms are checked, not proved.

# What the checker reads

The compiler publishes the source program in hidden rows next to the layout
metadata: `SlottedCarrier`, `SlottedRuleSource`, `SlottedLetSource`,
`SlottedUnionSource`, `SlottedClaimSource` (the exact conventions are in
`slotted/ENCODING.md`). Binder positions come from `SlottedBinderLayout`. The
checker resolves globals through the `let` rows, parses each rewrite's source
form, and checks a proof against those alone; it never looks at the encoded tables.

# Translation

The translator (`egglog/src/proofs/slotted/translate.rs`) maps an egglog proof over
the encoded program to a slotted proof. Its core is a denotation `dec` from encoded
terms to surface terms: `dec(F(m1, c1, ..., mk, ck)) = F(m̂1·dec(c1), ...)`, where
each edge is completed to a bijection by naming the child's redundant slots with
fresh names, and `dec(SlottedVar_N 0)` is `$0`. Every encoded fact then denotes a
proposition, and every maintenance rule firing has a fixed derivation:

| encoded fact | proposition |
| --- | --- |
| egglog equality `a = b` | `dec(a) = id·dec(b)` |
| `RenamesToLeader a m b`, `Equated a m b`, `ShapeEqual a m b` | `dec(a) = m̂·dec(b)` |
| `g` in `EclassGroup c`, `Reading c _ g` | `dec(c) = ĝ·dec(c)` |
| `Invocation c n a` | `dec(a) = n̂·dec(c)` |
| slot `r` of `c` outside `ClassSlots c` | `dec(c) = {r↦r'}·dec(c)` for fresh `r'` |

The last row is a *redundancy certificate*. It is derived on demand from the
derivation of the `ClassSlots` row: the merge chain of intersections says which
`set` dropped the slot, and transport along an edge and group slot closure each
have a short Sym/Shift/Trans derivation. Group membership is derived through a
provenance-aware closure, since the stored group is closed and an element has to
be expressed as a product of symmetries the translator has proofs for.

| rule firing | derivation |
| --- | --- |
| orient, restate on narrower slots | Shift, with certificates for the slots the restriction dropped |
| self-equation, self-edge into the group | the premise, respelled |
| transitivity | Trans of the first edge with the second |
| one leader per follower | Sym, Trans, Shift |
| migration | Sym of the edge, Shift by the total extension `R` |
| child update | Congr with the child's edge |
| binder scope | Shift away from the bound slot, which is not free on the left |
| shape collision, node symmetries | Congr with the children's symmetries, then Shift by `back` |
| invocation naming | the edge, then Congr with the symmetry `coset-min` chose |
| user rewrite | Rule, with the root premise built from the atom rows by Congr and Shift |
| claim | the two terms' atom proofs, the class equality, and the `coset-same` symmetry |

# Running

`egglog --slotted-proofs program.egg` runs a program the compiler emitted with
`--proofs`: each `(prove ...)` is translated and checked, and the slotted proof is
printed. `python3 slotted/slotted-egglog.py test.egg --proofs` compiles and runs a
slotted source that way, `python3 slotted/run-slotted-tests.py --slotted-proofs`
does it for the whole test suite, and `make slotted-proof-tests` builds egglog
first. Sources that use `subst` are skipped: it has no proof translation.
