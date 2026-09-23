Encodes a slotted e-graph — one where a class carries named slots and nodes are equal up to renaming them — as ordinary egglog tables and rules.

# Overview

A slotted e-graph, from Schneider et al., *Slotted E-Graphs* (PLDI 2025), gives every e-class a set of **slots** and lets a
node reach a child under a **renaming** of them. That is what makes
`(lam $0 $0)` and `(lam $1 $1)` one class rather than two, without a separate
alpha-equivalence pass.

Egglog has no notion of a slot, so the encoding puts one in: a child column
becomes *two* columns, a renaming and a class, and a handful of relations track
which invocation of a class a value stands for. Everything is ordinary egglog —
the compiler emits it, nothing in the Rust is slotted-aware beyond a few
primitives on renamings.

`slotted/LANGUAGE.md` is the source language a person writes. This file is the
level below it: what that language compiles *to*, and why each table exists.

The running example is:

```
(sort Math)
(constructor Add (Math Math) Math)
(let a (Add $0 $1))
(let b (Add $1 $0))
(union a b)
(rewrite (Add x y) (Add y x) :name "comm")
```

Run `python3 slotted/slotted-egglog.py FILE.egg --desugar` on any program to see
its full encoding; every listing below is real output, with comments trimmed.

# The idea in one paragraph

A slotted class is **not** one egglog value. It is a set of values — one per
*invocation*, that is, per way of naming the class's slots — related by
`RenamesToLeader` and *not* by egglog's `union`. One invocation is the leader;
the rest are deleted once they are known to be renamings of it. So "are these
two terms equal?" is not egglog's `=`: it asks whether the two reach the leader
by the *same* renaming.

# Per-carrier tables

One family per declared equality sort. A program declaring several gets one
indexed family each — `RenamesToLeader_0`, `RenamesToLeader_1` — and nothing is
shared between them but the renaming sort itself.

```
(sort Renaming (Map i64 i64))
(sort Math)
(constructor Var (i64) Math)
(relation RenamesToLeader (Math Renaming Math))
(relation Equated (Math Renaming Math))
(function ClassSlots (Math) Renaming :merge (map-intersect old new))
(relation SubstPending (Math Renaming Renaming Math))
```

**`Renaming`** is a partial injection on slots, spelled as a map from `i64` to
`i64`. `compose`, `inverse`, `map-image` and `map-domain` are primitives on it.

**`Var`** is the one variable class. Every variable is `(Var 0)` reached by an
edge `0 -> s`, so *which* slot a variable names lives in the renaming and not in
the value. Its class slots are seeded outright:

```
(set (ClassSlots (Var 0)) (map-of 0 0))
```

**`RenamesToLeader f m l`** reads `f = m * l`: `m` carries `l`'s slots to `f`'s.
A class is a connected component of this relation, and its leader is the
component's canonical member. A **self-loop** `(RenamesToLeader c p c)` with `p`
not the identity is a **symmetry** — the class is equal to itself under a
permutation of its slots, which is how the example's `union` records that `Add`
is commutative.

**`Equated`** holds the same fact with no orientation chosen. Orientation is a
function of value order, so a row oriented before a merge can be backwards after
one; `Equated` is what the machinery derives `RenamesToLeader` from, and a stale
row is deleted and re-derived rather than repaired in place. Repairing in place
does not converge — transitivity keeps re-deriving the backwards row.

```
(rule ((Equated a m b) (!= a b) (= a (ordering-max a b)))
      ((RenamesToLeader a m b)) :ruleset slotted)
(rule ((RenamesToLeader f m l) (!= f l) (= l (ordering-max f l)))
      ((delete (RenamesToLeader f m l))) :ruleset slotted)
```

**`ClassSlots c`** is the slots the class actually depends on, as an identity
renaming. It is held directly rather than read off a self-loop, because a
self-loop is derived from a *node* and so can name more slots than the class
has. Its merge is `map-intersect`, so it only ever shrinks — which is what makes
a slot **redundant**: union two invocations that disagree on a slot and the
class stops depending on it. A slotless class has one invocation, so all its
spellings are the same term.

# Per-constructor machinery

A child column expands to a renaming column and a class column, so
`(constructor Add (Math Math) Math)` becomes:

```
(constructor Add (Renaming Math Renaming Math) Math)
```

and `(Add $0 $1)` is stored as
`(Add (map-of 0 0) (Var 0) (map-of 0 1) (Var 0))`. Each constructor then gets
one block of rules. Three are worth reading.

**Class slots**, an upper bound the merge narrows:

```
(rule ((= e1 (Add m1 c1 m2 c2)))
      ((set (ClassSlots e1) (map-union (map-image m1) (map-image m2)))) :ruleset slotted)
```

**A self-loop**, so a query can reach any class that holds a node:

```
(rule ((= e1 (Add m1 c1 m2 c2))
       (= m (map-union (map-image m1) (map-image m2))))
      ((RenamesToLeader e1 m e1)) :ruleset slotted)
```

**The alpha-finder**, which is the heart of it: two nodes with the same children
that differ only by a renaming are one invocation, so one is deleted and the
renaming between them recorded.

```
(rule ((= e1 (Add m1_o c1 m2_o c2))
       (= e2 (Add b1 c1 b2 c2))
       (= e1 (ordering-max e1 e2))
       (RenamesToLeader c1 sym1 c1)
       (RenamesToLeader c2 sym2 c2)
       (= m1 (compose m1_o sym1))
       (= m2 (compose m2_o sym2))
       (= m (find-mapping m1 m2 b1 b2))
       ...)
      ((Equated e1 m e2)
       (delete (Add m1_o c1 m2_o c2))) :ruleset slotted)
```

`find-mapping` solves for the renaming carrying one tuple of edges onto another.
The `RenamesToLeader c sym c` atoms are the children's *symmetries*: two nodes
may agree only after permuting a child's slots, so the solve quantifies over the
group. The same solve is kept non-destructively by a second rule, which is how a
child's symmetry becomes the parent's.

Because this deletes rows, a class keeps exactly one node per shape — which is
why a claim about a term matches it rather than spelling it out. A term the
e-graph holds need not have a row under the spelling you wrote.

# Binders

`:binder i` marks a child column whose slot the node binds. The bound slot is
stored as an edge `0 -> s` to `(Var 0)` like any other, so a binder is not a
different kind of column — what differs is that the slot is taken out of the
class's slot set over the column the binder **covers**, which is the one right
after it. `let` binds in its body and leaves its value's occurrence free.

When a bound slot collides with a free one the machinery renames the bound one
first, to a slot the node does not use, which keeps it alpha-renameable.

# Matching

egglog finds the e-nodes a rule's left-hand side matches; what the match says about
**slots** is a set of constraints on those nodes, solved by a handful of primitives
inside the same query. A rule reads like this (the SDQL library's `sum-fact-3`,
`(Sum R $x $y (Sing e1 e2)) -> (Sing e1 (Sum R $x $y e2))` when `$x` and `$y` are not
free in `e1`):

```
(rule ((= cls_p (Sum e0_R cls_R e0_lit_x (Var 0) e0_lit_y (Var 0) e0_t1 cls_t1))
       (= atom_p (atom "_p" (root "_p" (ClassSlots cls_p))
                            (child "R" e0_R (ClassSlots cls_R))
                            (bound "$x" e0_lit_x) (bound "$y" e0_lit_y)
                            (child "_t1" e0_t1 (ClassSlots cls_t1))))
       (= cls_t1 (Sing e1_e1 cls_e1 e1_e2 cls_e2))
       (RenamesToLeader cls_t1 sym_t1 cls_t1)
       (= atom_t1 (atom "_t1" (root "_t1" (ClassSlots cls_t1) sym_t1)
                              (child "e1" e1_e1 (ClassSlots cls_e1))
                              (child "e2" e1_e2 (ClassSlots cls_e2))))
       (= f (frame-join atom_p atom_t1))
       (Idx choice)
       (= m (refine (anchor f "_p") choice))
       (not-free m "$x" (names "e1"))
       (not-free m "$y" (names "e1")))
      ((let built_sum (Sum (ren m "R") cls_R (ren m "$x") (Var 0) (ren m "$y") (Var 0) (ren m "e2") cls_e2))
       (let built_sum_slots (node-slots m (names "R") (names "$x" "$y" "e2") (names "$x" "$y")))
       (let built_sing (Sing (ren m "e1") cls_e1 built_sum_slots built_sum))
       (union built_sing cls_p)) :name "sum-fact-3")
```

Two atoms, egglog's own; one `atom` value per atom saying what its columns mean;
their join, anchored at the root so the root's renaming is the identity; one
refinement; the conditions; the right-hand side built in the frame's slots and
unioned with the root. Names in quotes are the pattern's own variables and literals (`_p` and `_t1`
are the flattener's, which no author's name begins with), so a frame is keyed by the
words the rule was written in.

## The frame

A **frame** is the closure of equations between *slot occurrences*: `Node(a, s)`,
slot `s` of the e-node matched at the atom labelled `a`; `Var(v, t)`, slot `t` of
the class variable `v` is bound to; `Lit("$x")`, a slot the pattern wrote or the
right-hand side minted. Its classes are the pattern's slots, numbered in canonical
order. Two **cliques** may never collapse: the slots of one e-node (and of one class,
so a renaming stays injective), and the set of distinct literals. `sort/frame.rs` in
the egglog crate holds the algebra; the primitives are:

| primitive | what it says |
| --- | --- |
| `(root "p" cs [sym])` | the atom's node is an invocation of `p`'s class, whose exact slots are `cs`; through the symmetry `sym` if `p` was matched before |
| `(child "v" e cs [sym])` | the column with edge `e` carries `v`: `Node(a, e(t)) = Var(v, t)` for each class slot `t` |
| `(lit "$x" e)`, `(bound "$x" e)` | the column is the literal `$x`: `Node(a, e(0)) = Lit("$x")`; `bound` is a binder column, whose literal is node data and not carried into refinement |
| `(leaf e)` | a payload leaf reached through its own class: node slots, nothing more |
| `(atom "a" binding...)` | one atom's constraints, closed; fails if its own columns break a clique |
| `(frame-join f g)` | both frames' constraints, closed; fails where a clique breaks. Associative and commutative |
| `(anchor f "p")` | the frame spelled in `p`'s slot names: the rule's root, so its renaming is the identity and the action is egglog's `union` |
| `(refine f i)` | the `i`-th consistent merging of the classes refinement may touch, `0` the identity; fails past the last |
| `(mint f (names "$z"...))` | fresh slots for a right-hand side, apart from everything named |
| `(free m "$x" (names v...))`, `(not-free ...)` | is the literal's slot in one of the variables' images |
| `(same m "a" "b")`, `(bool-same ...)` | the two variables are one invocation |
| `(ren m "v")` | `v`'s renaming into the pattern's slots; a literal comes back as `{0 -> slot}` |
| `(node-slots m uncovered covered bound)` | a built node's free slots from its named columns; `(without m slots bound)` for a built child under a binder |

## The contract

What a compiled rule asserts, clause by clause; `compile_query_frames` and
`compile_rule` in `slotted-encoder.py` name these where they emit them, and
`mutations.py` breaks one at a time and requires the curated corpus to notice.

**C1. A pattern variable is an invocation.** `x` is a class `cls_x` and a renaming
`(ren m "x")` of that class's slots into the pattern's. Two occurrences agree when
they reach one class by renamings that differ at most by a symmetry of it
(Definition 6); equal renamings alone is too weak, equal classes alone is wrong.

**C2. Atoms, and the frame.** The left-hand side is flattened into depth-1 atoms,
one per e-node, every child a variable or a literal. Each atom's columns are one
`atom`, and the frame is their `frame-join`. Nothing is ordered: an atom is a function
of its own node's edges, the join is associative and commutative, and the left-nested
tree the compiler writes is a hint to prune early, not a meaning. A slot no equation
reaches is a placeholder, a class of its own.

**C3. Atoms are written in a connected order.** `connected_order` puts each atom
after one it shares a variable with, parent before child, so the join tree fails as
early as it can. Under frames this is only a heuristic.

**C4. A variable's renaming is no wider than its class.** Every binding carries the
class's exact slots, `(ClassSlots cls)`, and the frame's occurrences of `v` are those
slots and no others; a node may carry a slot its class has made redundant, and that
slot is the node's alone.

**C5. Repeated occurrences are compared up to symmetry.** A further occurrence of a
bound variable joins its own symmetry row `(RenamesToLeader cls_x sym_x cls_x)` and
hands `sym_x` to its binding; one row per group element, so the match quantifies over
the group.

**C6. Where two atoms agree on a variable, their occurrences are one.** The join
identifies `Node(a, e(t))` and `Node(b, e'(t))` through `Var(v, t)`, which is the
reference's `unify`, and fails only where that breaks a clique.

**C7. A slot literal is solved, and different literals differ.** `$x` in a column is
read off the node's slot there; the same literal written twice names one slot; two
different literals are two classes, by the literal clique. In a binder column a
literal is the bound slot (`bound`), and only a literal may stand there.

**C8. Placeholders are refined last.** `refine` enumerates every consistent way to
merge the classes a variable or a carried literal reaches -- never two literals, never
two slots of one node or class -- and the rule reads one per `(Idx choice)`; `0` is
the identity, so running out of indices loses matches and never invents one. This is
the reference's `final_refine`.

**C9. Conditions are read after refinement.** `free` and `not-free` are facts over the
refined frame. A matched binder's slot may be read as any name, a free variable's
included, so a rule whose right-hand side rebinds such a slot over a variable matched
outside the binder owes `(not-free $s v)`; `capture_guards` derives what it owes.

**C10. A right-hand-side slot the pattern never pins is fresh.** `mint` adds it after
refinement, apart from every slot the match named; the reference writes
`Slot::fresh()` where the encoding has to invent a name.

**C11. An action is a union in the root's frame.** The frame is anchored at the
rule's root, so the root's renaming is the identity by construction, and the right-hand
side, built bottom-up in the frame's slots -- one `let` per node and one `node-slots`
for its slot set -- is an invocation in the root's own frame. egglog's `union` is then
exactly the equation the rule means, and the machinery's `ClassSlots` merge makes any
slot the two sides disagree on redundant. The one action that is not a union is a
right-hand side that is a bare variable `a`: `a`'s renaming need not be the identity,
so the rule states `(Equated cls_root (ren m "a") cls_a)` and the machinery orients it.

**C12. A right-hand side that is a call is answered by a primitive.** `(subst body $x
t)` cannot be built as a node: `slotted-subst` copies one representative of the body
-- the smallest term, and among equal sizes the least canonical spelling, so every run
copies the same one -- and returns an invocation, which `SubstPending` carries back
into the root's frame.

# Where the pieces live

| path | what it is |
| --- | --- |
| `slotted/LANGUAGE.md` | the source language: every form and why it exists |
| `slotted/slotted-egglog.py` | the compiler — a program in that language to egglog |
| `slotted/slotted-encoder.py` | the encoding itself: the tables above, and rule compilation |
| `slotted/tests/` | tests written in the source language |
| `slotted/xdiff/` | the differential harness against `memoryleak47/slotted-egraphs` |
| `slotted/xmulti/` | the reference oracle, pinned to an exact revision |
| `slotted/paper_fixtures.py` | the paper's ten SDQL workloads from the artifact: translation, Table 1's numbers, the generated tests |
| `slotted/eval.py` | the paper's two case studies -- the array goal and all ten SDQL workloads -- on the encoding and on the reference through both of its matchers; `make slotted-eval` |

Nothing here is hand-maintained egglog: the machinery is generated from the
constructors a program declares, so a worked example is a program you run
through the compiler rather than a file that can drift from it.
