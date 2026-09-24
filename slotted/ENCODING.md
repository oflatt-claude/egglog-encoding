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

# Tables, once per sort

Everything in this section is emitted once per equality sort the program declares,
with the sort's position as a suffix: a program with two slotted sorts gets
`RenamesToLeader_0` and `RenamesToLeader_1`, and the two share nothing but the
`Renaming` sort. The listings below drop that suffix, and the `_` the generator puts
in front of its own variables.

```
(sort Renaming (Map i64 i64))
(sort Math)
(constructor Var (i64) Math)
(relation RenamesToLeader (Math Renaming Math))
(relation Equated (Math Renaming Math))
(function ClassSlots (Math) Renaming :merge (map-intersect old new))
(relation SubstPending (Math Renaming Renaming Math))
(function ShapeEqual (Math Renaming Math) Unit :no-merge)
(function Invocation (Math Renaming) Math :merge ((union old new) old))
(function Group (Math) Groups :merge (set-union old new))
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

**`ClassSlots c`** is the slots the class actually depends on, as an identity
renaming. It is held directly rather than read off a self-loop, because it is
what every renaming is spelled on (C15), so it has to come first. Its merge is
`map-intersect`, so it only ever shrinks — which is what makes
a slot **redundant**: union two invocations that disagree on a slot and the
class stops depending on it. A slotless class has one invocation, so all its
spellings are the same term.

**`SubstPending root q mr r`** is a substitution's answer on its way back: `r` is the
class the primitive built and `mr` its renaming, and `q` carries `r`'s slot names into
the root's (C12).

**`ShapeEqual a m b`** is an `Equated` row on its way in. The shape index (C14) states
it from a merge block, which may `set` a function but not insert into a relation.

**`Invocation c m`** names the invocation "`c` read through `m`". Every member of a
class registers under the names of its readings, and the function's merge unions two
members that share one, which is how one invocation stays one egglog value.

**`Group c`** is the class's symmetry group as a set, which is how a node is spelled
once over every reading its children allow rather than once per reading (C14). It holds
what the self-loops hold, and two rules keep the two in step.

## The rules, once per sort

Seventeen rules and one fact, none of which mentions a constructor.

**Orienting `Equated`.** The larger value is the follower, so a leader is the least
member of its component. An equation of a class with itself is a self-loop as it
stands. Either way the renaming is spelled on the two classes' slot sets (C15): an
entry on a slot a class has made redundant says nothing, and left in it makes one edge
many rows and one symmetry many loops, which every closure rule below then multiplies.

```
(rule ((Equated a m b) (!= a b) (= a (ordering-max a b))
       (= csa (ClassSlots a)) (= csb (ClassSlots b)))
      ((RenamesToLeader a (compose csa (compose m csb)) b)) :ruleset slotted)
(rule ((Equated a m b) (!= a b) (= b (ordering-max a b))
       (= csa (ClassSlots a)) (= csb (ClassSlots b)))
      ((RenamesToLeader b (compose csb (compose (inverse m) csa)) a)) :ruleset slotted)
(rule ((Equated a m a) (= cs (ClassSlots a)))
      ((RenamesToLeader a (compose cs (compose m cs)) a)) :ruleset slotted)
```

**Every class has its identity loop**, so a query can reach it and a symmetry join
always has one row.

```
(rule ((= cs (ClassSlots c)))
      ((RenamesToLeader c cs c)) :ruleset slotted)
```

**Dropping a stale edge.** egglog's own `union` can change which of two values is the
larger, leaving an edge that points from the smaller to the larger. It is deleted;
transitivity re-derives it the right way round.

```
(rule ((RenamesToLeader f m l) (!= f l) (= l (ordering-max f l)))
      ((delete (RenamesToLeader f m l))) :ruleset slotted)
```

**Carrying class slots along an edge**, in both directions. One member's slot set,
taken through the renaming, bounds the other's; the merge intersects, so the whole
component settles on the slots every member has.

```
(rule ((RenamesToLeader a m b) (= slots (ClassSlots a)))
      ((set (ClassSlots b) (map-image (compose (inverse m) slots)))) :ruleset slotted)
(rule ((RenamesToLeader a m b) (= slots (ClassSlots b)))
      ((set (ClassSlots a) (map-image (compose m slots)))) :ruleset slotted)
```

**Transitivity.** Two edges compose into an equation. The guard keeps a symmetry of
the middle class from multiplying edges: through a self-loop the rule fires only when
the loop is idempotent, `m * m = m`, which is a loop that drops slots rather than
permuting them, or when the path closes a cycle, which is how a class learns a
symmetry of its own.

```
(rule ((RenamesToLeader e1 m12 e2)
       (RenamesToLeader e2 m23 e3)
       (guard (or (bool-!= e2 e3) (bool= (compose m23 m23) m23) (bool= e1 e3))))
      ((Equated e1 (compose m12 m23) e3)) :ruleset slotted)
```

**One leader per follower.** A follower with edges to two leaders makes the leaders
equal and keeps the edge to the smaller. Two different edges to the *same* leader make
a symmetry of that leader, and the one with the larger renaming goes. Only edges
already spelled on their classes' slots take part: an edge a narrowing has outdated
belongs to the restatement rule below, and two deleting rules must not choose
differently between an edge and its restatement.

```
(rule ((RenamesToLeader a m1 b)
       (RenamesToLeader a m2 c)
       (!= a c) (!= a b)
       (= csa (ClassSlots a)) (= csb (ClassSlots b)) (= csc (ClassSlots c))
       (= m1 (compose csa (compose m1 csb)))
       (= m2 (compose csa (compose m2 csc)))
       (= (ordering-max b c) b)
       (guard (or (bool-!= b c)
                  (and (bool= b c) (bool-!= m1 m2) (bool= (ordering-max m1 m2) m1)))))
      ((delete (RenamesToLeader a m1 b))
       (Equated b (compose (inverse m1) m2) c)) :ruleset slotted)
```

**A follower keeps no symmetries.** Every rule that reads a group reads it off a class
a row or a child column names, and those are leaders, so a loop on a value that has a
leader is a copy nothing reads. One is derived per member per group element, which is
most of the edge relation.

```
(rule ((RenamesToLeader f g f) (RenamesToLeader f m l) (!= f l))
      ((delete (RenamesToLeader f g f))) :ruleset slotted)
```

**A renaming outlives a narrowing.** `ClassSlots` only ever shrinks, and an edge
oriented before a class dropped a slot still names it. The edge is restated on what the
classes have now; this is the one rule that deletes an edge without a leader having
changed.

```
(rule ((RenamesToLeader f m l)
       (= csf (ClassSlots f)) (= csl (ClassSlots l))
       (= m2 (compose csf (compose m csl)))
       (!= m m2))
      ((delete (RenamesToLeader f m l))
       (RenamesToLeader f m2 l)) :ruleset slotted)
```

**One variable class.** `(Var v)` with `v` other than 0 is restated as `(Var 0)` under
`{0 -> v}` and deleted. The variable class holds no constructor node, so it gets its
self-loop as a fact.

```
(rule ((= e (Var v)) (!= v 0))
      ((Equated e (map-insert (map-empty) 0 v) (Var 0))
       (delete (Var v))) :ruleset slotted)
(RenamesToLeader (Var 0) (map-insert (map-empty) 0 0) (Var 0))
```

**The same invocation is one value.** A member reaching leader `c` by `m` registers
under `Invocation c (compose m sym)` for every symmetry `sym` of `c`, and two members
that register under one name are unioned by the function's merge. This is where "the
same class by the same renaming" becomes egglog equality, and why a claim's `=`
compares renamings up to a symmetry row. Nothing else depends on it, since rows live
on leaders and parents are rewritten to leaders; what it keeps small is the graph. A
built node whose class already existed is a value of its own until it is identified
with the member it duplicates, and every such value carries an edge and slots that
every rule over the graph then reads. The cost is one `set` per edge per element of the
leader's group.

```
(rule ((RenamesToLeader a m c)
       (RenamesToLeader c sym c))
      ((set (Invocation c (compose m sym)) a)) :ruleset slotted)
```

**A substitution's answer.** Once the class the primitive built has its slot set, the
pending row becomes an equation between the root and that class in the root's slot
names.

```
(rule ((SubstPending root q mr r) (= cs (ClassSlots r)))
      ((Equated root (compose q (compose mr cs)) r)) :ruleset slotted)
```

**A shape collision.** What the shape index's merge block wrote enters the class
relation like any other equation.

```
(rule ((ShapeEqual a m b))
      ((Equated a m b)) :ruleset slotted)
```

**The group and the self-loops.** Each is derived from the other: a loop is an element
of the group, and an element of the group is a loop. Rules read the loops; the shape
primitives read the group.

```
(rule ((RenamesToLeader c g c))
      ((set (Group c) (set-of g))) :ruleset slotted)
(rule ((Idx i) (= s (Group c)) (= g (set-get s i)))
      ((Equated c g c)) :ruleset slotted)
```

# Per-constructor machinery

A child column expands to a renaming column and a class column, so
`(constructor Add (Math Math) Math)` becomes:

```
(constructor Add (Renaming Math Renaming Math) Math)
```

and `(Add $0 $1)` is stored as
`(Add (map-of 0 0) (Var 0) (map-of 0 1) (Var 0))`. Each constructor then gets one
block of rules: class slots, the shape index and its deletion, migration, and one
child-update per child column.

**Class slots**, an upper bound the merge narrows:

```
(rule ((= e1 (Add m1 c1 m2 c2)))
      ((set (ClassSlots e1) (map-union (map-image m1) (map-image m2)))) :ruleset slotted)
```

**The shape index**, which is the heart of it. Two rows are one node up to renaming
exactly when they have the same *shape*: the row with its slots renumbered 0, 1, 2… by
first occurrence, scanning the edges in order and each edge by child slot. `(shape m1
m2)` returns the renumbered edges followed by the renaming from those numbers back to
the row's own names. Every row is entered into a function per constructor, keyed by the
shape and holding one class that has the node with the renaming from the shape's names
into that class's. A second class arriving at a key is that node under another
renaming, and the function's merge block states the equation between the two. This is
the reference's hashcons on shapes: one lookup per row.

```
(function _shape_Add (Renaming Math Renaming Math) (Math Renaming)
  :merge ((set (ShapeEqual old0 (compose old1 (inverse new1)) new0) ())
          (values old0 old1)))

(rule ((= c (Add m1 c1 m2 c2))
       (= g1 (Group c1)) (= g2 (Group c2))
       (= sh (strong-shape (vec-of m1 m2) (vec-of g1 g2))))
      ((set (_shape_Add (vec-get sh 0) c1 (vec-get sh 1) c2) (values c (vec-get sh 2)))
       (set (Group c) (node-symmetries (vec-of m1 m2) (vec-of g1 g2)))) :ruleset slotted)
```

`strong-shape` takes each child's group and spells the node the way every reading of
those children agrees on, so two nodes that agree only after permuting a child's slots
arrive at one key. A row costs one insertion, whatever the groups hold. `ShapeEqual` is
a function rather than a relation because a merge block may `set` a function, and one
rule per sort hands its rows to `Equated`.

The rule's second action is what a node says about its *own* class: a reading that
spells the node the same way up to a renaming of the node's own slots says the class
equals itself under that renaming. `node-symmetries` returns those renamings as a set,
unioned into the group, which is how a child's symmetry becomes its parent's. This is
the reference's `determine_self_symmetries`, and it shares the rule's join because it
reads the same groups.

**One row per shape per class.** The index says which rows are one node; it removes
none. A class can still hold two rows of one shape under two readings: the same node
built twice in different frames, or a node and its image under a symmetry of a child.
One row is enough. The merge block has already recorded the symmetry between the two
readings, and a pattern reaches the other reading through the class's self-loops (C5).
So every row writes its shape into `_shapeof_Add`, canonical edges and reading as
columns, and where two rows of one class have the same children and the same canonical
edges, the one whose reading is the greater is deleted. Both rows are matched as rows,
so the rule only ever compares nodes that exist.

```
(function _shapeof_Add (Renaming Math Renaming Math) (Renaming Renaming Renaming)
  :merge (values new0 new1 new2))

(rule ((= c (Add m1 c1 m2 c2))
       (= sh (shape m1 m2)))
      ((set (_shapeof_Add m1 c1 m2 c2) (values (vec-get sh 0) (vec-get sh 1) (vec-get sh 2)))) :ruleset slotted)

(rule ((= c (Add m1 c1 m2 c2))
       (= (values s1 s2 b1) (_shapeof_Add m1 c1 m2 c2))
       (= c (Add n1 c1 n2 c2))
       (= (values s1 s2 b2) (_shapeof_Add n1 c1 n2 c2))
       (!= b1 b2)
       (= b1 (ordering-max b1 b2)))
      ((delete (Add m1 c1 m2 c2))) :ruleset slotted)
```

**Migration** rebuilds a follower's node in the leader's slot names and unions it into
the leader. `R` takes the node's slots to the leader's, agreeing with the edge where
the leader has the slot and minting a name where the class has dropped it. After this
every node lives in a leader, and a follower is a name in `RenamesToLeader` and
nothing more.

```
(rule ((RenamesToLeader e2 m e1)
       (= e2 (Add m1 c1 m2 c2))
       (!= e1 e2)
       (= e2 (ordering-max e1 e2))
       (= nodeslots (map-union (map-image m1) (map-image m2)))
       (= R (find-mapping-total (map-domain m) nodeslots (map-domain m) m))
       (= n1 (compose R m1))
       (= n2 (compose R m2)))
      ((union e1 (Add n1 c1 n2 c2))
       (delete (Add m1 c1 m2 c2))) :ruleset slotted)
```

**Child-update** rebuilds a node whose child has a leader so that it points at the
leader, its edge composed with the child's renaming. Through a self-loop, `c1 = c'`,
only an idempotent one counts and only if the edge changes: that is a child that
dropped a slot, and the parent's edge drops it too, which is how redundancy travels
upward. One such rule per child column; the one for the second column is the same
with `m2` and `c2`.

```
(rule ((RenamesToLeader c1 m c')
       (= node (Add m1 c1 m2 c2))
       (= c1 (ordering-max c1 c'))
       (guard (or (bool-!= c1 c') (bool= (compose m m) m)))
       (guard (or (bool-!= c1 c') (bool-!= (compose m1 m) m1))))
      ((union node (Add (compose m1 m) c' m2 c2))
       (delete (Add m1 c1 m2 c2))) :ruleset slotted)
```

Because the index's deletion and migration delete rows, a class keeps one row per
shape — which is why a claim about a term matches it rather than spelling it out. A term the e-graph holds need not have a row under the spelling you wrote.

# Binders

`:binder i` marks a child column whose slot the node binds. The bound slot is
stored as an edge `0 -> s` to `(Var 0)` like any other, so a binder is not a
different kind of column — what differs is that the slot is taken out of the
class's slot set over the column the binder **covers**, which is the one right
after it. `let` binds in its body and leaves its value's occurrence free.

One rule per bound slot does the taking out: the node's edge to its leader is
restated without the bound slot, and the class-slot transport above then intersects
that slot away, so the class does not depend on what it binds.

```
(rule ((RenamesToLeader (Lam mvar (Var 0) m2 c2) ml l)
       (= v (map-get mvar 0)))
      ((Equated (Lam mvar (Var 0) m2 c2) (inverse (map-remove (inverse ml) v)) l)) :ruleset slotted)
```

In the constructor's own block the binder column needs no special case in the shape
index, since the variable class's group holds the identity alone, and its
child-update also requires `(map-get (compose m1 m) 0)` to exist: a bound name may be
renamed but not lost.

When a bound slot collides with a free one the machinery renames the bound one
first, to a slot the node does not use, which keeps it alpha-renameable.

# Matching

egglog finds the e-nodes a rule's left-hand side matches; what the match says about
**slots** is a set of constraints on those nodes, checked by a handful of primitives
inside the same query. This section walks one rule through, the SDQL library's
`sum-fact-3`:

```
(rewrite (Sum R $x $y (Sing e1 e2))
         (Sing e1 (Sum R $x $y e2))
         :name "sum-fact-3"
         :when ((not-free $x e1) (not-free $y e1)))
```

`Sum` binds `$x` and `$y` over its body (its `:binder 1 2` columns), so the rule pulls a
singleton's key out of a sum when the key does not mention the bound variables.

## Flattening

egglog matches one e-node per atom, so the left-hand side becomes depth-1 atoms, one
per constructor, every child a pattern variable or a slot literal. The flattener names
the nodes it has to invent with a `_` prefix, which no author's name begins with:

```
_p  = (Sum R $x $y _t1)      the root
_t1 = (Sing e1 e2)           the Sing node under it
```

`R`, `e1` and `e2` are pattern variables. Each stands for an **invocation**: a class
and a renaming of that class's slots into the pattern's (C1). `$x` and `$y` are slot
literals, names the pattern gives to slots of its own. Each atom becomes one egglog
row pattern with a variable per column: `cls_p` and `cls_t1` for the two classes,
`e0_R` for atom 0's edge to `R`, `e1_e1` for atom 1's edge to `e1`, and so on. An
edge is a renaming from the child class's slots to the node's; a binder column's edge
sends `0` to the bound slot.

## Occurrences

The matched `Sum` node has slots numbered however the e-graph stores them, the matched
`Sing` node has its own numbering, and so does every class a variable is bound to. The
pattern needs to know which of all these are the *same* slot. So the frame speaks of
**occurrences**, one name for every place a slot shows up in the match:

| occurrence | reads as |
| --- | --- |
| `Node(a, s)` | slot `s` of the e-node matched at the atom labelled `a` |
| `Var(v, t)` | slot `t` of the class pattern variable `v` is bound to |
| `Lit("$x")` | the slot the pattern calls `$x`, or one the right-hand side minted |

`Node(_t1, 1)` means "whatever the matched `Sing` node calls slot 1", and
`Var(e1, 0)` means "whatever `e1`'s class calls slot 0": relative names, the two ends
of an edge egglog matched. Only `Lit` is a name of the pattern's own. A node and its
class are kept apart because a node may carry a slot its class has made redundant
(C4), and a child's class numbers its slots differently from the node that holds it,
with the edge as the translation.

Every column of a matched node is then an equation between occurrences:

- the root column: `Node(a, s) = Var(p, s)` for each slot `s` of `p`'s class, the node
  is an invocation of its own class (through a symmetry of the class when `p` was
  matched by an earlier atom, C5);
- a child carrying `v` by edge `e`: `Node(a, e(t)) = Var(v, t)` for each slot `t` of
  `v`'s class;
- a literal at edge `e`: `Node(a, e(0)) = Lit("$x")`.

Take a match of `sum-fact-3` against `(Sum r $x $y (Sing $z $x))`, where `r` is some
term with one free slot. Say the `Sum` node stores `r`'s slot as 0, `z` as 1, `x` as 2
and `y` as 3, so its class's slots are `{0, 1}`; the `Sing` node stores `z` as 0 and
`x` as 1, and the edge from the `Sum` node to it is `{0 -> 1, 1 -> 2}`; the bare slots
`$z` and `$x` are the variable class with its one slot 0, reached by the edges
`{0 -> 0}` and `{0 -> 1}`. The equations close into four blocks:

```
{ Node(_p,0)  Var(_p,0)  Var(R,0) }                                   R's one slot
{ Node(_p,1)  Var(_p,1)  Node(_t1,0)  Var(_t1,0)  Var(e1,0) }         z, free in the root
{ Node(_p,2)  Lit("$x")  Node(_t1,1)  Var(_t1,1)  Var(e2,0) }         the bound x, reached again as e2
{ Node(_p,3)  Lit("$y") }                                             the bound y, unused below
```

The second block is the interesting one: the `Sum` atom put `Node(_p,1)` with
`Var(_t1,0)`, and the `Sing` atom put `Var(_t1,0)` with `Node(_t1,0)` and `Var(e1,0)`.
`Var(_t1, 0)` is the same occurrence in both atoms, so joining them identifies the
parent's edge with the child's own slot. That is the reference matcher's `unify`,
and it needs no order: the join takes the union of the equations and re-closes.

## The frame

A **frame** is the closure of these equations. Its **blocks** are the pattern's
slots: two occurrences in one block are one slot, and the blocks are numbered
canonically, `anchor` making the root's class slots their own numbers. Above, anchored
at `_p`, the blocks are slots 0, 1, 2, 3 in the order written, so `(ren m "e1")` is
`{0 -> 1}`, `(ren m "e2")` and `(ren m "$x")` are `{0 -> 2}`, and `(not-free m "$x"
(names "e1"))` asks whether slot 2 lies in `e1`'s image `{1}`: it does not, and the
rule fires. Had `e1` been `(var $x)`, `Lit("$x")` and `Var(e1, 0)` would share a
block and the condition would refuse.

The equations say which occurrences are one slot; the **cliques** say which are
different. A clique is a set of occurrences every two of which must be distinct slots,
so no two may share a block:

- the slots of one e-node, `Node(a, ·)`: a node's slots are distinct positions;
- the slots of one class, `Var(v, ·)`: a renaming is injective;
- the different literals: the pattern asked for two names.

A frame is **consistent** when no clique is broken; `atom` and `frame-join` return
nothing otherwise, so a reading that identifies two slots of one node simply fails to
join. The cliques are not stored: `sort/frame.rs` in the egglog crate reads them off
the occurrences (`apart`). The reference matcher keeps the same information as pairwise
disequality constraints. In the match above every block holds a slot of the root
node, so the node clique pins all four and `refinements` holds the frame alone; C8
says when it has more to do.

The primitives:

| primitive | what it says |
| --- | --- |
| `(root "p" cs [sym])` | the atom's node is an invocation of `p`'s class, whose exact slots are `cs`; through the symmetry `sym` if `p` was matched before |
| `(child "v" e cs [sym])` | the column with edge `e` carries `v`: `Node(a, e(t)) = Var(v, t)` for each class slot `t` |
| `(lit "$x" e)`, `(bound "$x" e)` | the column is the literal `$x`: `Node(a, e(0)) = Lit("$x")`; `bound` is a binder column, whose literal is node data and not carried into refinement |
| `(leaf e)` | a payload leaf reached through its own class: node slots, nothing more |
| `(atom "a" binding...)` | one atom's constraints, closed; fails if its own columns break a clique |
| `(frame-join f g)` | both frames' constraints, closed; fails where a clique breaks. Associative and commutative |
| `(anchor f "p")` | the frame spelled in `p`'s slot names: the rule's root, so its renaming is the identity and the action is egglog's `union` |
| `(refinements f)` | every consistent merging of the blocks refinement may touch, as a `Vec` of frames with `f` itself first; `vec-get` reads one and is partial past the last |
| `(mint f (names "$z"...))` | fresh slots for a right-hand side, apart from everything named |
| `(free m "$x" (names v...))`, `(not-free ...)` | is the literal's slot in one of the variables' images |
| `(same m "a" "b")`, `(bool-same ...)` | the two variables are one invocation |
| `(ren m "v")` | `v`'s renaming into the pattern's slots; a literal comes back as `{0 -> slot}` |
| `(node-slots m uncovered covered bound)` | a built node's free slots from its named columns; `(without m slots bound)` for a built child under a binder |

## The compiled rules

What `slotted-encoder.py` emits for `sum-fact-3`, with the `_0` that says which
sort's tables these are dropped from the table names, and with the right-hand side
written in the frame's own slots; the spelling it is actually emitted in is one
optimization away, below. Names in quotes are the rule's own variables and literals,
so a frame is keyed by the words the rule was written in.

One rewrite becomes a relation and three rules. egglog joins a body's table atoms
first and runs its primitives afterwards, once per matched row; had the index relation
`Idx` been in the same body as the frame primitives, every frame would have been built
once per index. So the first rule finds a match and stores its refinements; the second,
in the `slotted-apply` ruleset, joins the stored row with `Idx`, reads one refinement,
checks the conditions and acts; and the third deletes the row once that phase has read
it (C13).

```
(relation _matched_sum-fact-3 (Frames U U U U U))

(rule (;; egglog's own match of the two atoms, one row pattern each: an ordinary
       ;; column is an edge and a class, a binder column an edge and the variable
       ;; class (Var 0)
       (= cls_p (Sum e0_R cls_R e0_lit_x (Var 0) e0_lit_y (Var 0) e0_t1 cls_t1))
       (= cls_t1 (Sing e1_e1 cls_e1 e1_e2 cls_e2))
       ;; _t1 is bound by the first atom and read again by the second, so the second
       ;; reading may differ by a symmetry of its class; one row per group element (C5)
       (RenamesToLeader cls_t1 sym_t1 cls_t1)
       ;; what each atom's columns say about slots: each binding names the column's
       ;; variable or literal, its edge, and the exact slots of its class (C2, C4, C7)
       (= atom_p (atom "_p" (root "_p" (ClassSlots cls_p))
                            (child "R" e0_R (ClassSlots cls_R))
                            (bound "$x" e0_lit_x) (bound "$y" e0_lit_y)
                            (child "_t1" e0_t1 (ClassSlots cls_t1))))
       (= atom_t1 (atom "_t1" (root "_t1" (ClassSlots cls_t1) sym_t1)
                              (child "e1" e1_e1 (ClassSlots cls_e1))
                              (child "e2" e1_e2 (ClassSlots cls_e2))))
       ;; the two joined: where they share _t1 the occurrences are identified (C6);
       ;; nothing here if a clique breaks
       (= f (frame-join atom_p atom_t1))
       ;; spelled in the root's class slots, then every consistent merging of what the
       ;; pattern left open, the frame itself first (C8)
       (= refined (refinements (anchor f "_p"))))
      ;; the match, stored: its refinements and every class the action will read (C13)
      ((_matched_sum-fact-3 refined cls_p cls_R cls_t1 cls_e1 cls_e2)) :name "sum-fact-3")

(rule ((_matched_sum-fact-3 refined cls_p cls_R cls_t1 cls_e1 cls_e2)
       ;; one refinement per index; `vec-get` is partial past the last (C8)
       (Idx choice)
       (= m (vec-get refined choice))
       ;; the side conditions, read off the refined frame (C9)
       (not-free m "$x" (names "e1"))
       (not-free m "$y" (names "e1")))
      (;; the right-hand side bottom-up, each column's renaming read out of m
       (let built_sum (Sum (ren m "R") cls_R (ren m "$x") (Var 0) (ren m "$y") (Var 0) (ren m "e2") cls_e2))
       ;; the built node's free slots: R's image, and e2's with the bound $x, $y taken out
       (let built_sum_slots (node-slots m (names "R") (names "$x" "$y" "e2") (names "$x" "$y")))
       ;; a built child sits at the identity, its slot set as the edge
       (let built_sing (Sing (ren m "e1") cls_e1 built_sum_slots built_sum))
       ;; the root's own slot set, which the union below does not need
       (let built_sing_slots (map-union (node-slots m (names "e1") (names) (names)) built_sum_slots))
       ;; anchored at _p the root's renaming is the identity, so the equation the rule
       ;; means is egglog's own union (C11)
       (union built_sing cls_p))
      :ruleset slotted-apply :name "sum-fact-3/apply")

;; the stored match is spent, whether or not a refinement passed the conditions
(rule ((_matched_sum-fact-3 refined cls_p cls_R cls_t1 cls_e1 cls_e2))
      ((delete (_matched_sum-fact-3 refined cls_p cls_R cls_t1 cls_e1 cls_e2)))
      :ruleset slotted-apply :name "sum-fact-3/drain")
```

**Building canonically.** The action above says what the rule means, and every node in
it is spelled in the frame's own slots. A node below the root is emitted differently:
its edges go through `shape` first, so it is written in the canonical numbering and not
in this rule's (C16).

```
(let shape_sum (shape (ren m "R") (ren m "$x") (ren m "$y") (ren m "e2")))
(let built_sum (Sum (vec-get shape_sum 0) cls_R (vec-get shape_sum 1) (Var 0)
                    (vec-get shape_sum 2) (Var 0) (vec-get shape_sum 3) cls_e2))
(let built_sum_slots (node-slots m (names "R") (names "$x" "$y" "e2") (names "$x" "$y")))
;; the frame's names for those slots, read off the canonical ones; `compose` drops a
;; canonical slot the node binds
(let built_sum_edge (compose built_sum_slots (vec-get shape_sum 4)))
(let built_sing (Sing (ren m "e1") cls_e1 built_sum_edge built_sum))
```

Two rules that build one node in two frames then write one row and reach one egglog
value. Spelled in each rule's own slots they are two values denoting one class, and
the machinery has to find them equal, migrate the rows of one into the other, point
every parent at the survivor and close the edges that all of that adds. That cascade
runs per built node. The root keeps the frame's spelling, since the action unions it
with the root's class and an invocation there must be at the identity (C11), and
`union` disposes of it at once.

**When the rules run.** A user step is `(seq (run) (run slotted-apply) (saturate (run
slotted)))`: the matching rules, then the acting and draining rules, then the machinery
to a fixed point. egglog finds every match of a ruleset before it applies any action,
so the drain never hides a row from the acting rule, and a row is gone after one phase
whether or not a refinement passed the conditions; a match that recurs after the
machinery has changed its nodes is found afresh. On the SDQL matrix-multiplication
benchmark this took the run from 1.16 s to 0.18 s with one thread, the user rules'
apply time, where `--timing-summary` books the primitives, falling from 820 ms to
about 20 ms.

## The contract

What a compiled rule asserts, clause by clause; `compile_query` and
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
tree the compiler writes means nothing. A slot no equation reaches is a placeholder, a
block of its own.

**C3. Atoms are written in a connected order.** `connected_order` puts each atom
after one it shares a variable with, parent before child. Under frames this is only a
convention for readable output; the answer does not depend on it, and `xarray.py`
checks that.

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
different literals are two blocks, by the literal clique. In a binder column a
literal is the bound slot (`bound`), and only a literal may stand there.

**C8. Placeholders are refined last.** `refinements` enumerates every consistent way
to merge the blocks a variable or a carried literal reaches -- never two literals, never
two slots of one node or class -- as a `Vec` with the frame itself first, and the rule
reads one per `(Idx choice)` with `vec-get`, which is partial past the last. Running
out of indices loses matches and never invents one. This is the reference's
`final_refine`.

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

**C13. A match is stored before it is acted on.** egglog runs a body's primitives
after its table join, once per row, so a rule that joined `Idx` beside its frame
primitives would build the frame once per index. Instead the matching rule stores each
match, its refinements and the classes the action reads, in a relation of its own, and
a rule in the `slotted-apply` ruleset joins that row with `Idx`, reads one refinement,
checks the conditions and acts, and a third rule in that ruleset deletes the row. The
schedule runs the two rulesets in turn within one step, so a step still means one round
of every rule.

**C14. Nodes are indexed by shape.** Every row of a constructor is entered, under
every symmetric reading of its children, into a function keyed by its shape -- the row
with its slots renumbered by first occurrence -- and holding one class with that node
and the renaming into it. Two rows meeting on a key are one node up to renaming, and the
function's merge block states the equation between their classes; a class meeting
itself there gains a symmetry. Of two rows of one class with one shape, the greater
reading is deleted. This is the reference's shape hashcons: `weak_shape` over
`get_group_compatible_variants`.

**C16. A built node below the root is spelled canonically.** Its edges go through
`shape` and its edge into its parent is the renaming back to the frame, narrowed to the
slots the node leaves free. This is the one place the encoding writes something other
than what the rule says, and it changes no answer: the node is the same node, spelled
in the numbering every frame agrees on, so two rules that build it write one row and
reach one value. The root keeps the frame's spelling (C11).

**C15. A renaming is spelled on its classes' slots.** Every `RenamesToLeader` row's
renaming has its domain within the leader's class slots and its image within the
follower's. Orientation restricts it as it enters, a later narrowing restates it, and
the rules that delete edges act only on restricted ones. An entry on a slot a class has
dropped says nothing about the class, but it makes two spellings of one edge two rows,
and every rule that composes edges then multiplies the spellings.

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
