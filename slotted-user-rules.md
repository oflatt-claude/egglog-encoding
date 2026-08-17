# Compiling user rules into the slotted encoding

Companion to three runnable files:

| file | what it is |
| --- | --- |
| `tests/slotted-egraph-encoding-11.egg` | the machinery: union, congruence, redundancy, symmetry |
| `tests/slotted-user-rules.egg` | hand-encoded user rules, M1–M8 |
| `slotted-experiments/xdiff/xdiff.py` | differential tests against the reference implementation |

Semantics come from Schneider et al., *Slotted E-Graphs*, PLDI 2025
([PDF](https://steuwer.info/files/publications/2025/PLDI-Slotted-E-Graphs.pdf),
[code](https://github.com/memoryleak47/slotted-egraphs)) — mainly Definition 6
(when two invocations are equal), Definition 8 (which e-nodes an invocation
stands for), §3.5 (union) and §3.6 (matching).

## Vocabulary

Only three terms are needed.

A **slot** is a variable name. An e-class is parameterised by the slots of the
terms it holds, so referring to one means saying what goes into each slot — an
**invocation**, written `m*c` for a class `c` and a renaming `m`. (The paper calls
this a *renamed id*; the Rust crate calls it an `AppliedId`.) A **renaming** is a
one-to-one map between slots.

Slot names are local. `(Var 0)`'s `$0` and some `f` node's `$0` are unrelated
names that happen to look alike, so relating one class's slots to another's always
means writing down a renaming.

Notation used below:

| | |
| --- | --- |
| `(compose a b)` | `b` first: `(compose a b)[x] = a[b[x]]` |
| `(App f m1 c1 m2 c2)` | the node `f(m1*c1, m2*c2)`; each `mi` maps its child's slots into the node's |
| `(RenamesToLeader a m b)` | `a = m*b` |
| `(RenamesToLeader c m c)` | `m` is a symmetry of `c` |
| `(find-mapping a… b…)` | the least `m` with `m ∘ bi = ai`; fails if no one-to-one `m` exists |

Note `compose` runs in the opposite order from `SlotMap::compose` in the crate.

Two facts about the machinery that matter later. A slotted e-class is **not** one
egglog e-class: nodes equal up to renaming are linked by `RenamesToLeader` and one
is deleted, so a slotted class is a set of `U` values sharing a leader. And every
`(Var v)` collapses to `[0↦v] * (Var 0)`, so the leaves are one class, not many.

## The model

**A rule variable is an invocation, not a class.** So a user variable `x`
compiles to two egglog variables: the class `X`, and a renaming `mx` carrying
`X`'s slots into the pattern's.

The pattern's slots are not invented. One atom is chosen as the **first atom**,
its matched node's slots *are* the pattern's, and its own renaming is therefore
the identity and never written down.

## Compiling a rule body

**Step 1 — flatten.** Rewrite the left-hand side as depth-1 atoms

```text
?v == (Op ?c1 ?c2)
```

one per e-node, every child a bare variable. This is `MultiPattern` in the crate,
and it is already the shape of an egglog rule body, which is what makes the rest
mechanical. `(f (g ?x) ?y)` becomes `?t == (f ?u ?y), ?u == (g ?x)`.

Flattening is not always meaning-preserving: a nested pattern is matched under one
renaming for the whole pattern, a flattened one gets a renaming per atom. A slot
written both under a binder and outside it therefore means different things in the
two forms, and the binder escapes. A flattener must reject or rename those.

**Step 2 — order the atoms so each one shares a variable with the ones before
it.** This is a correctness condition, not a heuristic. An atom sharing nothing
has no constraint on its renaming, so every slot it needs is *invented* — and an
invented slot cannot be revised later. If a following atom then shows that slot is
really one the pattern already named, the two disagree and the match is lost.
`order_atoms` in `xdiff.py` does the reordering; `C12` is the case that motivated
it. A body no ordering can connect has to invent slots, and there the gap is real.

**Step 3 — give each atom a renaming.** One rule:

> An atom's renaming is the least renaming, total on its node's slots, agreeing
> with **everything already known about that atom**: its root if an earlier atom
> bound it, every child an earlier atom bound, and every slot literal an earlier
> atom pinned. Collect them into a single `find-mapping-total`, whose avoid-set is
> every slot named so far.

It is tempting to read this as three separate cases — first atom, root known,
children known — and that reading caused three of the four bugs listed at the end.
`tests/slotted-user-rules.egg` had drifted back to it and has been brought into
line; `M3b` there is an e-graph where the two readings visibly disagree, the short
one computing an *empty* renaming for a child that has a slot.
The cases are only *which* constraints happen to exist:

* nothing known — the atom is first; its renaming is the identity and it defines
  the pattern's slots;
* root known — join `(RenamesToLeader V symV V)` and constrain by
  `(compose mv symV)`;
* children known — constrain by `(compose mx sym)` against the stored edge, with a
  `(RenamesToLeader X sym X)` join per child.

An atom that knows several of these must use all of them.

**Step 4 — walk the children.** A child at stored edge `p` has candidate renaming
`(compose mp p)`. If its variable is new, that *is* its renaming. If it is already
bound, check the two agree.

## Checking that two occurrences agree

This is the whole of what a repeated variable costs. Definition 6: two invocations
of the same class are equal exactly when one renaming differs from the other by a
symmetry of that class. Both renamings are known by the time this runs, so the
symmetry it would need is *determined* — compute it and look it up:

```text
(= sym (compose (inverse mx) (compose mp p)))
(RenamesToLeader X sym X)
```

With all three arguments bound that is an index lookup, not a join. The
enumerate-and-compare spelling means the same thing but makes the planner produce
one row per symmetry and discard all but one:

```text
(RenamesToLeader X sym X)
(= (compose mp p) (compose mx sym))
```

`M2` runs both and checks they agree, including on a case needing a real swap.

Add one guard to either spelling:

```text
(= (map-length sym) (map-length mx))
```

Composition truncates silently, and a redundant slot is stored as a *partial*
self-loop, so a short symmetry could match one of those and be accepted wrongly.
The guard rules that out without relying on the e-graph being saturated — which
matters, because user rules share a ruleset with the machinery and can therefore
match mid-repair. It costs nothing on the test corpus.

**Neither may be weakened to `(= (compose mp p) mx)`.** Equality of renamings is
strictly weaker than equality of invocations, and the difference shows: `M2(c)`
matches `f(?x, ?x)` against `f(a[$0,$1], a[$1,$0])` where `a` is symmetric. The two
occurrences *are* the same invocation, the symmetry-aware rule fires, and the naive
one does not. The machinery will not normalise the two edges to be equal either, so
this is not a case you can pre-process away.

## Symmetry joins: where they are needed

Matching in the paper considers every node an invocation stands for, including all
symmetry-permuted variants. The encoding stores one variant per orbit, so those
have to be regenerated. The claim is that regenerating them where occurrences are
checked suffices:

> Every occurrence of a variable after the first costs one symmetry lookup. The
> first occurrence costs nothing.

The first occurrence is free because binding `mx` pre-composed with a symmetry
just reparameterises every later constraint by it. The first atom needs no join,
because permuting its root relabels the pattern's slots, and the action is built
in pattern slots, so the result is an α-variant the machinery identifies anyway.
Variables used once need no join for the same reason.

### One symmetry per class, handed to the primitives

The intended shape, and the better one: join **one** `(RenamesToLeader C sym C)`
per e-class and use that `sym` everywhere that class's renaming is used, rather
than joining a fresh one at each site. The primitives then receive
`(compose mx sym)` and work out whether it fits — solving the constraint is what
decides, instead of the query enumerating candidates site by site.

Two consequences worth stating:

* **Fewer joins.** One per class, not one per use, and each is a small relation.
* **It makes a correctness fix affordable.** A variable bound as an atom's root
  gets `mp`, whose domain is the matched *node's* slots — but a variable's
  renaming must have its *class's* slots for a domain, and the two differ exactly
  when the node carries a redundant slot. Restricting it needs the live slot set,
  which is precisely what a symmetry's domain is: `(compose mp sym)`. With a
  per-class join that costs nothing extra.

Measured against the per-use scheme it is indistinguishable — same answers, same
firing count, same single known failure. `XDIFF_SYM` selects between them.

The scheme does **not** address the branching question above, and did not fix
`X1`: both are about redundancy, not symmetry.

**The stored set has to be closed, not just a set of generators**, or a lookup for
a composite element would fail and lose matches. It is: the machinery's
transitivity rule composes self-loops, because its guard has an `e1 = e3` escape.
`S1` pins this down — a class is given one 3-cycle, and the parent then holds it
at the identity beside it at the cycle's *square*, which is never unioned in. The
rule fires, so the lookup found the composite. `S1b` is the control: without the
3-cycle there is no match, so `S1` is not passing for some other reason.

The set is not quite a group, though: a redundant slot is recorded as a *partial*
self-loop, so it is an inverse monoid. That matters for the occurrence check —
if the computed symmetry came out short, because a composition truncated, it could
match one of those partial loops and be accepted wrongly. Hence the width guard
above. On a saturated e-graph the shrinking rule keeps self-loops at the live
slots and the question does not arise, but user rules share a ruleset with the
machinery and so can match mid-repair, which is exactly when it would. `S2` covers
a symmetry and a redundancy in play together.

## Actions

Each variable at a child position uses its renaming. New nodes are built in
pattern slots.

**`union` is only correct at the identity.** The paper's union takes invocations,
and whether it produces a redundancy, a new symmetry, or a class merge depends on
their renamings. egglog's `union` takes classes, i.e. only the case where both
renamings are the identity. So:

* the action's root is the first atom's root → plain `(union A B)` is fine;
* anywhere else → build the node and insert the fact instead:

  ```text
  (let _hn (App "h" ma A mb B))
  (RenamesToLeader _hn mp_root Root)
  ```

  The machinery re-orients it, and promotes it to a real union if the renaming
  turns out to be an identity.

**Getting this wrong is silent**, which is why it is stated twice. A plain
`(union root built)` asserts an equation whose renamings are both the identity.
When the root's renaming is not, the equation is simply false — it merges two
distinct pattern slots — and the e-graph absorbs it as a redundancy rather than
complaining. `C11` is the case: a root renaming of `{$0↦$3, $2↦$2}` drove
`(Var 0)` from one live slot to none, after which every edge was emptied and
`h(x,y)` collapsed with `h(x,x)`. Two things make it hard to spot: the built node
is *correct*, so inspecting it tells you nothing; and an edge-width check misses it
because the children's classes go slotless too and the widths agree again.

Restricting the built node to the root's slot space instead — composing each child
renaming through `inverse mp_root` — is also sound, but needs a totality guard and
then declines to fire on cases the fact-insert handles.

The same gap appears for plain input terms. A `U` value is a node, not an
invocation, so a bare leaf has nowhere to carry its slot: `(var $0)` and
`(var $2)` both encode as `(Var 0)`, and `union (var $0) (var $2)` — which makes
the variable class slotless in the reference, collapsing every `h(var, var)` —
becomes a no-op. Slots inside a compound term ride in the stored edges and
survive; only a top-level leaf loses them.

## Slots the constraints never reach

`find-mapping` returns the *least* renaming, so a node slot outside the
constraints gets no name, and dropping a slot leaves an edge narrower than its
child's slot set, which Definition 4 forbids. The paper's §3.6 handles this by
picking any fresh slot; the crate does it in `enodes_applied`, so it never has an
unnamed slot to drop.

`find-mapping-total` ports that: same constraints and same one-to-one check as
`find-mapping`, plus a fresh name for every domain slot left unnamed.

```text
(find-mapping-total avoid domain first… second…)
```

`domain`'s keys are the slots the result must cover, `avoid`'s slots are the ones
it may not reuse. Both are identity maps the caller already has: a node's slots are
`(map-union (map-image p1) (map-image p2))`.

**It picks the smallest unused slot, and that is not a detail.** Picking one above
the maximum instead makes the name depend on how large the existing names happen
to be — so a rule whose action builds a node of the same operator its premise
matches mints a *higher* slot every round, building an endless run of
α-equivalent-but-distinct nodes and never reaching a fixpoint. That was the
encoding's only observed performance problem, and it was really
non-termination: on one generated case the node count climbed 16, 18, 30, 28, 38,
47, 50, 59 with no sign of settling, while the reference saturated in two rounds.
The built nodes' edges were visibly escalating, `{$0↦$0}, {$0↦$1}, … {$0↦$6}`.
Smallest-unused gives the same situation the same name, so those nodes coincide;
the same case then settles.

So: any deterministic choice is *sound*, because different choices give
α-variants the machinery identifies — but only a choice that does not drift
terminates.

**The avoid-set must accumulate.** The primitive is pure and sees one atom at a
time, so passing only the first atom's slots lets two inventing atoms pick the
same slot. Thread a running union of `(map-image mp)`; identity maps never conflict
under `map-union`, so the union is always defined.

The alternative, if you would rather not invent slots: guard every variable the
action uses with `(= (map-length (compose mp p)) (map-length p))`. Sound but
incomplete — `M6(b)` shows the rule declining to fire in the bad case and still
firing in the good one. Occurrence checks are self-guarding already, since a
dropped slot changes the domain and breaks the equation.

## What the differential tests cover

`xdiff.py` builds a case, runs it through the reference (`xmulti`, which drives the
crate directly) and through a compiled egglog rule, and compares which probe terms
end up equal. Per case it checks three things:

1. **baseline** — with no rule at all both sides must already agree, so a
   difference is attributed to matching rather than to the machinery;
2. **agreement** — the compiled rule against the reference;
3. **fixpoint** — both sides must have settled. A case that hasn't means the two
   ran different amounts of work, so comparing them says nothing: the reference
   reports whether it saturated, and the encoding is rerun at twice the iterations
   and must agree. That doubles as a determinism check;
4. **order independence** — the answer must not change when the atoms are compiled
   in a *different* order, which moves which atom is first and hence every slot;
5. **slot-renaming invariance** — renaming every slot in the program must not
   change either side's answer. This is a per-side property needing no
   cross-system comparison, and it asks a different question from agreeing with
   the reference: a side can be consistently wrong and still invariant.

```text
./xdiff.py              the curated cases
./xdiff.py fuzz 250 7   250 random cases, seed 7
./xdiff.py show C11     dump one case: spec, both answers, compiled rule
./xdiff.py show 61 555  the same, for a random case
```

Touching the generator renumbers every random case, since they share one RNG
stream — so a failing index does not reproduce across a generator change. Copy an
interesting case into `curated()` before changing anything, which is where `C11`
and `C12` came from.

Current state — `./xdiff.py` and `./xdiff.py fuzz 250 777`:

| | curated | random |
| --- | --- | --- |
| cases agreeing | 29/30 | 248/250 |
| of which the rule fired | 23 | 57 |
| matching differences | 0 | 0 |
| order dependence | 0 | 0 |
| slot-renaming | 0 | 0 |
| machinery differences | 0 | 0 |
| excluded: timeout or unsettled | 0 | 1 |

## A soundness bug in the machinery: migration truncates edges

Found by the differential suite as `X1`/`X2`, and fixed. It is worth reading
because it is the *same* dropped-slot mistake as the fresh-slot section above,
one level down.

The migration rule rewrites a node into its leader's slot space:

```text
e2 = m*e1  and  e2 = f(m1*c1, m2*c2)   =>   e1 = f((m⁻¹∘m1)*c1, (m⁻¹∘m2)*c2)
```

`compose` keeps only the keys whose value lies in the left map's domain. So when
`m1` reaches outside `im(m)` — exactly when `e2` has a slot that is redundant in
`e1` — the rewritten edge **silently narrows**. In the minimal case `m = {$0↦$0}`
and `m1 = {$0↦$1}` compose to the *empty* map, and an empty edge to `(Var 0)`
asserts the variable class has no slots. Every `h(var, var)` then collapses.

The minimal reproducer is one term and one rule, no unions:

```text
term   h(v0, v1)
rule   ?c == (h ?a ?b)  =>  union ?a (h ?b ?c)
```

Two things made it hard to see. It is **child-position sensitive** — swapping the
action's two arguments makes it disappear, because the truncation only hits the
edge that reaches the dropped slot — and every visible symptom is downstream:
malformed self-loops appear (derived by transitivity closing a cycle), the
variable class loses its slot, and `h(x,y)` merges with `h(x,x)`. Deleting the
self-loops does not help, and neither does guarding transitivity.

Fixed by declining to migrate when either edge would narrow — the guard now in
`tests/slotted-egraph-encoding-11.egg`.

### What declining costs, measured

The complete alternative is to mint a name for the uncovered slot instead of
dropping it: extend the pullback to be total on the node's slots, which is
`(find-mapping-total idE1 domNode idE1 m)` where `idE1` is the identity on
`slots(e1)` and `domNode` the identity on the node's. That version is in
`tests/slotted-egraph-encoding-11-minting.egg`.

Comparing the two, the guard's "incompleteness" turns out **not** to be about
derived equalities:

| | |
| --- | --- |
| machinery's own 13 tests | both pass |
| curated (31 cases) | identical answers |
| generated (200 cases) | identical answers |
| App rows on `X2` | guarded 8, **minting 1224** |

So no case distinguishes them on *what they prove*, and minting costs about 150× the
rows on `X2`. Its `App` count is stable after the first iteration, which is not the
same as settling: under `(saturate (run))` minting does not reach a fixpoint on `X2`
in 600s, where the guard settles at 7 rows. Restricting migration to fire only into a
canonical leader does not reduce the fan-out.

That fits what migration is for. The encoding's own header calls it compression —
"we delete nodes which are not canonical" — so declining leaves a node
un-canonicalised. Whether it also loses a *fact* is settled in the next section: it
does, though never yet in a way that changes an answer.

**Recommendation: keep the guard.** It is sound, cheap, and no test distinguishes
it from the complete version on what gets proved. Its one real cost — leaving a node
on a class no query could see — turned out to be fixable in the *maintenance* rules
instead, for about 9% more union-find rows; see two sections down. Minting is kept
alongside, measured, for whoever wants to revisit it — the open question is why it
fans out so far, not whether it is correct.

### The guard really is incomplete: the invariant is false

The question was whether this holds:

> every fact carried by a node on a self-loop-less class is also carried by a node
> on a self-looped one

If it did, the guard would be complete and "incomplete" would be the wrong word,
since a compiled rule only ever misses a node whose content it can reach anyway.

**It is false.** `X2`, under the guard, reaches a fixpoint holding two nodes that
no compiled rule can see and that are α-variants of nothing visible:

```
h( {1→1,2→2}·h( {1→1,2→2}·B, {0→2}·Var0 ),  {1→1,2→2}·B )
h( {1→1,2→2}·B,  {1→1,2→2}·h( {0→1}·Var0, {1→1,2→2}·B ) )
        where  B = h( {0→2}·Var0, {0→1}·Var0 )
```

`slotted-experiments/xdiff/stranded.py` reproduces this. It works in two steps:

1. Declare two observer relations *after* the machinery reaches a fixpoint, one
   joining `RenamesToLeader V s V` and one not, both keyed on the whole `App` row.
   The difference is exactly the set of rows a symmetry-joining rule cannot see.
   Counting relation rows during the run instead would answer a question about
   history, since rows outlive the `delete` in the migration rule; and reading
   `print-function` output instead would merge classes, since a class with no
   extractable term prints as `Unextractable`.
2. For each invisible row, search the visible ones for an α-variant — same operator,
   same children, edges equal under one injective renaming — with each edge first
   restricted to the slots its child actually has, because the machinery does not
   force an edge's domain to match its child and an unrestricted comparison reports
   false uniques.

| | stranded | of those, no visible α-variant |
| --- | --- | --- |
| `X1` guarded | 1 | 0 |
| `X2` guarded | 2 | **2** |
| `X2` minting | 0 | 0 |

Minting strands nothing, which attributes the stranding to the guard rather than to
anything else in the machinery.

**Why the earlier structural argument fails.** It went: every `App` row gets a
self-loop from the "everything must have a self-loop" rule, so a row only loses one
when single-parent deletes it, by which point its content is already related to the
leader. The gap is the last step. Single-parent deletes the self-loop, and nothing
re-derives it — that rule fires on a *new* `App` row, and the row is not new any
more. If migration was also declined, the leader never received the node. So the
relation `e2 = m·e1` is recorded while the node itself sits only on `e2`, reachable
in principle and unreachable by any rule that joins a self-loop.

**Not every decline strands something.** Declining means `compose (inverse m) m1`
lost a key, i.e. the child edge maps into slots outside the leader's frame. Two
kinds:

* **(a) the lost key is junk** — the child does not have that slot, so the entry
  meant nothing and dropping it would have been safe. This is `X1`'s only decline:
  `m1 = {0→0, 2→2}` into `Null`, which has no slots at all. Harmless, and the reason
  `X1`'s one stranded row *does* have a visible α-variant.
* **(b) the lost key is live** — the child genuinely uses it, so the class really has
  a slot its leader cannot name. This is `X2`, and it is the harmful kind.

The whole curated suite declines only 4 times: 1 on `X1` (kind a) and 3 on `X2`
(kind b). Aiming at kind (b) directly does *not* work: five cases built by unioning
a wider term with a narrower one, so the leader's frame is too small, all strand
nothing, because the redundancy path records a partial-identity self-loop that
widens the frame before migration is ever asked. `X2`'s kind-(b) declines arise
instead from the machinery's own churn on nested nodes, which is why they were hard
to construct on purpose.

**What this establishes.** There are reachable, stable states whose content no
compiled rule can reach. No case changes an *answer* — `X2` itself agrees with the
reference — so the defect is in what rules can see, not yet in what gets proved. But
"invisible to every query" is not a state the encoding should be allowed to reach,
so it is worth fixing on its own.

### The fix: don't delete a self-loop that a class still needs

The two-rule interaction reduces to four lines of machinery, with no user rule
involved — `Case 14` in `tests/slotted-egraph-encoding-11.egg`:

```lisp
(let $B (App "h" (map-of 0 2) (Var 0) (map-of 0 1) (Var 0)))     ; h($2,$1), slots {1,2}
(let $N (App "h" (map-of 0 1) (Var 0) (map-of 1 1 2 2) $B))      ; h($1,B), slots {1,2}
(union $N (Var 2))          ; N's class is just $2, so slot 1 is redundant for it
(run 20)
```

At the fixpoint `$N` holds an `App` row and its only `RenamesToLeader` row is
`$N → {0→2} → (Var 0)`. No self-loop, so no query can see the node.

The instinct is to blame the guard on migration, but the cheaper culprit is
**single-parent**, whose `b = a` branch deletes a class's self-loop the moment the
class acquires a leader:

```lisp
(rule ((RenamesToLeader a m1 b) (RenamesToLeader a m2 c) (!= a c) ...)
      ((delete (RenamesToLeader a m1 b))
       (RenamesToLeader b (compose (inverse m1) m2) c)))
```

With `b = a` that deletes `RenamesToLeader a m1 a`. The edge it adds in exchange is
**already derivable**: transitivity turns the same two rows into
`a = (compose m1 m2)·c`, and a symmetry group is closed under inverse, so
`compose (inverse m1) m2` and `compose m1 m2` generate the same set. So that branch
contributes nothing but the deletion. One guard removes it:

```lisp
       (!= a b)
```

| | before | after |
| --- | --- | --- |
| `X1` stranded / of those unique | 1 / 0 | 1 / 0 |
| `X2` stranded / of those unique | 2 / **2** | **0 / 0** |
| machinery's own tests | 13 pass | **14** pass (`Case 14` is new) |
| curated differential | 31/31 | 31/31 |
| generated differential | 250/250 | 250/250 |
| curated `RenamesToLeader` rows | 183 | 199 (+9%) |
| curated `App` rows | 144 | 143 |

So the cost is about 9% more union-find rows and slightly *fewer* e-nodes — `X2`
compresses to 7 `App` rows instead of 8, because a class that keeps its self-loop
can still be migrated into later. Compare minting, the other candidate fix, at ~150×
the rows on `X2`.

`X1`'s one remaining stranded row is the harmless junk-edge kind and is stranded by
a *different* mechanism: the shrinking rule deleting a too-wide identity self-loop,
which is open question 2. It has a visible α-variant, so nothing is lost.

The same guard is mirrored into `slotted-egraph-encoding-11-minting.egg` so the two
files still differ only in the migration rule.

### Do follower classes need self-loops at all?

They should not, and mostly they do not. A follower is supposed to be *emptied*:
migration moves each of its nodes into the leader's frame and deletes the original,
so nothing is left to match on and a self-loop would be dead weight. Measured at a
genuine fixpoint, that is what happens — `C1`, `C2`, `C5`, `S2` and `B2` all end with
zero followers holding an e-node.

The exception is exactly where migration **declines**. Then the node stays on the
follower forever, and with no self-loop no compiled rule can see it. So the follower
self-loop is not a general requirement; it is the price of the guard. `X2` is the
case that shows it: 2 followers still hold a node at its fixpoint.

Which suggests the obvious alternative — mint instead of declining, so followers
really are emptied, and go back to deleting their self-loops. That works:

| | |
| --- | --- |
| minting + follower self-loop deleted | 33/33 agree, 24 firing |
| `X2` rows, guarded vs minting | 7 vs 1224 |
| `X2` under `(saturate (run))` | guarded settles at 7 rows; minting does not reach a fixpoint in 600s |

So both designs are correct, and the current one is kept for cost: minting's fan-out
does not converge on `X2` where the guard does. The row count alone understated
this — the fan-out was previously described as "created in the first iteration and
stable after", which is true of `App` rows and not of the database.

**Migrating the self-loop to the leader does not substitute for keeping it.** The old
single-parent rule already did that — `RenamesToLeader b (compose (inverse m1) m2) c`
carries the symmetry onto the parent edge, and transitivity derives the same set
independently, a symmetry group being closed under inverse. Nothing is lost from the
*information*. What is lost is being addressable: a rule reaches a class's symmetries
by joining `(RenamesToLeader v sym v)`, so a class holding a node and no self-loop
cannot be matched, and having its symmetry on the leader does not help because the
node is not on the leader. The guard moves the symmetry but not the node.

**Read the firing count before the agreement count.** A case whose rule never
fires says nothing about matching, and random patterns mostly do not fire, so the
harness always reports how many did. Getting that number up was most of the work
of making the sweep mean anything: it went 1/53 → 21/141 → 61/300 as the generator
learned to read patterns off terms that are actually in the e-graph.

Curated cases, and what each is for:

| | |
| --- | --- |
| `C1`–`C10` | repeated variables, chains, joins, symmetry, redundancy, three-atom bodies |
| `C11` | the action must not use `union` off the identity |
| `C12` | atoms must be compiled in a connected order |
| `C13` | the first atom must not be a binder |
| `C14` | the action's root may carry a non-identity renaming (replaces `C11`) |
| `P1`,`P2` | ported: a node's distinct slots may not be merged, with and without redundancy |
| `S1`,`S1b` | the stored symmetries are closed, so a lookup finds a composite element |
| `S2` | a symmetry and a redundancy in play at once |
| `B1`–`B4` | binders: chaining through one, α-equivalence, the same slot literal on two binders |
| `M1`,`M6` | shapes `tests/slotted-user-rules.egg` teaches that nothing else covered: a swapped action, and one shared variable across two operators |

`tests/slotted-user-rules.egg` is the readable form of this same recipe, so its
header maps each of its sections to the case above that covers the shape. Keep the
two in step — the hand-written file passing its own assertions only says it does
what it expects, and it had drifted to the three-case reading once already. One
shape there, `M7`, cannot be covered as the oracle stands: it puts a slot literal
in a non-binder child position, and the reference admits a slot there only via
`Bind` or as the whole of `Var(Slot)`, which is a unary atom the harness's
two-child format cannot express.

### Ported from the crate's own suite, and what is not

`P1` and `P2` are `regress::same_node_redundant_slots_stay_distinct` and
`live_slots_of_one_class_stay_distinct`. `B3` is
`known_bugs::lambda_bug_reaches_the_goal_under_multipat`.

Not ported, with the reason:

* **`?q == (var $s)` atoms** (`slot_literal_over_redundancy`, and the eta tests) —
  the encoding has no `var` *node* to match. `(Var 0)` is a leaf class and the slot
  lives in the parent's edge, so there is no atom to write.
* **`known_bugs::bug2` / `bug3`** — they need three rules interleaved to
  saturation, and the harness runs one rule per case.
* **`props.rs` slot-renaming invariance** — the generator does not shift every
  slot in a program yet. Worth adding.
* **`refine.rs`** — both sides are incomplete in the same way, so there is nothing
  to compare; the crate marks them `#[ignore]` for the same reason.
* **`flattening_is_not_faithful_for_a_sibling_slot_literal`** — it compares nested
  against flattened matching *inside* the crate, and the encoding has no nested
  matcher to compare against.

### Checking that the tests still test something

Each past bug can be put back with `XDIFF_BUGS=`, and the corpus is expected to
notice:

```text
XDIFF_BUGS=root-only  ./xdiff.py     an atom's renaming from its root alone
XDIFF_BUGS=slot-late  ./xdiff.py     a slot literal checked after the renaming
XDIFF_BUGS=unordered  ./xdiff.py     atoms compiled in the order written
XDIFF_BUGS=binder-1st ./xdiff.py     the first atom may be a binder
XDIFF_BUGS=union-id   ./xdiff.py     the action unions classes, not invocations
```

Where each is caught:

| bug | caught by | how |
| --- | --- | --- |
| `root-only` | C3, C5, C6, C9, C10 (+3 more) | disagrees with the reference |
| `unordered` | C12, C13 | disagrees with the reference |
| `slot-late` | B3 | disagrees with the reference |
| `union-id` | C14 | disagrees with the reference |
| `binder-1st` | C13 | order-independence check only |

Two things this was worth doing for.

**Coverage decays silently.** Changing minting to smallest-unused made `C11` — the
witness for the only unsoundness found — stop testing what it was written for,
because under the new policy its root renaming comes out as the identity, and at
the identity the right and wrong spellings agree. The same happened to `R2` in
`tests/slotted-multipat-diff.egg`. For a while nothing anywhere caught `union-id`.
`C14` replaces `C11`, with the action rooted at a *child* variable so its renaming
is a stored edge rather than the identity.

That also exposed a blind spot in the generator: it only ever rooted an action at
an atom root, and those usually carry the identity, so the class-versus-invocation
distinction went unexercised. Rooting the action at any bound variable finds
witnesses in the first handful of cases.

**A mutant has to be faithful, or it measures nothing.** The first `root-only`
switch dropped the child constraint *and* the occurrence check that the original
bug still performed, which makes the rule more permissive rather than
under-constrained — so it looked as though nothing caught `root-only`, when in
fact eight cases do.

`binder-1st` is still caught only indirectly, by order-independence rather than by
disagreeing with the reference. A direct witness would be better.

### Not covered

* **Symmetry branching.** The reference's `unify` returns several states when two
  invocations differ in two or more slots and more than one pairing is legal,
  where a primitive returns one. `U1` builds the shape deliberately — two atoms
  over a node whose slots are both redundant, so each lookup freshens them
  independently — and both sides still agree. Two constructions tried, neither
  discriminates, so the question is *open, not settled*: the encoding may be fine
  here, or the observable may simply be too coarse to see it.
* **Other action shapes.** Two are now generated: building a node, and equating
  two variables (`E1`–`E3`), which is the union of two invocations egglog's own
  `union` cannot express. Nothing exercises a right-hand side deeper than one
  level, or the `Subst` form.
* **Cost.** The one performance problem found turned out to be the minting policy
  above, and no case in 250 now times out or fails to settle. That is not the same
  as knowing the encoding is fast: nothing here is a benchmark, the terms are tiny,
  and the machinery has known derive-and-delete pairs that do redundant work.

## Mistakes worth not repeating

Each of these was silent, and each cost a round of confusion.

**In the encoding**

* *`union` in an action off the identity renaming* — asserts a false equation,
  absorbed as a spurious redundancy. `C11`.
* *An atom's renaming solved from its root alone* — under-constrained as soon as a
  node carries a redundant slot.
* *Atoms compiled in the order written* — an unconnected atom invents slots it
  cannot revise, and loses matches. `C12`.
* *A slot literal checked after the renaming was solved* — same failure: two
  binders written with the same slot each invent their own, then cannot agree.
  Constrain with it, do not check against it.
* *Invented slots colliding across atoms* — the avoid-set has to accumulate.
* ***`compose` truncates, silently.*** It keeps only the keys whose value lies in
  the left map's domain, so every `(compose a b)` on an edge is a place a slot can
  disappear — and a narrowed edge asserts its child is slotless. This one mistake
  is behind the fresh-slot gap, the `M6` unsoundness, and the migration bug above.
  The lesson is not "avoid `compose`" — narrowing is correct for partial maps, and
  two rules depend on it. It is that **an `App` edge is the one place narrowing is
  always wrong**, so use `compose-total` there and let the primitive hold the
  invariant. Wherever you use plain `compose`, ask where the result lands.
* ***A deleted fact does not come back.*** If rule A derives a fact from a row and
  rule B deletes that fact, A will not re-derive it — semi-naive fires A on a *new*
  row, and the row is no longer new. So a maintenance rule that deletes another
  rule's output has permanently overridden it, not temporarily. This is the whole of
  `Case 14`, and it is the same shape as open question 2. Before writing a `delete`,
  ask which rule produced the thing and whether it could ever fire again.
* *Argument order.* The renaming comes *before* each child:
  `(App String Renaming U Renaming U)`, `(RenamesToLeader U Renaming U)`.
* *Child rewrite direction.* It is `(compose m1 m)`, not
  `(compose r_i (inverse R))`.
* *A variable reached two ways does not compile to `(= path_i path_j)`.* That is
  equality of renamings; it has to be the symmetry lookup above.
* *A head is not special.* A variable used as both a constructor head and a child
  is just a variable with two occurrences.

**In the test harness**

* *A slotted e-class is not an egglog e-class.* Grouping probes by egglog class is
  strictly finer and reports differences that are not there.
* *`eg.eq` is not class identity.* It compares invocations, so it depends on which
  slot names survive a redundancy.
* *A bare leaf at top level loses its slot.* This alone accounted for every
  apparent machinery difference: 13 of 200 before the fix, 0 after.
* *An operator can be named differently on the two sides.* The machinery's
  α-equivalence rule is written against the literal string `"lambda"`, so a rule
  compiled for `"lam"` silently matches nothing.
* *A regression case can stop being one.* Changing the minting policy left `C11`
  and `R2` passing whether or not the bug they were written for was present. Put
  the bug back and check the test fails — `XDIFF_BUGS=` exists for that.
* *And so can a mutant.* If the switch that puts a bug back does not reproduce
  what the bug actually did, the coverage it reports is fiction in either
  direction.
* *A generator's defaults are part of its coverage.* Rooting every action at an
  atom root meant the action's renaming was almost always the identity, so nothing
  exercised the difference between unioning classes and unioning invocations.

## Cost

Per rule, against a non-slotted encoding: one extra `Renaming` column per child
position per atom; one fully-bound `RenamesToLeader` *lookup* per repeated
occurrence; one `find-mapping-total` per atom, with a `RenamesToLeader` *join* per
variable it is constrained through. Only the joins fan out, and `RenamesToLeader`
is small — usually one self-loop per class.

## Where `compose` can lose a slot

`(compose a b)` keeps only the keys of `b` whose value lies in `a`'s domain, so
every composition is a place a slot can silently vanish. That is not a defect —
it is the composition of partial maps, and two things depend on it. Auditing each
site in the machinery, and checking on real cases which ones actually truncate:

| site | truncation | why it is or is not a problem |
| --- | --- | --- |
| idempotence tests — `(bool= (compose m m) m)`, and the shrinking rule | intended | truncation *is* the test: it is how a non-permutation is detected |
| child-update, `(compose m1 m)` | impossible | `m`'s image is inside `m1`'s domain by well-formedness |
| **migration**, `(compose (inverse m) m1)` | **observed** | **was unsound**: the narrowed edge is asserted as fact, claiming its child is slotless. Now `compose-total` |
| single-parent, `(compose (inverse m1) m2)` | possible, never observed | lands in a `RenamesToLeader` row, where a partial map is meaningful. 0 occurrences across the corpus |
| transitivity, `(compose m12 m23)` | observed on `X1` | same: narrowing through a partial self-loop says the slots are redundant, which is what a partial map means there |
| α-finder and symmetry-finder, `(compose m_o sym)` | observed on `X1` | feeds `find-mapping`, which requires equal key sets, so a narrowed map makes the rule *not fire*: incomplete, not unsound |
| `MISC`, `(compose m1 (inverse m2))` | possible | only feeds an idempotence test, so a truncation means no union: incomplete, not unsound |

The first reading of this table was "truncation is harmless where it makes a rule
decline, dangerous where the composed map is inserted as a fact". That is wrong:
single-parent and transitivity both insert composed maps and are fine. **What
matters is where the map lands:**

| landing site | may it narrow? | why |
| --- | --- | --- |
| an `App` **edge** (`m1`/`m2`) | **never** | Def. 4 requires `dom(m) = slots(child)`, so a narrowed edge misstates *the child* |
| a `RenamesToLeader` renaming | yes | a partial map is meaningful there — it is how a redundant slot is recorded |
| the input to a test | yes | failure just makes the rule decline |

Only the first line needs anything from the primitives, and only two sites produce
an edge from a composition: migration, and child-update where it cannot happen. So
migration uses `compose-total`, which refuses to drop a key, and the guard that
used to compare `map-length` by hand is gone — the invariant is stated once, in the
name of the primitive, instead of re-derived per site. A narrowing composition can
no longer reach an edge position by accident.

## Primitives

What the encoding relies on. All of these were already here, ported from
[`memoryleak47/egglog@slotted-encoding2`](https://github.com/memoryleak47/egglog/tree/slotted-encoding2)
and rewritten against this tree's `add_primitive!`, **except
`find-mapping-total`**, which is new:

* `egglog/src/sort/map.rs`
  * `map-union` — partial-map union, fails on a conflicting key.
  * `compose` — `(compose a b)[x] = a[b[x]]`; explicit partial maps, so a missing
    key means "no mapping", not "identity".
  * `compose-total` — the same composition, refusing to drop a key. For the one
    place narrowing is always wrong: a result that becomes an `App` edge.
  * `map-image`, `map-domain` — a renaming's two slot sets, as identity maps.
    Slot sets *are* identity renamings here, so these name what used to be spelled
    `(compose m (inverse m))` and `(compose (inverse m) m)`. The node-slots idiom
    `(find-mapping p1 p2 p1 p2)` becomes
    `(map-union (map-image p1) (map-image p2))`, which says what it is.
  * `inverse` (also `map-inverse`) — rejects a non-injective map, whose inverse is
    not meaningful. Measured: the machinery never builds one, so this only turns a
    silently wrong answer into a rule that does not fire.
  * `find-mapping` — variadic, taking the two tuples flat as `[first…, second…]`.
    Strict: a paired `(first[i], second[i])` must carry the same key set, and the
    result must come out functional and one-to-one. That one-to-one check is
    load-bearing — it is what keeps `k($50,$50)` and `k($50,$60)` apart.
  * `find-mapping-total` — as above, extended to be total on a domain, inventing
    slots for the keys the constraints leave unnamed. `Map i64 i64` only, since
    inventing a slot needs the space ordered and unbounded above.
* `egglog/src/lib.rs` — `bool=`.
* `egglog/src/sort/bool.rs` — `and` made variadic, like `or`.

The renaming primitives are registered only when the key and value sorts match,
and deliberately not reserved: reserving `compose` breaks
`egglog/tests/tricky-type-checking.egg`, which declares its own.

Not ported: `shape2` (no consumer here), `has_delta` (a stub), and the `Vec i64`
flavour of `find-mapping` (a different representation).

## Open questions

1. **Choice of first atom.** It must not be a binder (`C13`), and beyond that the
   choice decides how many atoms have to solve for a renaming. Probably pick the
   one with the most shared variables, or leave it to the query planner. Also
   unsettled: what to do when *every* atom is a binder — the compiler currently
   just takes the first, and no test forces the question.
2. **Are self-edges derived from nodes a problem?** Two machinery rules derive a
   class-level self-edge from a node's own edges. Under redundancy that states
   something false about the class, and although the shrinking rule deletes the
   too-wide identity, semi-naive never re-runs the derivation, so the saturated
   state is not a fixpoint of its own rules. It reproduces in eight lines:

   ```text
   (relation SymSeen (U Renaming))
   (rule ((RenamesToLeader c m c)) ((SymSeen c m)))

   (let $f (App "f" (map-insert (map-empty) 0 0) (Var 0)
                    (map-insert (map-empty) 1 1) (Var 1)))
   (union $f (Null))
   (run-schedule (saturate (run)))

   (check      (SymSeen (Null) (map-empty)))
   (fail (check (SymSeen (Null) m) (!= m (map-empty))))   ; fails
   ```

   **Measured, and there is no rule to fix.** The shrinking rule does narrow the
   too-wide identity away: with a narrow idempotent `m` beside a wide `m1`,
   `compose m (compose m1 m)` is the narrow one, so the rule deletes `m1`. In the
   eight-line case above the wide loop is derived and then gone. Under
   `run-schedule (saturate (run))`, `X2`, `C5`, `S2` and `B2` all reach a genuine
   fixpoint; only `X1` does not, and that is its *rule* growing — its action is
   `union ?x1 (h ?x3 ?x1)`, which builds a new node every round. A program that
   never saturates keeps creating nodes, each of which re-derives the wide loop, so
   there it survives; on the same e-graph with no rule, nothing does.
   `slotted-experiments/xdiff/fixpoint.py` is the check.

   So the derive/delete pair converges whenever the program does. What is left is
   the shape of the mistake, worth not repeating: **do not derive a class-level
   fact from a node**, and prefer a merge that can only move one way over two rules
   that derive and delete against each other.
3. **Redundant slots in the pattern's slots.** The pattern's slots are the first
   atom's *node* slots, which may include slots the class has already made
   redundant. That falls out for free, but it means the pattern's slots are not
   always a subset of the class's live slots — check nothing downstream assumes
   otherwise.
4. **Stranded nodes.** Fixed for the single-parent mechanism (`Case 14`), but `X1`
   still strands one row via the shrinking rule deleting a too-wide identity
   self-loop — question 2 above. That row is harmless (it has a visible α-variant),
   so the open part is whether the shrinking rule can strand a row that does not.
   `slotted-experiments/xdiff/stranded.py` is the detector: it reports, per case, how
   many rows no symmetry-joining rule can see and how many of those are α-variants
   of nothing visible. Worth running after any change to the maintenance rules.

## Machine-checked invariants

Def. 4 — an edge's domain is exactly its child's slot set — used to be maintained by
discipline alone. `slotted-experiments/xdiff/invariants.py` checks the half that is
provable, plus the precondition `inverse` relies on:

* **An edge wider than its child.** An idempotent self-loop `s` on the child is a
  partial identity, so `child = s*child` and every slot outside `dom(s)` is
  redundant: the child's live slots are inside `dom(s)`. An idempotent self-loop
  with *fewer* keys than the edge therefore proves the edge names slots the child
  does not have. Looking only for narrower witnesses is what makes this immune to
  question 2's too-wide loops — an earlier version compared against an arbitrary
  self-loop and reported eight "bad edges" on `X1` that were all a correct `{0→0}`
  edge to `(Var 0)` sitting beside a bogus `{0→0, 2→2}` loop.
* **A stored renaming that is not injective**, which is what `inverse` needs and
  nothing checked. Zero across the corpus, so `inverse` being strict costs nothing.

The narrow direction is not checkable this way, and is what `compose-total` now
prevents where it was reachable.

Across the corpus: 0 non-injective renamings, and one wide edge, on `X1`. It is
built by the compiled action out of question 2's surviving too-wide loop, and it is
inert — the slots it names are redundant for that child, so `m*c = c` either way.
Both probes take a snapshot: they declare their rules in their own ruleset and run
only that, because a relation keeps an observation after the row that caused it is
deleted, which answers a question about history instead.
