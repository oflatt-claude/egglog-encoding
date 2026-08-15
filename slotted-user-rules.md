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
it may not reuse. Both are identity maps the caller already has, since
`(find-mapping p1 p2 p1 p2)` is the identity on a node's slots.

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
same slot. Thread a running union: `compose m (inverse m)` is the identity on
`m`'s image, and identity maps never conflict under `map-union`, so the union is
always defined.

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

Fixed by declining to migrate when either edge would narrow. Sound but
incomplete, exactly like the totality guard in `M6(b)`: the redundant slot has no
name in `e1`'s space, and the complete fix is to mint one.

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
  Wherever you compose, ask what happens when the image escapes the domain.
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

## Primitives

Ported from
[`memoryleak47/egglog@slotted-encoding2`](https://github.com/memoryleak47/egglog/tree/slotted-encoding2),
rewritten against this tree's `add_primitive!`:

* `egglog/src/sort/map.rs`
  * `map-union` — partial-map union, fails on a conflicting key.
  * `compose` — `(compose a b)[x] = a[b[x]]`; explicit partial maps, so a missing
    key means "no mapping", not "identity".
  * `inverse` (also `map-inverse`) — total, matching upstream; only meaningful on
    one-to-one input, which is all the encoding builds.
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

   Probably harmless: a too-wide identity is inert, because every consumer
   composes it with an edge and the edges have already been narrowed. It is also
   only visible to a rule co-scheduled with maintenance, so user rules running at
   phase boundaries cannot see it. The lesson to carry forward is the shape of the
   mistake — **do not derive a class-level fact from a node** — and to prefer a
   merge that can only move one way over two rules that derive and delete against
   each other.
3. **Redundant slots in the pattern's slots.** The pattern's slots are the first
   atom's *node* slots, which may include slots the class has already made
   redundant. That falls out for free, but it means the pattern's slots are not
   always a subset of the class's live slots — check nothing downstream assumes
   otherwise.
