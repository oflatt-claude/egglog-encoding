# Encoding user rules into the slotted encoding

Companion to `tests/slotted-egraph-encoding-11.egg` (the machinery) and
`tests/slotted-user-rules.egg` (hand-encoded user rules, all runnable).
See [Easy things to get wrong](#easy-things-to-get-wrong) for the design points
an earlier draft of this encoding got backwards.

Ground truth for the semantics is Schneider et al., *Slotted E-Graphs*, PLDI
2025 ([PDF](https://steuwer.info/files/publications/2025/PLDI-Slotted-E-Graphs.pdf),
[impl](https://github.com/memoryleak47/slotted-egraphs)) — in particular
Definition 6 (equivalence of renamed ids), Definition 8 (which e-nodes a
renamed id represents), §3.5 (`union`), and §3.6 (e-matching).

## Notation

This document uses the paper's names throughout. From §3.6, `match(p, m * a, β, mp)`:

| symbol | paper's words |
| --- | --- |
| `slots(a)` | the e-class's slots, `M[a].S` — "the free variables, or free slots, of this e-class" |
| `m * a` | a **renamed id**: an e-class plus a renaming of its slots (the crate calls it an "invocation") |
| `β` | "a substitution mapping from pattern variables to renamed ids" |
| `mp` | "a renaming that maps the slots from the e-graph to the slots of the pattern" |
| `mp′` | "the minimal renaming, s.t. `mp′ * f(nc)` matches `f(pc)`, and where `mp ∪ mp′` is a bijective renaming" |
| `G(a)` | the e-class's permutation group, `M[a].G` |
| `≡` | equivalence of renamed ids (Def. 6) |

The only term added here is **initial atom**, for the atom matching starts
from — the paper's `match` is "initially called with `β = mp = ∅`, and where
`m` is the identity renaming from `slots(a)` to itself", and with a
single-rooted pattern there is nothing to name. egglog rule bodies are
conjunctive and multi-rooted, so there is a choice to make.

Two facts about slots that everything below rests on. Slots are named *locally*
to whatever owns them — `(Var 0)`'s `$0` and some `f` node's `$0` are unrelated
names that happen to coincide — so the only way to relate one e-class's slots
to another's is to write down a renaming. And the pattern has slots of its own:
a match must carry every variable it binds into `slots(pattern)` before those
variables can be compared or used.

## Conventions of the machinery file

| notation | meaning |
| --- | --- |
| `(compose a b)` | `a ∘ b` — `b` applies first: `(compose a b)[x] = a[b[x]]` |
| `(App f m1 c1 m2 c2)` | `f(m1*c1, m2*c2)`; each `mi : slots(ci) → slots(node)` |
| `(RenamesToLeader a m b)` | `a = m*b`, so `m : slots(b) → slots(a)` |
| `(RenamesToLeader c m c)` | `m ∈ G(c)` — the group, materialised as self-loops |
| `(find-mapping a1 … an b1 … bn)` | least `m` with `m ∘ bi = ai` for every `i`; fails if no injective `m` exists |

Note `compose`'s order is the *opposite* of `SlotMap::compose` in the Rust
crate, which applies the receiver first.

The self-loops are really an inverse monoid of partial injections rather than
`G(c)` exactly: the idempotents (`m ∘ m = m`, i.e. partial identities) are how
the machinery records *redundant* slots, and the "single parent for symmetries"
rule shrinks every self-map down to the live slot set. On a saturated e-graph
they are a group on the live slots, which is what makes the reasoning below
work.

## The model: a U-variable is a renamed id, not an e-class

This is the whole design in one sentence: **the compiled rule body computes the
paper's `β` and `mp` explicitly.**

`β` maps a pattern variable to a renamed id, so a user rule variable `x : U`
compiles to *two* egglog variables — the leader `X : U` and a renaming
`mx : slots(X) → slots(pattern)` — together standing for `β(x) = mx * X`.

`slots(pattern)` is not invented. We take one atom, the **initial atom**, and
declare its matched node's slots to be the pattern's; its `mp` is then the
identity and never has to be written down.

Everything else follows mechanically.

## Compiling the body

First **flatten** the rule's LHS into depth-1 atoms `?v == (Op ?c1 ?c2)`, one
per e-node, every child a bare pattern variable — the reference crate's
`MultiPattern`, and the shape an egglog rule body already wants. Depth 0 is
preprocessing and depth >1 flattens by naming intermediate nodes.

Flattening is not meaning-preserving in general: a nested pattern is matched
under one renaming for the whole pattern, a flattened one gets a renaming per
atom, so a slot literal written both under a binder and outside it lets the
binder escape. A flattener has to reject or rename those.

Then process the atoms in an order where each atom after the first shares a
variable with the already-processed part. Each atom needs an `mp` carrying its
node's slots into `slots(pattern)`, and there are exactly three ways to get one:

1. **Initial atom** — `mp = id`. Nothing is emitted; the children's stored edges
   *are* their pattern-slot renamings.
2. **Root already in `dom(β)`** — the atom's root variable is one `β` already
   binds. This is the eta case: `b` is a child of atom 1 and the root of atom 2.
   Then `mp = (compose mb symB)`, joining `(RenamesToLeader B symB B)`, i.e.
   picking `symB ∈ G(B)`.
3. **`mp` must be extended** — the atom's root is a variable seen for the first
   time, so nothing yet relates its node's slots to the pattern's. This is the
   paper's `mp′`: the minimal renaming making the node match, solved for through
   the *children* the atom shares with `dom(β)`. With shared children `x_i` at
   stored edges `p_i`, `mp′` is the least map with `mp′ ∘ p_i = mx_i ∘ sym_i`:

   ```text
   (RenamesToLeader X1 sym1 X1)
   (RenamesToLeader X2 sym2 X2)
   (= mp' (find-mapping (compose mx1 sym1) (compose mx2 sym2) p1 p2))
   ```

   With one shared child, equivalently `(compose (compose mx1 sym1) (inverse p1))`.
   `find-mapping`'s injectivity check is the paper's requirement that
   `mp ∪ mp′` be bijective. M4 and M5 are the worked examples; M6 is what goes wrong when
   `mp′` does not cover the whole node.

Then walk the atom's children. A child at stored edge `p` has candidate
renaming `(compose mp p)`. If its variable is not in `dom(β)`, that *is* its
`mx` — `β` grows. If it is, emit the equivalence check.

## The equivalence check

This is the answer to "what does the query need to check". It is the second
case of the paper's `match(x, m * a, β, mp)`: when `x ∈ dom(β)`, keep the match
only if `β(x) ≡ m * a`. Definition 6, for two renamed ids of the same leader:

> `m1 * c ≡ m2 * c`  iff  `m2⁻¹ ∘ m1 ∈ G(c)`

Both renamings are bound by the time this runs, so the group element it would
need is *determined*. Compute it and look it up — do not enumerate:

```text
(= sym (compose (inverse mx) (compose mp p)))
(RenamesToLeader X sym X)
```

`(RenamesToLeader X sym X)` with all three arguments bound is an existence
check on an already-indexed relation, not a join that fans out over `G(X)`.
The enumerate-then-compare spelling

```text
(RenamesToLeader X sym X)
(= (compose mp p) (compose mx sym))
```

means the same thing and is what the machinery file's own rules use, but it
makes the planner produce `|G(X)|` candidate rows per match and discard all but
one. `tests/slotted-user-rules.egg` M2 runs both and checks they agree,
including on the case that needs a real swap.

The two can only diverge if the computed `sym` comes out *shorter* than `mx`
(when `im(mp ∘ p) ⊄ im(mx)`, composition truncates) and that shorter map happens
to be a recorded self-loop. The machinery's shrinking rule keeps every self-map
at the live slot set, so on a saturated e-graph there is only one domain in play
and no shorter map to hit. Add `(= (map-length sym) (map-length mx))` if you
want that independent of saturation.

What you cannot drop is the group *membership test*: that is Definition 6. What
you drop is the enumeration.

*Neither* form may be weakened to `(= (compose mp p) mx)`. Syntactic equality of
renamings is strictly weaker than `≡`, and the difference is observable.
M2(c) matches `f(x, x)` against `f(a[$0,$1], a[$1,$0])` where `a` is symmetric:
the two occurrences of `x` *are* the same renamed id, the `≡`-aware rule fires,
and the `NaiveHit` witness relation stays empty. The machinery will not rewrite
the node so the two edges become equal — the child-update rule explicitly
excludes non-idempotent self-maps — so this is not a case you can normalise away
first.

### Extending `mp` is the exception

Case 3 above looks like the same check, and it is — but it cannot be demoted to
a lookup, because there `mp′` is the *unknown*. Every shared variable
contributes part of it as well as constraining it, and until the last one is in,
`mp′` is still partial: `(compose mp' p)` for a not-yet-covered child truncates
to something meaningless, so there is nothing to compute a group element from.
That is why all the pairs go into one `find-mapping`, and why its `sym_i` are
genuinely enumerated.

M4 makes this concrete. `TooEager` there builds `mp′` from `x` alone and then
probes `y` against it; on M4(a) — `f(v[$0], v[$1])` against `g(v[$0], v[$1])` —
`im(p2)` is only `{$0}`, `mp′` never reaches `$1`, and the match is silently
lost. On M4(c) the same demotion happens to work, because there `im(p2)` covers
all of the node's slots. Whether `mp′` is already total is a property of the
data, not of the rule, so a compiler cannot rely on it.

The general shape, then: **a group element is a lookup when the renamings on
both sides are known, and an enumeration when one of them is being solved for.**

`find-mapping` fails when the constraints disagree or when the result is not
injective. M4(b) is the negative: `f(x,y)` against `g(x,x)` admits no `mp′`.

## Where group joins are needed, and where they are not

The paper's `match` unions over every e-node *represented by* the renamed id
(Def. 8), which includes all group-permuted variants. The reference
implementation does this explicitly in `get_group_compatible_weak_variants`.
The encoding stores only one variant per orbit — the α-finder deletes the
others and records the symmetry — so those variants must be regenerated.

The claim is that regenerating them where `≡` is checked is enough:

> **Every occurrence of a U-variable after the first contributes one `G` lookup
> and one constraint. The first occurrence contributes neither.**

* *First occurrence is free.* Binding `mx := (compose mp p) ∘ σ` instead of
  `(compose mp p)` just reparameterises every later constraint by `σ`, and
  `σ ∘ G(X) = G(X)`.
* *The initial atom needs no join.* A group element of its root relabels
  `slots(pattern)` by a bijection; since the action is built entirely in pattern
  slots, the result is an α-variant, which the machinery identifies anyway.
* *An atom that extends `mp` needs no separate `G(root)` join.* `mp′` is pinned
  on `⋃ im(p_i)` by the constraints, and the valid `mp′` are enumerated exactly
  by the `sym_i`. Applying a root permutation afterwards either breaks a
  constraint or reproduces an `mp′` already enumerated.
* *Variables used only once need no join*, because differing by a group element
  produces an α-variant of the action's output.

In practice `G(X)` is trivial, and `≡` checks are lookups rather than joins
(above), so the only real fan-out left is the `sym_i` of case 3.

The one place this reasoning leans on an assumption is the group-ness of the
self-loops: with a non-invertible idempotent in the monoid, `σ ∘ G = G` can fail
and "first occurrence is free" would need re-checking. Saturation should
restrict self-maps to live slots, making them a group, but that is worth
verifying.

## Actions

Each U-variable at a child position in the action uses its `mx`. New nodes are
built in pattern slots.

`union` needs care. The paper's `union` takes *renamed ids* — §3.5 is
`union(m1 * a1, m2 * a2)`, and which of redundancy, a new group element, or an
e-class merge it produces depends on those renamings. egglog's `union` takes
e-classes, i.e. only the case where both renamings are the identity. So:

* both operands at the identity → plain `(union A B)`;
* otherwise → insert the `RenamesToLeader` fact directly:

  ```text
  ;; user:  (union e x)   with  e at the identity, x at mx
  (RenamesToLeader E mx X)
  ```

  The machinery's transitivity / single-parent rules re-orient it, and the
  `MISC` rule promotes it to a real `union` once the renaming turns out to be an
  identity. M2 and M7 both need this; M8 states it as a relation.

So the surface language wants an action that takes renamed ids, or the encoder
has to synthesise the `RenamesToLeader` insert itself.

**This is not a nicety, and getting it wrong is silent.** A plain
`(union root built)` asserts an equation whose two renamings are the identity.
When the root's renaming is not the identity, that equation is simply *false* —
it conflates two distinct pattern slots — and the e-graph absorbs it as spurious
redundancy rather than complaining. `C11` in `xdiff.py` is the worked case: a
root renaming of `{$0↦$3, $2↦$2}` drove `(Var 0)` from one live slot to none,
after which child-update emptied every edge and `h(x,y)` collapsed with
`h(x,x)`. Two things about the failure are worth remembering:

* the built node was *correct* — the corruption was entirely in how it was
  attached, so inspecting the action's output tells you nothing;
* an edge-width check does not catch it, because the children's classes go
  slotless too and the widths agree again by the end.

The safe rule for a compiler: emit `union` **only** when the action's root is the
initial atom's root, whose `mp` is the identity by construction. Anywhere else,
emit the `RenamesToLeader` fact. Restricting the built node to the root's slot
space instead (composing every child renaming through `inverse mp_root`) is also
sound, but it needs a totality guard and then declines to fire on cases the
`RenamesToLeader` form handles.

## Fresh slots

`find-mapping` gives the *minimal* `mp′`, exactly as Definition 8 asks, so a
slot of the node outside `⋃ im(p_i)` gets no name in `slots(pattern)`. The paper
covers this in the last line of §3.6 — a redundant or bound slot would stand for
infinitely many e-nodes, but "for the purpose of this algorithm, it suffices to
pick any fresh slot for them". A `Renaming` is only a map, so minimal `mp′`
silently *drops* the slot, leaving an edge whose domain is smaller than its
child's slot set — which Definition 4 forbids.

M6 is the worked case. For

```text
(rule ((= p (App "f" x y)) (= q (App "g" x z))) ((union p (App "h" y z))))
```

with `p = f(v[$0], v[$1])` and `q = g(v[$0], v[$5])`, minimal `mp′` is `{$0↦$0}`,
`z`'s renaming comes out empty, and the action builds `h(y, z)` with an empty
edge to `z`.

**What to measure.** Not "did `p` lose a slot?" — that assertion does not
isolate the bug. `f(x,y) = h(y,z)` genuinely says `f` does not depend on `x`, so
`p` losing `$0` is the correct reading of the rule and happens in the fixed
version too. The narrow observable is the malformed edge; M6's `BadEdge`
relation witnesses it directly, and that is what separates the two.

`find-mapping-total` closes the gap: same constraints and same injectivity check
as `find-mapping`, plus a fresh name for every domain slot the constraints leave
unnamed.

```text
(find-mapping-total avoid domain first… second…)
```

`domain`'s keys are the slots the result must cover and `avoid`'s slots are the
ones it may not mint over; both are identity maps the caller already has, since
`(find-mapping p1 p2 p1 p2)` is the identity on a node's slots. Minted slots go
strictly above everything mentioned, so the result stays injective and cannot
collide with a slot in play. Any deterministic choice works, because differing
choices produce α-variants that the machinery identifies anyway.

The sound-but-incomplete alternative is still worth knowing, since it needs no
primitive: guard every action-used variable with
`(= (map-length (compose mp' p)) (map-length p))`. M6(b) shows the rule then
declines to fire in the bad case and still fires in the good one. `≡` checks are
self-guarding already, since a dropped slot changes the domain and breaks the
equation.

The same gap in its extreme form: a body whose atoms share *no* variable gives
no constraint on `mp′` at all, so that node's slots are named entirely by
minting. Rules whose RHS introduces a binder (eta-expansion) need this too.

## Fidelity to `multi_ematch`

Differentially tested against the reference implementation
(`slotted-experiments/xmulti` runs the oracle; `tests/slotted-multipat-diff.egg`
runs the encoded form).

**The three cases above are really one, and splitting them loses matches.** An
atom's `mp` must be the least total renaming consistent with *everything already
known about that atom* — its root **and** every already-bound child. Case 2 as
written derives `mp` from the root alone, which is under-constrained exactly when
the node carries slots the root's renaming does not cover, i.e. redundant slots.
The atom then names those slots independently of an earlier atom that already
named the same ones, and the repeated variable's `≡` check fails.

Two cases pin it. Both use `add(zero, zero)` over nodes with a redundant slot,
with `?u` written in two atoms so its occurrences must be identified.

* **R1**, both atoms over the *same* node — agrees under either spelling, but by
  coincidence: `find-mapping-total` is a pure function, both atoms hand it the
  same arguments, so it returns the same minted slot. Determinism stands in for
  unification, which is why R1 alone would not have caught this.
* **R2**, two *different* nodes with redundant slots named `$9` and `$7` —
  root-only mints `$10` and `$8` and loses the match (reference 1, encoding 0).
  Folding `?u`'s known renaming in as a constraint pins atom 3 to `$10` and the
  reference's match comes back.

So the fix is to stop treating the three cases as different shapes: emit one
`find-mapping-total` per atom over every constraint available at that point.
"Extending `mp` is the exception" understates it — extension is the *general*
case, and initial/chain are just the instances with no constraints and with
root-only constraints respectively.

Worth being clear about what this is **not**: not a limit of egglog, and not a
missing merge step. Solving for a renaming *is* construction, and a constraint
computed in an earlier atom threads into a later one as an ordinary value, so
purity is no obstacle. What genuinely cannot move into a primitive is the group
membership test, since a primitive cannot query the database —
`(RenamesToLeader c sym c)` stays an egglog join, and it is also where the
nondeterminism `unify` gets from branching has to come from.

### What the sweep found

`slotted-experiments/xdiff/xdiff.py` generates cases, compiles each
multipattern, runs both sides, and compares the probe partition. Results:

Over 150 generated cases plus the curated corpus, on a run where 21 of 141
usable cases actually fired the rule:

* **One unsoundness, and it is also the one order dependence.** Kept as curated
  case `C11`. The encoding derives `h(x,y) = h(x,x)`; the reference refuses, and
  is right to — Def. 8 makes each lookup's renaming injective, so a node with two
  distinct slots can never represent `h(x,x)`
  (`regress::same_node_redundant_slots_stay_distinct` in the crate).

  The reference builds `h` over two distinct slots and keeps the probes apart.
  The encoding ends up with exactly **one** `h` node, **both edges empty**, and
  its class carrying no slots, so both probes collapse into it. That is a dropped
  slot again — the same family as the fresh-slot gap above, but reached through
  the *action* rather than through `find-mapping`. A `BadEdge`-style width check
  does **not** catch it: by the end the children's classes have gone slotless
  too, so the widths agree.

  The order dependence is consistent with the cause: `C11` has two atoms sharing
  no variable, so one of them mints, and which slot space it mints into depends
  on which atom went first.
* **Order independence otherwise holds**, across every permutation of every other
  multi-atom case. Minting made the compilation order-sensitive by construction,
  so this was expected to break much more widely than it did.
* **No other matching divergence** in any case where the machinery agreed.
* **The machinery under-merges.** Nine of 150 differ with no user rule at all,
  always in the direction of the encoding deriving *fewer* equalities. Traced in
  one case to leaf-class redundancy: `union (var $0) (var $2)` makes the variable
  class slotless, so in the crate every `h(var, var)` collapses into one class;
  the encoding does not propagate that. Incompleteness rather than unsoundness,
  and outside matching.

### Two ways to measure this wrong

Both cost a round of false findings, so they are worth stating:

1. **A slotted e-class is not an egglog e-class.** The α-finder relates
   equal-up-to-renaming nodes with `RenamesToLeader` and *deletes* one rather
   than unioning them, so a slotted class is a set of `U` values sharing a
   leader. Grouping probes by egglog e-class is strictly finer and reports
   differences that are not there.
2. **`eg.eq` is not e-class identity.** It is equality of *renamed ids*, so it
   depends on which slot names the invocation carries: after a redundancy two
   probe terms can sit in one class while naming different surviving slots, and
   `eg.eq` calls those unequal. Use it deliberately, not as "are these the same".

### Still unverified

1. **Coverage.** A case where the rule never fires tests nothing about matching,
   and random patterns mostly do not fire; the harness reports the firing count
   for exactly this reason. Read the "of those had the rule actually change the
   partition" line before believing an agreement count.
2. **Branching.** `unify` returns *several* states; a primitive returns one. The
   claim that enumerating `G` through `RenamesToLeader` covers the difference is
   still just a claim — no generated case has forced it.
3. **Actions.** Only one action shape is generated (`union ?root (h ?a ?b)`).
   Nothing exercises `union` over two non-identity renamings, which is the case
   egglog's `union` cannot express at all.

## Unresolved: self-edges are derived from nodes

Flagging this as an open question, not a fixed bug — the evidence is thinner
than it first looked.

Two rules derive a self-edge from a node's own edges (`find-mapping m1 m1' m1
m1'`, the identity on the node's slots). Redundancy is *defined* as a node
keeping slots its class has dropped (Def. 4: slots in `im(m)` but not in `S`),
so under redundancy those rules state something false about the class. The
shrinking rule deletes the too-wide identity, but only once — semi-naive never
re-runs a derivation on an already-consumed `App` row — so the saturated state
is not a fixpoint of its own rules.

It reproduces in eight lines. `(Null)` has no slots — that is asserted, not
derived — yet a monotone observer catches it transiently carrying a two-slot
identity:

```text
(relation SymSeen (U Renaming))
(rule ((RenamesToLeader c m c)) ((SymSeen c m)))

(let $f (App "f" (map-insert (map-empty) 0 0) (Var 0)
                 (map-insert (map-empty) 1 1) (Var 1)))
(union $f (Null))                        ; both of $f's slots go redundant
(run-schedule (saturate (run)))

(check      (SymSeen (Null) (map-empty)))
(fail (check (SymSeen (Null) m) (!= m (map-empty))))   ; fails: {$0↦$0,$1↦$1}
```

Note the machinery's own Case 13 asserts the same thing about the *end* state
and passes — the wide identity is deleted by then. The two differ only in
whether they can see inside the phase.

**Why it probably does not matter.** Two things came out of trying to turn this
into a wrong answer, and both cut against acting on it:

* A too-wide identity is *inert*. Every consumer of `RenamesToLeader c sym c`
  uses `sym` by composing it with an edge, and once child-update has narrowed
  the edges to the live slots, `compose edge wide == compose edge narrow`. Seven
  scenarios — re-triggering the derivation after saturation, parents built
  before the redundancy, fresh α-equivalent rows, interacting redundancies, the
  M4 glue rule over a redundant shared variable — all came out byte-identical.
* **Phasing hides it entirely.** The wide edge is only observable by a rule
  co-scheduled with maintenance. Introduce the observer *after* the maintenance
  phase and the check above passes, because `saturate`
  runs to fixpoint and the shrinking rule wins by the end of every phase. So if
  user rules run only at phase boundaries, this cannot reach them.

A candidate fix exists — `LiveId`, a function whose merge intersects, so
re-deriving a wider identity is absorbed instead of having to be deleted — but
it is not recommended on this evidence and is not part of this change.

What is worth carrying into a rewrite is the shape of the mistake, not the
patch: **don't derive a class-level fact from a node**, and prefer a merge that
can only move one way over two rules that derive-and-delete against each other.
The machinery has other derive/delete pairs (the α-finder deletes `App` rows,
single-parent deletes `RenamesToLeader` rows) that I have not examined.

## Cost sketch

Per rule, relative to a non-slotted encoding: one extra `Renaming` column per
child position in every atom; one fully-bound `RenamesToLeader` *lookup* per
repeated-variable occurrence; one `find-mapping` per atom that extends `mp`,
with a `RenamesToLeader` *join* per variable it is constrained through; and one
totality guard per action-used variable. Only the joins fan out, and
`RenamesToLeader` is small — usually one self-loop per e-class.

## Easy things to get wrong

An earlier draft of this encoding (`slotted-encoding.md`, kept out of the
branch as historical) got each of the following wrong. They are the places
where a plausible reading of the design diverges from what the machinery
actually does, so they are worth stating positively:

* **Argument order.** The renaming comes *before* each child, not after:
  `(App String Renaming U Renaming U)` and `(RenamesToLeader U Renaming U)`.
* **Child rewrite direction.** It is `(compose m1 m)`, not
  `(compose r_i (inverse R))` — the inverse is wrong given
  `RenamesToLeader c1 m c'` meaning `c1 = m*c'`.
* **Leaves.** Every `(Var v)` collapses to `[0↦v] * (Var 0)` and the original
  is deleted — the leaves are not kept as distinct e-classes with pair rules
  between them.
* **The group is load-bearing.** An α-finder, migration, or child-rewrite rule
  written without a `G` join cannot see α-equivalences that hold only through a
  child's symmetry.
* **Rule compilation.** A variable reached by two paths does *not* compile to
  `(= path_i path_j)`. That is equality of renamings, not `≡`; it has to be
  `(= path_i (compose path_j sym))` with a `G` join, or the lookup form above.
* **`(union e x)`.** Without a union over renamed ids, any rule equating
  `m1 * a1` with `m2 * a2` for non-identity renamings is inexpressible.
* **A head is not special.** A variable used as both a constructor head and a
  child is just a variable with two occurrences, so it takes the same `≡` check
  as any other repeat — no separate head-identity synthesis is needed.

## Primitives

The machinery file did not run in this tree: `compose`, `inverse`,
`find-mapping` and `bool=` did not exist, and `and` was binary while the file
uses it variadically. They are ported from
[`memoryleak47/egglog@slotted-encoding2`](https://github.com/memoryleak47/egglog/tree/slotted-encoding2)
— same names and semantics, rewritten against this tree's `add_primitive!`
macro instead of hand-rolled `Primitive` impls.

* `egglog/src/sort/map.rs`
  * `map-union` — partial-map union for any `Map`, fails on a conflicting key.
  * `compose` — `(compose a b)[x] = a[b[x]]`; explicit partial maps, so a
    missing key means "no mapping", not identity.
  * `inverse` (also `map-inverse`) — total, matching upstream: a repeated value
    keeps the last key. Only meaningful on injective input, which is all the
    encoding ever builds. Making it fail instead changes no behaviour in any
    test here, so the port keeps upstream's.
  * `find-mapping` — variadic, taking the two tuples flat as
    `[first…, second…]`; returns the least `R` with `R ∘ second[i] = first[i]`.
    Strict: a paired `(first[i], second[i])` must carry exactly the same key
    set, and `R` must come out functional and injective.
  * `find-mapping-total` — `find-mapping` extended to be total on a domain,
    minting fresh slots for the keys the constraints leave unnamed. Takes
    `[avoid, domain, first…, second…]`. Registered only for `Map i64 i64`,
    since minting needs the slot space ordered and unbounded above.
* `egglog/src/lib.rs` — `bool=`.
* `egglog/src/sort/bool.rs` — `and` made variadic, like `or`.

The three renaming primitives are registered only when the key and value sorts
coincide, and deliberately **not** listed in `reserved_primitives`: reserving
`compose` breaks `egglog/tests/tricky-type-checking.egg`, which declares
`(constructor compose (TERM TERM) TERM)`. Registration happens when a `Map`
sort is created, so a program that never declares one keeps the names.

The injectivity check in `find-mapping` is load-bearing: it is what makes the
machinery's negative case 4 (`k($50,$50)` vs `k($50,$60)`) stay separate.

Not ported from that branch: `shape2` (canonical slot numbering — no consumer
here yet), `has_delta` (a stub whose comparison is `false // TODO`), and the
`Vec i64` flavour of `find-mapping` (a different renaming representation).

## Open questions

1. **Which slots `avoid` must contain.** `find-mapping-total` takes the
   avoid-set from its caller, and the rules here pass `slots(pattern)`. That is
   enough for one atom; a rule that mints in two different atoms should probably
   avoid the union of everything minted so far, which the current spelling does
   not thread through.
2. **Choice of initial atom.** Any atom can be it; the choice determines which
   atoms have to extend `mp`, hence how many `find-mapping`s and how early the
   query is constrained. Probably worth choosing the atom with the most shared
   variables, or leaving it to the query planner.
3. **Verify or construct?** See [Fidelity to `multi_ematch`](#fidelity-to-multi_ematch)
   — differential testing found the encoding strictly less complete. The
   remaining sub-question is whether the "one `G` lookup per later occurrence"
   claim is complete *given* a merge step; the argument for it is informal and
   rests on the self-loops being a group on live slots.
4. **Redundant slots in `slots(pattern)`.** The pattern's slots are the initial
   atom's *node* slots, which may include slots the *e-class* has already made
   redundant (Def. 8's `m'' ⊇ m'`). That falls out for free here, but it means
   `slots(pattern)` is not always a subset of the initial e-class's live slots —
   check nothing downstream assumes otherwise.
