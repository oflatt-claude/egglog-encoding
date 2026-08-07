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

Process the atoms in an order where each atom after the first shares a variable
with the already-processed part. Each atom needs an `mp` carrying its node's
slots into `slots(pattern)`, and there are exactly three ways to get one:

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
   `mp ∪ mp′` be bijective. U3 is the worked example; U5 is what goes wrong when
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
one. `tests/slotted-user-rules.egg` U2 runs both and checks they agree,
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
U2(c) matches `f(x, x)` against `f(a[$0,$1], a[$1,$0])` where `a` is symmetric:
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

U3 makes this concrete. `TooEager` there builds `mp′` from `x` alone and then
probes `y` against it; on U3(a) — `f(v[$0], v[$1])` against `g(v[$0], v[$1])` —
`im(p2)` is only `{$0}`, `mp′` never reaches `$1`, and the match is silently
lost. On U3(c) the same demotion happens to work, because there `im(p2)` covers
all of the node's slots. Whether `mp′` is already total is a property of the
data, not of the rule, so a compiler cannot rely on it.

The general shape, then: **a group element is a lookup when the renamings on
both sides are known, and an enumeration when one of them is being solved for.**

`find-mapping` fails when the constraints disagree or when the result is not
injective. U3(b) is the negative: `f(x,y)` against `g(x,x)` admits no `mp′`.

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
  identity. U2 and U4 both need this.

So the surface language wants an action that takes renamed ids, or the encoder
has to synthesise the `RenamesToLeader` insert itself.

## The gap: fresh slots

`find-mapping` gives the *minimal* `mp′`, exactly as Definition 8 asks, so a
slot of the node outside `⋃ im(p_i)` gets no name in `slots(pattern)`. The paper
covers this in the last line of §3.6 — a redundant or bound slot would stand for
infinitely many e-nodes, but "for the purpose of this algorithm, it suffices to
pick any fresh slot for them". A `Renaming` is only a map, so the encoding
instead silently *drops* the slot — and dropping a slot asserts that it is
redundant.

U5(a) shows this is not theoretical. For

```text
(rule ((= p (App "f" x y)) (= q (App "g" x z))) ((union p (App "h" y z))))
```

with `p = f(v[$0], v[$1])` and `q = g(v[$0], v[$5])`, `mp′` is `{$0↦$0}`, `z`'s
renaming comes out empty, the action builds `h(y, z)` with an empty edge to `z`,
and unioning that into `p` forces `p`'s slot `$0` to become redundant. Silent,
and wrong.

Two ways out:

* **Guard (sound, incomplete).** For every variable used in the action, require
  its renaming to keep all of its slots:
  `(= (map-length (compose mp' p)) (map-length p))`. U5(b) shows the rule then
  declines to fire in the bad case and still fires in the good one. `≡` checks
  are self-guarding already, since a dropped slot changes the domain and breaks
  the equation.
* **Mint fresh slots (complete).** Wants a primitive — something like
  `(map-complete-fresh partial domain avoid)` extending a partial map to be
  total on `domain` with values outside `avoid`. Any deterministic choice works
  because the result is canonicalised anyway. Deciding what `avoid` has to
  contain is the real design question; the natural answer is every slot
  currently in `im(mp)` anywhere in the rule.

The same gap in its extreme form: a body whose atoms share *no* variable gives
no constraint on `mp′` at all, so that node's slots would have to be freshly
named outright. Rules whose RHS introduces a binder (eta-expansion) need this
too.

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
  U3 glue rule over a redundant shared variable — all came out byte-identical.
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

1. **Fresh slots** — the gap above. Needs a primitive and a decision about the
   avoid-set.
2. **Choice of initial atom.** Any atom can be it; the choice determines which
   atoms have to extend `mp`, hence how many `find-mapping`s and how early the
   query is constrained. Probably worth choosing the atom with the most shared
   variables, or leaving it to the query planner.
3. **Is the "one `G` lookup per later occurrence" claim actually complete?** The
   argument above is informal and rests on the self-loops being a group on live
   slots. Worth a differential test against the `slotted-egraphs` crate.
4. **Redundant slots in `slots(pattern)`.** The pattern's slots are the initial
   atom's *node* slots, which may include slots the *e-class* has already made
   redundant (Def. 8's `m'' ⊇ m'`). That falls out for free here, but it means
   `slots(pattern)` is not always a subset of the initial e-class's live slots —
   check nothing downstream assumes otherwise.
