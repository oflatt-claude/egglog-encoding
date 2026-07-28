# Proof encoding rework: record minimal justifications

Working plan for the `proof-encoding-minimal` branch. The user-facing proof
format does not change; what changes is how much the e-graph stores to produce
it.

## Goal

A proof node records only *what justified* a fact — which rule fired, with
which premise proofs — and the connecting skeleton (`Congr` / `Trans` / `Sym`)
is **reconstructed during proof conversion** rather than materialized as rows
while rules run.

Today a rule that builds a term and unions it writes nine proof rows per
firing plus four `@Ast` rows. The target is one row.

## Why this is possible

Three mechanisms already in the tree, not new capabilities:

1. **The replay engine exists.** `process_actions` (`proof_checker.rs`) walks a
   rule's head actions under a substitution and produces the propositions the
   rule concludes; `check_rule_produces_equality` already verifies a claimed
   conclusion that way, without consulting the skeleton.
2. **Primitives are recomputed, not stored.** The checker evaluates a body
   primitive through `prim.validator()`.
3. **Programs where that would fail are already rejected.**
   `expr_primitives_have_validators` (`proof_encoding_helpers.rs`) is part of
   the proof-support gate, so every primitive reaching the encoder is
   recomputable from a substitution.

Precedent: `MergeFnIdx` / `MergeFnRow` are already term-free justifications
whose conclusions are reconstructed at conversion time (`run_merge_subexpr`).
This rework generalizes that from merge bodies to rule bodies.

## Design

* **Rule proof:** `RuleN(body premises, those premises extended with the
  interned subterms' view proofs, conclusion site + role)`. Homogeneous `Proof`
  columns only, and the two lists share cells so recording both costs no rows.
  The subterm view proofs are **not optional** — see the canonicalization bridge
  below: a head that interns a subterm into an existing e-class needs that
  e-class's row proof, which is neither a site of the head nor one of its
  premises. They are already read at no row cost.
* **No `@Ast`.** Conclusions are derived, so terms need not be stored.
* **No per-rule constructors.** Typed columns were only needed to carry
  computed base values; those are derivable, so the constructor stays generic
  and no per-rule table is created.
* **Fiat** splits by where the value lives: a program-site index for anything
  written in source, an input-row index for `(input …)`-loaded facts.
* **Rebuilding:** `RebuildN(old_row_proof, e1 … ek)`, carrying the moved
  columns' `@UF` proofs as premises. Recording them as premises — rather than
  looking them up later — is what makes rebuilding reconstructible without
  historical union-find state.
* The UF rule keeps explicit `Trans` for now.

### Carrying the canonicalization bridge

A head interns each constructor application into its view. When `set-if-empty`
returns an **existing** e-class, that e-class's term row may spell a different
term than the head wrote; the proof they are equal came from some other rule's
firing, so it is neither a site of this head nor one of its premises. Deleting
that chain without carrying it fails 28 of 206 tests with `transitivity requires
matching middle terms`.

The proofs needed are the interned subterms' view-row proofs, which the encoder
already reads as `view-proof-<View>` at no row cost. They become trailing
premises of `RuleN`; see the phase 2b result for how they are recorded and how a
read that found no row is told apart from a real bridge.

The lookups cannot be hoisted to the front of the action: an outer view's key is
built from its children's *deduped* ids (`fv_can = mint(func, dedup_args)`), so
interning is bottom-up and interleaved with construction. Only what is done with
the result changes.

### One canonical site enumeration

`proof_sites.rs` defines `SiteIndex`, `SiteConclusion` and `conclusion_sites`.
Both the encoder (assigning an index) and the reconstructor (resolving one)
must read it. The hazard to avoid is `subexpr_at_index`'s "must mirror the
indexing the proof encoder uses" — a contract held by a comment. Here it is
held by a test.

## Phases

Each phase is independently verifiable. The ordering principle is **validate
before deleting**: the reconstructor must be proven to agree while the old
skeleton is still present to compare against.

| Phase | Work | Gate |
| --- | --- | --- |
| 0 | one canonical `conclusion_sites`; `process_actions` returns site-indexed propositions | done — zero snapshot changes |
| 1 | reconstructor runs *beside* the skeleton, differentially asserted | done — see below |
| 2a | rule proof carries a conclusion-site index; the conclusion is derived from it instead of from the stored `Ast` columns | done — zero snapshot changes |
| 2b | stop emitting the RHS `Congr`/`Trans`/`Sym` skeleton; reconstruction synthesizes it | done — zero snapshot changes; see below |
| 3 | drop `@Ast` | ditto |
| 4 | rebuilding → `RebuildN` | ditto |
| 5 | re-enable CSE after encoding, repair term mode, re-measure | nothing left behind the switch |

### Sequenced plan from here

1. ~~**Index proof extraction.**~~ Done — see "Extraction rescanned every
   candidate table once per node" below. `eggcc_2mm_pass1` went from 201 s to
   32 s at unchanged peak RSS.
2. **Then decide about connectors, not before.** The cumulative bridge list
   costs no rows (the two lists share cells) but grows with nesting. Giving each
   build site its own connector row bounds it to `children + 1`, at one row per
   site — flat `rewrite` unchanged at 4, nested ~12 instead of 11. Step 1 is in
   and the fixture is no longer extraction-bound, so this is not urgent; measure
   before paying for it.
3. **Port the two collapses dropped when this branch was cut.** Both were
   implemented and verified on `reduce-proof-writes`.
   * ~~The reflexive `Sym`/`Trans` collapse (`0b79259`, `6dd5366`, `fc1aada`).~~
     Done — see "The encoder applies the reflexive identities itself" below. A
     flat `rewrite` firing went from 6 proof rows to 4, a nested one from 13 to
     11, with zero snapshot changes.
   * Fused `Rule0..Rule4` carrying premises inline (`b347bb5`, removes `PNil` +
     `PCons`), taking a `rewrite` firing from 4 rows to 2. The fused arity must
     also cover the bridges, which is the same change as step 2 — decide them
     together.
4. **Phase 3, `@Ast`.** Narrower than first scoped: merge bodies already mint
   none, and top-level actions need a program-site index first.
5. **Phases 4 and 5.** `RebuildN`; then re-enable CSE after encoding, repair
   term mode, re-measure.

Row budget for `(rewrite (Add a b) (Add b a))`: 13 at the branch point, 6 today
(4 proof + 2 `@Ast`), 2 if all of the above lands.

**Open question, unresolved.** Nobody has traced how the bridge list reaches
~2000 cells on `eggcc_2mm_pass1`. A single head's list is bounded by its own
nesting, since the interned subterms are statically known — so either those
generated heads are far deeper than expected, or the depth accumulates across
chained firings. It matters: if it is cross-firing, bounding the per-head list
buys much less than step 2 assumes.

### Why phase 2 is split

Adding the index and deleting the emission are separable, and each fails
differently. 2a proves the encoder and the reconstructor agree on *which* site
a proof came from, while the old conclusion is still there to disagree with.
Only then does 2b remove the skeleton, so a failure there is unambiguously
about synthesis rather than about indexing.

Two hazards recorded from phase 0, both about assigning the index:

* The encoder emits **post-order** (`instrument_action_expr` builds children
  before the node) while sites are numbered **pre-order**, so it must look up
  the index of the node it is at rather than run a counter.
* `plan_construct_into` **drops `union` actions** it optimizes into a view row,
  so the site index must be captured before that pass runs.

And one from phase 1: 262 conclusions are the **reverse** of their site's
equality, so the emitted form needs either `Sym` of the site or a direction
bit. A bare index cannot name them.

### Phase 1 result

`proof_reconstruct_check.rs` replays every checked `Rule` node's head and
reports which conclusion sites reproduce the conclusion the proof records. It
runs under `EGGLOG_PROOF_RECONSTRUCT_CHECK=1` (logging one line per node at
`info`) and under the `rule_conclusions_reconstruct_without_carried_values`
test. Over the `proofs/` corpus, 13438 nodes:

| sites reproducing the conclusion | nodes |
| --- | --- |
| 1 | 12530 |
| 2 | 334 |
| 3 | 304 |
| 4 | 6 |
| 6 | 2 |
| 0, but one site's reverse | 262 |
| 0 in either direction | 0 |

Nothing is unreconstructible. The two shapes that are not one-to-one:

* **Reversed unions (262).** Every one is a `union` head whose proof records
  the equality the other way round. Confirms that the reverse direction must
  come out as `Sym` of a site — a site index alone cannot name it.
* **Several sites, same proposition (646).** In every case the conclusion is
  reflexive (`t = t`), concluded at several head positions — a repeated
  subexpression, or a `union` whose operands substitute to the same term. Any
  of those indices resolves to the same proposition, so the index disambiguates
  the *position*, not the meaning. No non-reflexive conclusion was ever
  ambiguous.

The same run rebuilds each substitution without reading any premise proof that
exists only to carry a value, recomputing those variables from the rule body
with `prim.validator()`. It agreed with the recorded substitution, variable for
variable, on all 13438 nodes.

The 13438 is that commit's count; the `set-if-empty` read-your-writes fix
(below) shares a duplicated subterm, so the same measurement over the corpus now
reaches 13248 nodes.

### Phase 2a result

`Rule` gains a fifth column, an `i64` holding `SiteRef::encode()` — the site
index and a direction bit packed as `2 * index + reversed`. Conversion decodes
it, replays the head under the substitution the premises determine, and takes
the proposition from that site, ignoring the `Ast` columns (still emitted,
removed in phase 3).

One packed column rather than an index plus a `Sym` wrapper, or an index plus a
separate direction column, because **a `union`'s direction is not known at
encoding time**: the `@UF` edge runs `ordering-max = ordering-min`, so which
operand is on the left depends on the ids the firing sees. The encoder emits
`(proof-of-max lhs <forward> rhs <reversed>)` — the existing orient primitive is
typed `(T, P, T, P) -> P` for any `P`, so it selects between two `i64`s by the
same value ordering `ordering-max` uses. A `Sym` wrapper would have changed the
emitted proof, which phase 2a must not do.

The three hazards:

* **Post-order emission.** `action_sites` returns the same numbering as
  `conclusion_sites` (one walk, two views of it) shaped like the head: per
  action, the site of its own conclusion plus an `ExprSites` tree per operand.
  The instrumenter carries the node's `ExprSites` down as it recurses, so it
  reads its index rather than counting.
* **`normalize_union_operands` and `plan_construct_into`.** Sites are computed
  on the head *as written*, before normalization, and each output action carries
  the `ActionSites` of the action it came from — lifting a union operand into a
  `let` shifts no index. `plan_construct_into` records the dropped union's site
  in the plan, oriented `target = guest` (reversed exactly when the guest is the
  union's lhs), which is the direction the guest's view row states it.
* **Reversed conclusions.** 558 of the emitted stamps are reversed: the 274
  where no site matches forwards, plus 284 where the reversed stamp lands on a
  site whose proposition is reflexive anyway.

`proof_reconstruct_check` now also reports whether the stamped site reproduces
the recorded conclusion. Over the `proofs/` corpus, 13392 nodes:

| stamped site | nodes |
| --- | --- |
| reproduces the conclusion, and is the only site that does | 12632 |
| reproduces it, alongside other sites | 760 |
| does not reproduce it | 0 |

13392 against the baseline's 13248: the site column is part of `RawProof`'s
hash-consing key, so two `Rule` nodes built at different head positions that
used to share a node now do not. All 144 extra nodes land in the
several-matching-sites bucket — they are the repeated-subexpression case phase 1
measured. Phase 3 will pull in the other direction: dropping the `Ast` columns
merges nodes that differ only there, and since same rule + same premises + same
site forces the same conclusion, that merge is sound.

### Phase 2b result

The head's `Congr`/`Trans`/`Sym` skeleton is gone from every rule head. What a
firing writes is one `Rule` row per proof it *stores* — a term proof, a view row,
a union-find edge — and proof conversion rebuilds the composition around it
(`proof_head_skeleton.rs`).

Three pieces make that work.

**A role on the site column.** A build site needs three propositions the head
does not conclude — the term as written, the same term over its children's
representatives, and the edge between them — so `SiteRef` gains a `SiteRole`
and `encode` packs `(index, direction, role)` into the one `i64` column. The
roles are `AsWritten` (the head's own conclusion, the only one phase 2a had),
`CanonicalReflexive`, `Connector`, `GuestView`, `GuestConnector`, `UnionEdge` and
`GlobalValue`. Conversion decodes the role and builds that role's composition;
the `Ast` columns are reused from the site's own conclusion, so a roled row costs
no extra AST rows.

**One shared lowering plan.** `HeadPlan` (union-operand normalization plus the
construct-into plan) moved out of the encoder into `proof_head_skeleton.rs`, and
`build_sites` derives from it, per site, the build sites of the site's children,
which union a guest is built into, and the order the head builds them. The
encoder and conversion both read it, so neither mirrors the other — the same
discipline as `conclusion_sites`.

**Bridge premises, and how "no bridge" is told apart.** `Rule` gains a second
`ProofList` column: the body premise list extended with the view-row proof of each
subterm the head interned, newest first. The two lists *share cells* — the
extension is consed onto the body list — so recording both costs no rows and
their length difference is exactly the bridge count. The discriminator the design
called for turned out not to need a distinguished sentinel: a row the head's own
`set-if-empty` seeded is absent when `view-proof` reads it, so the read returns
its fallback, a proof *about the term as written*. Only a proof whose rhs **is**
the canonical term states which e-class the canonical term was interned into, so
`bridge.rhs == canonical` is the test, and it is right whichever way the fallback
is chosen.

Two things were needed to keep this from dragging the whole proof in:

* Only a *roled* row records bridges. A term-proof anchor states the head's own
  conclusion, needs none, and keeps the bare body list.
* Conversion converts only the bridges the requested role is composed from
  (`sites_needed`). Converting the whole list made every row reach every subterm
  the firing happened to build.

Measured over the `proofs/` corpus: 206 tests pass with zero changed snapshots and
zero changed shared snapshots. `proof_reconstruct_check` reports 13392 nodes —
the same as phase 2a — with 0 `stamped_wrong` and 0 payload-free failures, and
counts 3540 canonicalization bridges of which 288 move the term. The bridge
counter now fires inside the synthesis rather than on an emitted `Congr` chain,
so it counts *applied* bridges rather than chain steps; the numbers are not
comparable with the 2082/240 phase 2b measured.

Rows written per rule firing, from `--proofs --mode desugar`:

| rule | proof rows | `@Ast` rows |
| --- | --- | --- |
| `(rewrite (Add a b) (Add b a))` | 9 -> 6 | 4 -> 2 |
| `(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))` | 22 -> 13 | 8 -> 6 |

The commute firing's six are the two the body premise needs (`Sym`, `Trans`), the
two-cell premise list (`PNil`, `PCons`), and the two `Rule` rows the head stores:
the natural node's term proof and the guest's view-row proof. That subsumes the
"Available now" 9->7 collapse for this shape — the rows that collapse there are
among the three deleted here — so it was not taken separately.

#### The proof got deep, so reading it stopped recursing

The bridge premises are a cons list, so on `egglog-experimental`'s
`eggcc-2mm-pass1` proof test the extracted proof term's depth went from a measured
maximum of **15** to over **2000**, and the fixture died of a stack overflow. The
depth is inherent to the cumulative list: resolving a build site needs every
bridge in its subtree, and the subtree's bridges are a front block of the list, so
the list cannot be shortened without losing them. Note the budget: a test runs on
a spawned thread, so the whole read is working inside 2 MiB, not the main thread's
8 MiB.

Fixed on the reading side, not in the encoding, so nothing a firing emits changes
and the row counts above stand. Both readers of the extracted term now drive
themselves from an explicit stack:

* `RootExtractor` (`proof_extractor.rs`) resolves one child at a time from a stack
  of frames, each recording which reconstruction its node is trying.
* `RawProofStore` parses the nested proofs of a term deepest first
  (`parse_nested_first`), so `parse_proof` finds each one already parsed;
  `parse_proof_list` also loops down the cons spine rather than recursing.

Measured with a per-routine stack probe on that fixture: parsing peaked at 2.3 MiB
before the change and, like `convert_raw_proof`, `simplify` and `check_proof`,
stays under 256 KiB after. The fixture passes again in 201 s (33 s before phase
2b; the extra time is the larger proof, not the fix), and the `egglog/tests`
corpus is unchanged at 206 passing in 9.4 s — still faster than the 13.2 s before
phase 2b.

Not needed, so not taken: recording each build site's **connector** as its own row
and having a parent name its children's connector rows instead of their bridges.
That bounds the list structurally but costs one row per build site, dropping the
saving from `k+5 -> 3` to `k+5 -> k+4`.

Still recursive, and unchanged here: `check_proof` descends per proof node, which
a synthetic chain of ~2000 rule firings overflows. That shape is nothing the
corpus or this fixture reaches — both leave it two orders of magnitude of headroom
— but it is the next thing to give.

#### Extraction rescanned every candidate table once per node

The 201 s above was not the cost of reading a bigger proof; it was the bigger
proof multiplied by a pre-existing rescan. `RootExtractor`'s `Stage::Eq` search
ran a full `for_each` over every candidate function's rows *per extracted node*
and sorted the matches, so extraction cost `O(nodes x rows)`. Phase 2b raised the
node count enough to make that term dominate.

Each candidate function is now read once per extraction run into `ScannedRows`:
its non-subsumed rows concatenated into one `Vec<Value>`, a permutation ordering
them by output value and then by whole row, and a map from output value to that
group's range in the permutation. The search takes rows from the group instead of
rescanning. A group is still in whole-row lexicographic order, so the row it picks
is the one the per-node sort picked; the `proofs/` snapshots are the oracle for
that, and none moved.

Measured `--release` on a 128-core box at load ~23, wall time of the test phase
and peak child RSS:

| | before | after |
| --- | --- | --- |
| `egglog-experimental --test files` (46 tests) | 200.4 s / 5.36 GB | 28.8-29.3 s / 4.29-5.17 GB |
| `proofs/eggcc_2mm_pass1_proof_testing` alone | 202.8 s / 3.26 GB | 31.6 s / 3.29 GB |
| `egglog --test files 'proofs/'` (206 tests) | 9.16 s / 6.06 GB | 8.96-9.22 s / 5.90-6.07 GB |

Read the whole-suite RSS as unchanged: it is the peak of whichever tests happen
to overlap, and the heavy one now finishes early. The single-fixture row is the
one to trust, and it moves under 1% — only functions the search actually consults
are read, and the index dies with the `RootExtractor`. The small corpus is
unchanged either way: its tables are too small for the rescan to have dominated.

### The encoder applies the reflexive identities itself

`simplify` rewrites `Sym(p) -> p` when `p` proves `t = t`, `Trans(refl, p) -> p`,
`Trans(p, refl) -> p` and `Congr(p, i, refl) -> p`, so a step composed onto a
reflexive proof was minted and then discarded. The encoder knows statically which
proofs are reflexive, so it applies those identities before minting and never
emits the node.

`ProofInstrumentor` carries a `reflexive` set of emitted proof-variable names —
`fresh_var` names are globally fresh, so entries never collide across generated
programs — and `mint_sym` / `mint_trans` / `mint_congr` consult it. Two things
enter the set: a body variable's `<S>Proof` read, and `term_proof_with_asts`'s
`Rule` / `Fiat` result, whose two AST endpoints both wrap the same value.
`edge_proof_with_asts` mints its endpoints over two *different* values, so its
rows stay out.

What collapses on a rule head is the body-premise composition. In proof normal
form a matched call appears as `(= var (call …))`, whose fact proof was
`Trans(Sym(var_proof), call_proof)` with `var_proof` the variable's reflexive
term proof; both nodes go. Every other rule-head site was already deleted by
phase 2b, which replaces the composition with a roled row. The remaining collapses
are on the paths phase 2b leaves alone — top-level actions and merge bodies.

Rows written per rule firing, from `--proofs --mode desugar`:

| rule | proof rows | `@Ast` rows |
| --- | --- | --- |
| `(rewrite (Add a b) (Add b a))` | 6 -> 4 | 2 |
| `(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))` | 13 -> 11 | 6 |

206 `proofs/` tests pass with zero changed snapshots and zero changed shared
snapshots, as predicted: the deleted nodes are exactly the ones `simplify` was
already removing, so the printed proof is byte-identical.
`proof_reconstruct_check` is unmoved too — 13392 nodes, 0 `stamped_wrong`, 0
payload-free failures, 3540 bridges of which 288 move the term.

Two sites still mint raw `Sym`/`Trans` that the set cannot help: `@UF` path
compression and `ordered_union_merge` compose runtime-bound proofs, and
`global_value_proof` builds `Trans(Sym c, c)`, which is reflexive but not by any
of the four identities. `add_constructor_with_proof`'s non-rule-head branch is
the one place a further collapse is available — see "Available now" below.

## Standing rules

* **No `proofs/` test may fail at any phase.** That corpus is the only oracle
  for "same user-facing proof format".
* **A phase may change how many proof nodes it mints without moving a
  snapshot.** `fresh_var` has its own `SymbolGen` hint, separate from the `"v"`
  that `proof_normal_form` gives rule-body variables — those names are printed
  in a proof's `substitution`, so a shared counter made every mint-count change
  rewrite unrelated proof output. Verified by doubling every temporary and
  observing zero snapshot changes. Keep them separate.
* **View row counts must not move.** The `print-size` output in
  `files__shared_snapshot_*.snap` is the e-graph itself; this rework touches
  only proof tables, so any change there is a bug, not churn to bless. Proof
  *node* counts may move — the hash-consing key changes as columns come and go —
  but a view count changing means the e-graph diverged. Across phases 0–2a,
  zero shared snapshots changed; keep it that way.
* **Term mode may break**, and is repaired in phase 5.
* Everything switched off for the rework hangs off `PROOF_REWORK_IN_PROGRESS`
  so the set is greppable from one place.

## Open questions

* ~~**Is `reflexive_fiat_proof`'s payload derivable?**~~ Answered by phase 1,
  for everything the corpus reaches. `bind-prim-result.egg`'s `res` recomputes
  to `"hello world"` through `prim.validator()`; a `(Vec i64)` and a
  `(Map String i64)` matched in a rule body and read (`vec-length`, `map-get`)
  recompute the same way. Still untested: `UnstableFn`, which no corpus rule
  binds.
* Which primitives lack a `validator()` — expected to be none that reach the
  encoder, given the support gate.

## Adjacent defect: non-eq containers built in a rule head

Pre-existing, unrelated to the rework, but it bounds the phase-1 answer above.
`(rule ((Seed v)) ((Built (vec-of v))))` for `(sort IVec (Vec i64))` passes
`file_supports_proofs` and then panics in the checker — `Fiat proof claims
10 = 10, which is not established by globals`, because `reflexive_value_term`
recognizes neither the container head nor a non-eq container as a value. The
same program with an eq-container builds fine. No corpus file does this, so it
is invisible today; a `(Vec i64)`/`(Map String i64)` *read* in a body is fine.

## Resolved: the `begin`-block / CSE defect

CSE runs *before* proof encoding and reshapes rule heads, so the encoder and
the proof checker would see different heads. Proof encoding should run early
enough that later passes need not know proofs exist, so CSE is off until it can
run on the encoded program instead.

Turning it off exposed a **read-your-writes bug in the bridge**, which CSE had
been masking since PR #35. `register_set_if_empty` looked its key up in the
*committed* table and, on a miss, *staged* an insert, so two calls with the same
key inside one action batch both missed and both inserted — minting two
e-classes for one term. Native `lookup_or_insert` reads through the batch's
predicted rows, so the treatments disagreed and the term encoding ran exactly
one iteration behind. `integer_math.egg` (`(run 4)`) showed it as `(Add 331)`
native versus `(Add 121)` term-encoded, because it never saturates and the lag
compounds. Minimal reproducer:

```
(datatype Math (Sub Math Math) (Const i64))
(rewrite (Sub a a) (Const 0))
(let $e (Sub (Const 2) (Const 2)))
(run 1)
(print-size Const)
```

Only duplicates *within one top-level action block* were affected: a duplicate
minted by a rule head is repaired by that same iteration's rebuild, since the
schedule runs before it rebuilds.

Fixed by routing `set-if-empty` through `TableAction::lookup_or_insert_vals`,
which uses `predict_val` as native already does. The fix is strictly stronger
than CSE — it dedups cases CSE's syntactic per-scope pass misses — so CSE is a
pure optimization again and phase 5 has no correctness work left, only
re-enabling it after encoding.

## Available now, independent of the phases

**Finish collapsing the skeleton the encoder knows is the identity.** Phase 2b
deletes these composites from rule heads outright and the smart constructors now
take two of the four everywhere else, so what is left applies only to
top-level actions (`Fiat`) and merge bodies. Whether `build_natural_with_congr`
emits a `Congr` chain at all is decided at encoding time — a child contributes a
step only if it has a `NatConn` connector — and with no chain, `nat_to_dedup`
*is* the natural node's reflexive term proof:

| emitted | with no chain | taken |
| --- | --- | --- |
| `can_prf = Trans (Sym chain) chain` | `nat_prf` (`fv_can` spells the same application) | no |
| `connector = Trans chain (Sym vprf)` | `Sym vprf` | no |
| `to_dedup = Trans edge chain` | `edge` | yes |
| `guest_conn = Trans chain (Sym view_proof)` | `Sym view_proof` | yes |

The two untaken rows are `add_constructor_with_proof`'s, which still mints
`Sym`/`Trans` directly; routing them through `mint_sym`/`mint_trans` is the whole
change. Top-level actions are also **not sited yet** rather than unsiteable: the
design gives them a program-site index, the same mechanism extended from rule
heads to top-level forms. Merge bodies (`MergeIdx`) need nothing — they already
mint no `@Ast` at all.

Three sites mint rows or reads nothing ever consumes:

* A body variable's `<S>Proof` read is emitted whether or not the fact that asked
  for it keeps the proof, so a `(= var (call …))` atom — the shape whose
  composition the reflexive collapse deletes — now leaves a dead
  `(let p (<S>Proof var))`. No row, but a lookup per match.
* `lookup_global` (`proof_encoding.rs`) mints 2 `Ast` + 1 `Fiat` + a wasted
  fresh id per firing, as fallback arguments to `set-if-empty` that a
  well-formed program never uses.
* The body-primitive branch of `instrument_fact` builds `arg_proofs` that only
  the *function* branch consumes, so every non-trivial argument of a body
  primitive mints 2 `Ast` + 1 `Fiat` that are unreachable.

## Deferred: the `check_shadowing` per-rule clone

`check_shadowing.rs` clones its whole name map once per rule
(`let mut inner = self.clone()`), so name-checking costs
`tables x (15us + 50ns x rules)` — an O(rules x tables) cross term paid once at
load. A rollback log removes it, and it is measurably worth ~12% of
proof-mode `luminal-llama` **on main**.

It is **not** worth taking on this branch yet: measured here it is ~1% slower
(8.03s vs 7.93s over three runs each, tight and non-overlapping). The likely
reason is that CSE is off, so the hoisted global tables that make the cross
term large are not being created. Revisit in phase 5 once CSE is back and the
table count returns to normal — and re-measure rather than trusting either
number.

## Measurement caveats

* **While CSE is off, bounded-schedule programs understate work done**, so a
  `(run N)` file is not comparable against main.
* `egglog/tests/files.rs` and `egglog-experimental/dd/tests/files.rs` write the
  same shared snapshot file with different metadata headers, so each rewrites
  the other's on every run.
* `INSTA_UPDATE=always` masks cross-treatment disagreement, because each suite
  simply rewrites the file. Only a clean re-run is meaningful.
