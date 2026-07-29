# Proof encoding rework: record minimal justifications

Working plan for the `proof-encoding-minimal` branch. The user-facing proof
format does not change; what changes is how much the e-graph stores to produce
it.

## Goal

A proof node records only *what justified* a fact — which rule fired, with
which premise proofs — and the connecting skeleton (`Congr` / `Trans` / `Sym`)
is **reconstructed during proof conversion** rather than materialized as rows
while rules run.

At the branch point a rule that builds a term and unions it wrote nine proof
rows per firing plus four `@Ast` rows. The target is one row.

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

* **Rule proof:** `Rule_k(body premises, conclusion site + role)` for a head's
  first sites, and `RuleLink(previous site's proof, one interned subterm's view
  proof, conclusion site + role)` for the later ones. Homogeneous `Proof` columns
  only, and every link is a row the head emits anyway, so nothing is written to
  carry the premises. The subterm view proofs are **not optional** — see the
  canonicalization bridge below: a head that interns a subterm into an existing
  e-class needs that e-class's row proof, which is neither a site of the head nor
  one of its premises. They are already read at no row cost.
* **No `@Ast`.** Conclusions are derived, so terms need not be stored.
* **No per-rule constructors.** Typed columns were only needed to carry
  computed base values; those are derivable, so the constructor stays generic
  and no per-rule table is created.
* **Fiat** splits by where the value lives: a program-site index for anything
  written in source, an input-row index for `(input …)`-loaded facts. The input
  case needs no new index kind — `lower_inputs` already turns each CSV row into
  an ordinary top-level action in the checker's program, and both readers walk
  the file identically, so row *k* is the *k*-th lowered site; `native_input`
  only needs the site offset of its own `(input …)` command. That takes it from
  2 `@Ast` + 1 `Fiat` per CSV row to one row, and it is the dominant `@Ast`
  population on CSV-heavy fixtures — invisible to `--mode desugar` counting,
  because `native_input` mints straight into the backend rather than through
  generated actions. It depends on the canonical-program decision, since
  `lower_inputs` runs before `remove_globals` and the encoder's site counter
  would live after it.
* **Rebuilding:** `Rebuild_k(old_row_proof, col_1, e_1, … col_k, e_k)`, carrying
  each canonicalized column's `@UF` proof as a premise beside the column it is
  about. Recording them as premises — rather than looking them up later — is
  what makes rebuilding reconstructible without historical union-find state.
* The UF rule keeps explicit `Trans` for now.

### Carrying the canonicalization bridge

A head interns each constructor application into its view. When `set-if-empty`
returns an **existing** e-class, that e-class's term row may spell a different
term than the head wrote; the proof they are equal came from some other rule's
firing, so it is neither a site of this head nor one of its premises. Deleting
that chain without carrying it fails 28 of 206 tests with `transitivity requires
matching middle terms`.

The proofs needed are the interned subterms' view-row proofs, which the encoder
already reads as `view-proof-<View>` at no row cost. Each becomes the bridge
column of a `RuleLink`; see the phase 2b result for how a read that found no row
is told apart from a real bridge.

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
| 3a | drop the rule proofs' two `Ast` columns | done — zero snapshot changes; see below |
| 3b | the rest of `@Ast`: site the top-level actions, per-base-sort `Fiat`, delete the `Ast` sort | ditto |
| 4a | the `Rebuild` raw-proof variant and its expansion, nothing emitted | done — zero snapshot changes; see below |
| 4b | rebuilding → `RebuildN`: emit it from the rebuild rules | done — zero snapshot changes; see below |
| 4c | fold the e-class `Sym`/`Trans` pair into the packed row | done — zero snapshot changes; see below |
| 5 | re-enable CSE after encoding, repair term mode, re-measure | nothing left behind the switch |

### Premises inline on the first site, chained after that

Done — `ProofList`, `PNil` and `PCons` are gone from the encoding entirely.

A head emits one rule proof row per conclusion site, and every site shares the
same body premises — only the bridges differ, and they accumulate (0, 1, 2 across
the three sites of a nested `rewrite`). So a fused arity is not one `N` per rule,
nor one per site:

* **A row needing no bridge** carries the premises inline as columns:
  `Rule_k(name, p1 … pk, site)`. `k` is the body-fact count.
* **A row needing bridges** is `RuleLink(name, prev, bridge, site)`,
  naming a row of the same head that already carries the premises and every
  earlier bridge. A head mints the row at level `i` just before recording the
  bridge that opens level `i+1` (`can_prf` then `record_bridge`, both in
  `add_constructor_with_proof`), so the link is always a row it was emitting
  anyway — verified by probe over the whole corpus and `egglog-experimental`: the
  chain never has a gap to fill.

Conversion tells premises from bridges structurally rather than by length
arithmetic: `rule_columns` walks the chain, each link contributing one bridge and
the row ending it every premise — with a loop, since a chain is as long as the
head has bridge-recording sites.

**Arity family, uncapped.** `Rule_k` is declared per premise count the program
actually uses, ahead of the program's own commands (`rule_arity_header`), so no
list fallback is needed and a wide rule does not pay for one. Measured premise
counts: over `egglog/tests` the arities used are 0–11, over
`egglog-experimental` 0–23, at most ~17 distinct per program — so the family
costs a handful of empty relations, while a cap of 4 would have cost the
23-premise rule 21 extra rows per firing. The names are derived from one fresh
prefix (`{prefix}_{k}`) rather than generated per arity, because the `desugar`
treatment re-parses a printed program with a fresh `EGraph` that never encoded
the rules and so must recover the same names.

Two constraints the inline row inherits:

* A body variable's premise proof is a deferred `<S>Proof` read (see below),
  emitted by `mint` when a row first names it. Inlining moves that first read to a
  head row, so the inline row goes through `mint` and `drop_pending_lookups` moved
  out of `instrument_facts` to each caller's end — after the head is
  instrumented, for a rule. Get it wrong and the head names an unbound variable,
  which fails at rule creation.
* The proof list used to be minted into `action_lookups`, which made
  `action_lookups` non-empty for every proof-mode rule and so decided
  `:unsafe-seminaive`. With no list, that flag reads `proofs_enabled` directly —
  a proof-mode head reads the database regardless.

Rows written per rule firing, from `--proofs --mode desugar`:

| rule | proof rows | `@Ast` rows |
| --- | --- | --- |
| `(rewrite (Add a b) (Add b a))` | 4 -> 2 | 2 |
| `(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))` | 11 -> 7 | 6 |

The commute firing's two are the whole head: the built term's proof and the
guest's view-row proof, both `Rule_1` over the one body premise. The nested
firing's seven are the body premise's `Congr`, four inline rows and two links.

206 `proofs/` tests pass with zero changed snapshots and zero changed shared
snapshots. `proof_reconstruct_check` is unmoved: 13392 nodes, 0 `stamped_wrong`,
0 payload-free failures, 3540 bridges of which 288 move the term. The node count
holding is the point — the hash-consing key is rebuilt from a different row
shape, and it hash-conses to exactly the same set.

One snapshot did move, in *term* mode: `doc_example_add_function1` renumbers its
`__pv` temporaries by one, because `instrument_rule` no longer burns a
`fresh_var` naming the proof list. Nothing else in it changes.

### Sequenced plan from here

1. ~~**Index proof extraction.**~~ Done — see "Extraction rescanned every
   candidate table once per node" below. `eggcc_2mm_pass1` went from 201 s to
   32 s at unchanged peak RSS.
2. ~~**Then decide about connectors, not before.**~~ Moot. The cumulative bridge
   *list* is gone: each later site names the previous site's row plus its own one
   bridge, so nesting adds no cells to bound and per-site connector rows would buy
   nothing.
3. **Port the two collapses dropped when this branch was cut.** Both were
   implemented and verified on `reduce-proof-writes`, and both are now in.
   * ~~The reflexive `Sym`/`Trans` collapse (`0b79259`, `6dd5366`, `fc1aada`).~~
     Done — see "The encoder applies the reflexive identities itself" below. A
     flat `rewrite` firing went from 6 proof rows to 4, a nested one from 13 to
     11, with zero snapshot changes.
   * ~~Fused rule constructors carrying premises inline (`b347bb5`).~~ Done — see
     "Premises inline on the first site, chained after that". Uncapped rather than
     `Rule0..Rule4`, and the bridges chain instead of joining the fused arity, so
     step 2 folded into it. Flat `rewrite` 4 rows -> 2, nested 11 -> 7.
4. **Phase 3, `@Ast`.** Narrower than first scoped: merge bodies already mint
   none, and top-level actions need a program-site index first. Split at the
   point where a canonical-program decision becomes necessary:
   * ~~**3a, the rule proofs' `Ast` columns.**~~ Done — see "Phase 3a result".
   * **3b, everything else.** Siting the top-level actions, a per-base-sort
     `Fiat`, and then deleting the `Ast` sort. All three wait on the
     canonical-program decision the `Fiat`/`lower_inputs` note above describes.
5. **Phases 4 and 5.** ~~`RebuildN`~~ — 4a, 4b and 4c are all in; a rebuild
   firing writes one row. What is left is phase 5: re-enable CSE after encoding,
   repair term mode, re-measure.

Row budget for `(rewrite (Add a b) (Add b a))`: 13 at the branch point, 2 today
(2 proof + 0 `@Ast`).

**Answered: how the bridge list got so long.** Within one firing, not across
firings. Probing `head_chain` at the end of every head: over `egglog/tests` the
largest head records **71** bridges, and over `egglog-experimental` one generated
head — a `(rule () …)` with an empty body — records **3350**. Those heads really
are that deep.

So the chain does not make the extracted proof shallower: that head chains 3350
links, the same order as the cons spine it replaces, and reading it still relies
on the explicit-stack parse from phase 2b. What it removes is the *rows*: 3351
`PNil`/`PCons` writes per firing become zero, since every link is a `Rule` row the
head was emitting anyway.

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
measured. (This section also predicted phase 3 would pull the count back down by
merging nodes that differ only in their `Ast` columns. It did not — the count is
unmoved; see "Phase 3a result".)

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
is chosen. (The two-list carrier is superseded — see "Premises inline on the
first site, chained after that" — but the discriminator is unchanged.)

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
of the four identities.

`add_constructor_with_proof` mints through the smart constructors as well, so its
`can_prf = Trans (Sym chain) chain` and `connector = Trans chain (Sym vprf)`
collapse to `chain` and `Sym vprf` whenever the `Congr` chain is empty — 3 rows
per such build. Only the non-rule-head paths reach it (a rule head takes the
roled branch instead), so the two `rewrite` fixtures are unchanged at 4 and 11
proof rows; a top-level `(let x (Add (Num 1) (Num 2)))` goes from 19 to 13.

A body variable's `<S>Proof` read is deferred until a minted row reads it. Since
the read is reflexive, the composition that asked for it often collapses, and the
lookup then costs nothing rather than one dead table read per match: over
`egglog/tests`, `--proofs --mode desugar` emits 3157 reads where it used to emit
4995, of which 1838 had no consumer.

### Phase 3a result

The two `Ast` columns are gone from `Rule_k` and from `RuleLink`. A rule proof row
is now `Rule_k(name, p1 … pk, site)` / `RuleLink(name, prev, bridge, site)`, and a
rule head mints **no `@Ast` rows at all**.

Conversion-neutral by inspection rather than by validation: since phase 2b the
conclusion has come from site + role + bridges, and `convert_raw_proof` bound the
two columns to `_lhs`/`_rhs` and never read them. `Fiat` is untouched and is now
the only reader of an `Ast`, via `unwrap_ast`.

Rows written per rule firing, from `--proofs --mode desugar`:

| rule | proof rows | `@Ast` rows |
| --- | --- | --- |
| `(rewrite (Add a b) (Add b a))` | 2 | 2 -> 0 |
| `(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))` | 7 | 6 -> 0 |

206 `proofs/` tests pass with zero changed snapshots and zero changed shared
snapshots.

**The predicted node-count fall did not happen.** `proof_reconstruct_check` is
unmoved: 13392 nodes, 0 `stamped_ok=false`, 0 `payload_free=disagrees`, 3540
bridges of which 288 move the term. Two reasons, one verified and one inferred:

* The harness counts *converted* nodes, and `push_shared_proof` keys a rule proof
  on `SynthKey::Rule(name, site, premises)` — no AST component — so the columns
  never distinguished a converted node.
* They did not distinguish a *raw* node either. The AST endpoints were a function
  of `(name, premises, site)`: the premises fix the substitution (the payload-free
  replay agrees on all 13392 nodes), the substitution fixes every natural node the
  head builds, a natural node is never interned so its extracted term is unique,
  and a roled row reuses its site's own endpoints. Two raw rows agreeing on the
  remaining columns therefore always agreed on the ASTs, so dropping them merges
  nothing. Not separately instrumented — the raw store size was not measured.

The trailing-column hazard is handled by shrinking the read, not reordering:
`rule_columns` now returns the site alongside the premises and bridges, reading it
at the index each shape's own arity assertion fixes (`args[arity + 1]` /
`args[3]`). `parse_proof_inner` no longer slices from the end of a row whose width
depends on the arity.

What 3b still has to answer, none of it started here: top-level actions are not
sited, so `Fiat` remains the encoding for anything written in source; `Fiat` is
`(Ast Ast Proof)`, so the `Ast` sort cannot be deleted until it is replaced by a
per-base-sort form; and both depend on the canonical-program decision, since the
encoder's site counter would have to live after `remove_globals` while
`lower_inputs` runs before it.

### A body `Fiat` is deferred, like the `<S>Proof` read beside it

The reflexive `Fiat` a body fact mints for a literal, a base-sort variable or a
base-output primitive result was minted eagerly and then thrown away by the
`mint_*` constructor that asked for it — the proof is reflexive, so `Trans` /
`Congr` drop the step and no row is left naming it.

`pending_lookups` already solved this shape for the `<S>Proof` reads, holding one
statement per proof; it now holds a **statement list**, so the whole triple (two
`@Ast` mints plus the `Fiat`) is deferred as one block. `mint` stays the single
chokepoint: it flushes the groups named by the whitespace-separated tokens of the
row it is about to write, so a binding is still emitted strictly before its first
reader, and `drop_pending_lookups` at the end of each caller discards whatever
reached no row. The value a deferred group wraps is bound by the query, so the
group is free to move to wherever that first reader is — including into the head's
own actions when the reader is a rule proof row carrying the premise inline.

Over `egglog/tests`, `--proofs --mode desugar` emits **245** `Fiat` triples inside
rule heads where it used to emit **476**: 231 of them, 49%, reached no row.
Corpus-wide (rule heads and top-level actions together) 2133 `Fiat` rows become
1823 and 4266 `@Ast` rows become 3646 — the 231 plus the 79 below. No `Fiat` row
that any statement fails to name is left.

Rows written per rule firing, from `--proofs --mode desugar`:

| rule | proof rows | `@Ast` rows |
| --- | --- | --- |
| `(rewrite (Add a b) (Add b a))` | 2 | 0 |
| `r1` of `tests/proofs/bind-prim-result.egg` | 4 -> 3 | 4 -> 2 |

The plain `rewrite` is byte-identical: its one body premise is an eq-sort
variable, whose `term_proof` read was already deferred. `r1`'s body is
`(Strings a b)` and `(= res (+ a " " b))`; the second fact fiats both operands and
then `Trans (Sym lhs) rhs` keeps only the primitive result's, so the `res` triple
was pure waste. The surviving triple is the premise the two `Rule_2` rows carry.

`lookup_global` handed `set-if-empty` a freshly minted `Fiat` triple as the
fallback proof it never uses. The signature still needs the fallback pair, so both
halves are now bare `get-fresh!` ids with no row about them: 3 rows + 3 ids per
occurrence become 0 rows + 2 ids, 79 triples over the corpus. A header-minted
shared constant was considered and dropped — reading one costs a table lookup per
occurrence where `get-fresh!` is a counter bump, and sharing an e-class would
alias two globals on exactly the malformed program the fallback exists for.
Every one of the 79 is in a top-level action, not a rule head: `remove_globals`
hoists a rule's global references into body facts, so `lookup_global` is only
reached from actions written at top level.

206 `proofs/` tests pass with zero changed snapshots and zero changed shared
snapshots — a proof no row names cannot appear in an extracted proof, so this is
neutral by construction. `proof_reconstruct_check` is unmoved: 13392 nodes, 0
`stamped_ok=false`, 0 payload-free failures, 3540 bridges of which 288 move the
term.

### The skeleton composites are deferred too

`mint_sym` / `mint_trans` / `mint_congr` register a deferred group instead of
emitting; nothing composed onto a proof no statement reads is written. Over
`egglog/tests`, `--proofs --mode desugar` goes from **13258** composite
`Congr`/`Sym`/`Trans` rows to **12516**, and no unread one is left:

| where | before | after |
| --- | --- | --- |
| top-level action blocks | 7823 | 7277 |
| merge blocks | 2912 | 2898 |
| rule heads | 1980 | 1949 |
| `(panic …)` rule heads | 151 | 0 |
| generated rebuild / `@UF` rules | 392 | 392 |

**Only the three composites defer.** Every other `mint` writes a row that is
load-bearing on its own — a term relation row, a `Rule_k` / `RuleLink` /
`Rebuild` / `MergeIdx` / `Fiat` the encoding stores and reads back — so
deferring it would only postpone a row that is always taken. The composites are
the only ones whose sole product is a proof id for a *reader* to name.

**A group does not have to be self-contained.** `defer_lookup` takes the
variables the group reads, and a flush emits those groups first, so groups
reference each other and each is emitted once, wherever it is first read. That
is what lets a `Congr` chain defer as a chain rather than as one nested block:
nesting breaks as soon as an operand is named twice, because the second naming
would reference a binding buried inside a group that may itself be dropped.

**Five statements read a proof without minting a row**, and each flushes
explicitly: `union`'s `proof-of-max`/`proof-of-min` pair and its `@UF` row,
`instrument_construct_into`'s view row, `ordered_union_merge`'s `@UF` row,
`add_constructor_with_proof`'s `can_prf` (term proof + `set-if-empty` +
`view-proof`), and the element `@UF` row a container-building primitive writes.
Three others take only eager mints and need nothing: `update_fd_view` (every
caller passes a `mint` result), the natural term proof, and
`anchor_container_term_proof`. Missing one is loud rather than silent — the
container `@UF` row was missed first time round and failed 12 tests with
`Unbound symbol @pv125`.

`drop_pending_lookups` grew from three call sites to five: a top-level action
block and a custom function's merge body each build a term whose connector
nothing goes on to compose with.

**Fresh-name numbering does not move at all.** `fresh_id` runs where the mint is
requested, not where it is emitted, so a dropped row leaves a gap rather than
renumbering: over `eggcc-2mm.egg`, 320 `@pv` names disappear from the desugared
program and not one of the remaining 38689 is renamed.

**Runtime rows, and what the static count does not tell you.** A `(panic …)`
head never fires, so all 151 of its rows were free at runtime — that column of
the table buys nothing but generated program text. The rows that were really
being written come from merge bodies (once per collision) and top-level blocks
(once). Over `eggcc-2mm.egg`, three runs each: `@Sym` 92830/92510/92641 ->
87059/87510/87612 (-5.7%), `@Trans` 91168/90697/90969 -> 85060/85723/85860
(-5.9%), `@Congr` unmoved, all tables together -0.32%. Its merge blocks lost
only 10 statements statically, which is where the ~10k rows come from. Over the
146 corpus files that run deterministically, `@Sym` 1836 -> 1655, `@Trans`
1345 -> 1253, `@Congr` unchanged.

`eggcc_2mm_pass1` is flat: 24.63/25.07/25.13 s -> 25.14/25.16/25.15 s. 0.3%
fewer rows is not a measurable time.

206 `proofs/` tests pass with zero changed snapshots and zero changed shared
snapshots, and the whole workspace plus `egglog-experimental --test files` is
green. `proof_reconstruct_check` is unmoved: 13392 nodes, 0 `stamped_ok=false`,
0 `payload_free=disagrees`, 3540 bridges of which 288 move the term.

**A deferred row is unreachable, not merely unread.** Proof tables are
`:internal-hidden :unextractable`, and every occurrence of the three composites
in the generated program is inside a `(set …)` — no rule body joins on one, so
the only way to a proof row is to follow a named id, and `RawProofStore` parses
only what the extracted proof term reaches.

### Phase 4a result

`RawProof::Rebuild { row, steps, eclass }` and its expansion are in; nothing
emits it yet, so no generated rule and no snapshot moved.

The variant is a *re-packing*, not a reconstruction. A rebuild rule already
records exactly the proof ids the composition needs — it just spreads them over
`m + 2` rows — so conversion is a purely local expansion of one raw node, with
no head replay, no substitution and no site machinery. That matters because a
generated rebuild rule is not in `proof_check_program` at all: anything
program-dependent, as the `Rule` arm is, would panic looking itself up.

Three things the shape settles:

* **Positions are explicit.** The eq-sort non-container columns are not
  `0..k-1`, and `steps` records `(column, proof)` so conversion never
  recomputes the schema. `expand_rebuild` asserts each step starts at the child
  it names, which is the same condition `check_proof`'s
  `CongruenceChildMismatch` enforces later.
* **The e-class is a field, not a term-matched step.** It composes on the lhs
  (`Trans(Sym(eclass), …)`), and it cannot be found by matching terms: an
  e-class can legitimately equal one of its own children's terms —
  `(rewrite (Add a Zero) a)` leaves the row `a = Add(a, Zero)` — so a search
  would rewrite the wrong thing.
* **Order is part of the contract.** The fold runs in ascending position, which
  is the order `indexed_rebuild_rule`'s chain composes in, and `expand_rebuild`
  asserts it. A `Congr` at a different nesting order proves the same
  proposition by a different tree, so a reordering would change the printed
  proof.

A reflexive step is folded like any other and dropped by `simplify`, exactly as
the emitted chain's reflexive `Congr` is today.

`proof_head_skeleton::trans` now asserts matching middle terms, as the
`RawProof::Trans` arm always has. It was the one composition point that could
build a malformed proposition silently and only fail later in `check_proof`.
It does not fire anywhere on the corpus.

The signal, since nothing exercises the variant end to end yet: three unit tests
in `proof_format.rs` build a `Rebuild` node and, beside it, the hand-written
`Congr`/`Sym`/`Trans` chain over the *same* premises, and require the converted
proofs to be the same tree after `simplify`. The expansion is deterministic and
local, so that is exact rather than statistical. Mutation-checked — vec index
instead of the recorded column trips the child assertion, a descending fold
diverges structurally, and composing the e-class on the rhs trips the new
middle-term assertion.

What 4b trips over when `indexed_rebuild_rule` starts emitting these:

* The constructor needs a name in `EncodingNames` and a declaration in
  `proof_header`, plus an arm in `parse_proof_inner` and a matching entry in
  `nested_proofs`.
* A row is not a flat proof list. Which columns a step is about, and whether
  there is an e-class step at all, are fixed when the rule is generated but
  unknown to a parser that sees only the head — so they have to be carried,
  either as literal columns beside the proofs or by making the head name the
  rebuilt-column set.
* The steps a firing writes must be exactly the columns whose `Congr` the chain
  mints, in ascending column order. Leaving out the reflexive ones is sound and
  saves nothing, since `simplify` already removes them.

### Phase 4b result

`indexed_rebuild_rule` emits the packed row. A firing writes one
`Rebuild_<k>(row, col, step, …)` instead of one `Congr` per canonicalized column,
and keeps the e-class's `Sym` + `Trans` pair (phase 4c folds that in).

**The columns ride as literals beside their proofs.** `Rebuild_<k>` is
`(Proof (i64 Proof)^k) -> Proof`: the row proof, then a column literal and a step
proof per step. Which column a step is about is a compile-time constant of the
generated rule, so a literal costs nothing at runtime, and the alternative — a
head naming the rebuilt-column *set* — would mint a constructor per distinct
column set rather than per arity. `rule_columns`-style structural discrimination
cannot work here: the steps are homogeneous, so nothing in the row's shape says
which column a proof is about.

Arity family, so the four `Rule_k` rules apply: `EncodingNames` holds one fresh
`rebuild_prefix` and `rebuild_proof(k)` derives `{prefix}_{k}` from it — a
per-arity `symbol_gen.fresh` would be unrecoverable in the `desugar` treatment's
fresh `EGraph`. Unlike a rule's premise count, a view's step count is not known
before the view's own rules are generated, so the declaration goes out with the
first rule that uses it rather than in a header pass. A step-free view (`Num`,
whose only child is an `i64`) emits no row at all rather than a `Rebuild_0` —
superseded by 4c, which gives such a view a `RebuildEq_0` when its output is an
e-class.

Rows written per firing of the `AddView` rebuild in
`(rewrite (Add a b) (Add b a))`, counted as table rows after a run that fires it
once — 51 tuples before, 50 after, `@Congr` 2 -> 0 and `@Rebuild_2` 0 -> 1:

| | before | after |
| --- | --- | --- |
| `AddView` rebuild (2 eq-sort children + e-class) | 4 | 3 |
| `NumView` rebuild (no eq-sort children) | 2 | 2 |

The generated action is now

```
(let c0_canon_ (@UF_Math_canon c0_ c0_))   (let pv14 (@UF_Math_canon_proof c0_ …))
(let c1_canon_ (@UF_Math_canon c1_ c1_))   (let pv16 (@UF_Math_canon_proof c1_ …))
(set (@Rebuild_2 pv12 0 pv14 1 pv16 pv17) ())
(let e2_canon_ (@UF_Math_canon e2_ e2_))   (let pv19 (@UF_Math_canon_proof e2_ …))
(set (@Sym pv19 pv20) ())  (set (@Trans pv20 pv17 pv21) ())
```

206 `proofs/` tests pass with zero changed snapshots and zero changed shared
snapshots, and the whole workspace is green. `proof_reconstruct_check` is
unmoved: 13392 nodes, 0 `stamped_ok=false`, 0 `payload_free=disagrees`, 3540
bridges of which 288 move the term. The corpus parses 1140 `Rebuild` nodes (238
one-step, 900 two-step, 2 three-step), so the byte-identical output is
agreement, not absence.

**`nested_proofs` does not yet fail on any fixture, and is in anyway.** Deleting
the entry leaves the corpus and `eggcc_2mm_pass1` green — today's rebuild chains
are short enough for `parse_proof_inner` to recurse through them. It is the one
hazard the snapshots cannot police, so it is held by
`a_deep_rebuild_chain_parses_without_a_deep_stack`: 50 000 chained rebuilds
parsed on a 512 KiB stack, which overflows without the entry.
`a_rebuild_rows_nested_proofs_are_its_row_and_its_steps` fails the same mutation
gracefully, naming the cause.

The literal columns *are* policed by the corpus: emitting `0` for every step
fails it with `rebuild step 0 does not start at that child of the row`.

What 4c trips over, folding the e-class step in:

* The e-class step is not a column, so it cannot join the `(i64, Proof)` pairs —
  it needs either its own arity dimension (`Rebuild_<k>` vs `RebuildEq_<k>`, two
  families off the one prefix) or a sentinel column that `parse_proof_inner`
  reads into the `eclass` field. `expand_rebuild` already takes it as a separate
  field, so only the spelling is open.
* It composes on the *left*, and its `Sym` is what makes the composition
  well-typed. `proof_head_skeleton::trans`'s middle-term assertion is the check
  that catches getting that backwards; phase 4a mutation-checked it.
* `output_is_eclass` decides at rule-generation time whether the pair exists, so
  the two shapes are distinguishable statically — the same fact that makes the
  column list a compile-time constant here.

### Phase 4c result

A view-rebuild firing writes **one** proof row. The e-class's `Sym` + `Trans`
pair is gone; its canonicalization step rides the packed row.

**A second arity family, not a sentinel column.** `RebuildEq_<k>` is
`(Proof (i64 Proof)^k Proof) -> Proof` — the plain shape with the e-class proof
appended — off its own `symbol_gen.fresh("RebuildEq")` in `EncodingNames::new`,
beside `Rebuild_<k>`'s. The sentinel alternative (column `-1` in the existing
family) was rejected on two counts: it overloads a channel that otherwise means
exactly "child position", so `parse_index`'s non-negative check would have to be
given up and the peel-before-the-fold ordering invariant held by a branch rather
than by the shape; and it buys nothing, because `output_is_eclass` is a
rule-generation-time fact, so the two shapes are statically distinguishable
anyway. It costs no extra declarations in practice — the family a view uses is
determined by its schema, so what used to be `Rebuild_<k>` declarations is now
mostly `RebuildEq_<k>` ones.

The two prefixes are safe to have one be a prefix of the other: the step count is
separated by `_`, and `RebuildEq`'s `Eq` stands exactly where that `_` would be,
so `rebuild_proof_shape` gets the same answer whichever it tries first.

**The row carries the raw step, not its `Sym`.** `expand_rebuild` composes
`Trans(Sym(eclass), fold)`, so the column holds the `@UF_<S>_canon_proof` result
as it stands. Handing it the `Sym`'d proof instead fails 62 of the 206 `proofs/`
tests on `transitivity requires matching middle terms` — the assertion phase 4a
added for exactly this.

Rows written per firing, on `(datatype Math (Num i64) (Add Math Math))` +
`(rewrite (Add a b) (Add b a))`:

| | 4a | 4b | 4c |
| --- | --- | --- | --- |
| `AddView` rebuild (2 eq-sort children + e-class) | 4 | 3 | 1 |
| `NumView` rebuild (no eq-sort children, e-class) | 2 | 2 | 1 |

A view with neither eq-sort children nor an e-class output still writes nothing.
The generated action is now

```
(let c0_canon_ (@UF_Math_canon c0_ c0_))   (let @pv27 (@UF_Math_canon_proof c0_ …))
(let c1_canon_ (@UF_Math_canon c1_ c1_))   (let @pv29 (@UF_Math_canon_proof c1_ …))
(let e2_canon_ (@UF_Math_canon e2_ e2_))   (let @pv31 (@UF_Math_canon_proof e2_ …))
(set (@RebuildEq_2 @pv25 0 @pv27 1 @pv29 @pv31 @pv32) ())
```

206 `proofs/` tests pass with zero changed snapshots and zero changed shared
snapshots, and the whole workspace is green. `proof_reconstruct_check` is
unmoved: 13392 nodes, 0 `stamped_ok=false`, 0 `payload_free=disagrees`, 3540
bridges of which 288 move the term.

**The new shape is exercised, so the byte-identical output is agreement.** The
corpus parses 1268 `Rebuild` nodes, 1264 of them carrying an e-class: 128
zero-step (4b wrote no row for these at all), 238 one-step, 896 two-step and 2
three-step, plus 4 two-step nodes with no e-class. The four are
`merge_during_rebuild`'s custom function, whose value column is an output rather
than an e-class and so keeps `fd_value_rebuild_rule` — the only fixture keeping
the plain `Rebuild_<k>` family alive.

**The corpus polices reading the column, but not nesting it.** Dropping the
e-class in `parse_proof_inner` fails 50 tests (48 on the middle-term assertion, 2
on `rebuild step 1 does not start at that child of the row`). Dropping it from
`nested_proofs` instead leaves all 206 green, exactly as 4b found for the row and
step entries — so the e-class field is covered by the same two unit tests, now
run over both shapes: `a_deep_rebuild_chain_parses_without_a_deep_stack` chains
50 000 links through the e-class field as well as through the row proof, and
overflows a 512 KiB stack without the entry.

The extracted proof term also got *shallower* per rebuild link, so nothing about
`check_proof`'s remaining recursion gets worse: a `Sym` + `Trans` pair over the
row proof is two levels, the packed row is one.

What the remaining work inherits:

* **Phase 5's CSE.** Re-enabled after encoding, CSE sees a rebuild rule head that
  is a run of `let`s and one wide `set`. There is nothing left in it to share, and
  the `get-fresh!` binding the row's id must stay per-firing — the packing has
  already taken what CSE could have found here.
* **The head-traversal refactor.** It does not reach the rebuild path.
  `expand_rebuild` is a local re-packing, not a head replay: a generated rebuild
  rule is not in `proof_check_program` at all, so there is no head to walk under
  `Option<bindings>`. It is now the *only* place the whole rebuild composition is
  written down, so it stays outside that unification rather than being folded in.
* **Phase 3b.** Untouched — a rebuild firing mints no `@Ast`, and `expand_rebuild`
  reads none.
* Anything enumerating the declared proof constructors now has two arity families
  to cover, keyed by `RebuildShape` rather than by a step count.

### The container rebuild anchor was minted twice

Two places built `Trans(Sym p, p)` over the same rebuild proof `p` and wrote it
to `<CSort>Proof(rebuilt)`: the `ContainerRebuildProof` primitive, and both
generated container rebuild rules (the container-child arm of `rebuilding_rules`
and `fd_container_value_rebuild_rule`). The rules bind `p` by calling the
primitive, so the primitive's row always landed first, and `<CSort>Proof` is
`:merge old` — the rules' row was always discarded.

Dropping the rules' copy saves 1 `Sym` + 1 `Trans` row per container-rebuild
firing. Dumping every table after the run: `container-set-collapse` goes 117
rows -> 109 over its four firings, `custom-container-output-rebuild` 78 -> 74
over its two, with every other table — `<CSort>Proof` included — unchanged, and
zero snapshot changes.

The primitive's copy is the one to keep: it recurses, so it anchors *nested*
rebuilt containers, which the rules never did. Deleting it instead (keeping the
rules') fails `container-reorder-proofs` and
`nested-container-dirty-propagation` on the missing inner anchor.

## Refactor to do before this lands

The diff has grown parallel structures that must agree: `proof_sites.rs`,
`proof_head_skeleton.rs`, `proof_reconstruct_check.rs`, the arity family. Every
phase has needed a written warning about which of them the next change would
drift from.

Collapse them into **one traversal of the head, parameterized by
`Option<bindings>`** (bindings being a proof per variable):

* **no bindings** — you are the encoder: emit `Rule_k` / `RuleLink` rows naming
  positions.
* **bindings present** — you are the reconstructor: build `Congr` / `Trans` /
  `Sym` directly.

The agreement stops being a contract and becomes the same code, and the replay
path becomes main's existing logic, so the conceptual delta against main shrinks
to "and if you have no bindings yet, emit a row instead". That should let
`proof_head_skeleton.rs`, the differential harness, and `conclusion_sites` as a
standalone enumeration all go away — positions fall out of the shared walk.

The detail to settle first: the two modes return different things (statement
text versus `TermId`s in a `TermDag`), so either the traversal is generic over a
sink or it returns an enum. Prototype on `build_natural_with_congr` before
converting everything.

## Bugs found, not yet fixed

* **`convert_raw_proof` silently truncates the premise list.** It zips the
  converted premises against a `reflex_mask` built from the *checker's* rule, and
  `zip` stops at the shorter side. For a rule with a global in its head the
  encoder emits one premise more than the checker's copy has body facts — because
  `remove_globals` hoists the global into a new body fact — and the extra one is
  silently dropped. It lands correctly only because `remove_globals` appends
  rather than splices. The comment above it claims "the checker rejects any count
  mismatch"; the checker cannot, because the zip destroys the evidence first. The
  dropped premise is converted before being discarded, so it is unverified work
  thrown away on every firing of such a rule. Not a soundness hole today (the
  checker recomputes the global from the program's own `let`), but it must not be
  relied on.
* **Rule-head site indices agree across the two programs for a real reason**,
  worth stating as a test rather than leaving as luck: `remove_globals` maps a
  head global `Var` to a fresh `Var`, and `push_expr_sites` gives every node a
  site including `Var`s, so the substitution is exactly site-preserving.
  Top-level actions have no such property — `Let` becomes `Function` + `Set`,
  adding a site and shifting every later index — which is why the canonical
  program decision cannot be skipped.

## Standing rules

* **No `proofs/` test may fail at any phase.** That corpus is the only oracle
  for "same user-facing proof format".
* **A phase may change how many proof nodes it mints without moving a
  snapshot.** `fresh_var` has its own `SymbolGen` hint, separate from the `"v"`
  that `proof_normal_form` gives rule-body variables — those names are printed
  in a proof's `substitution`, so a shared counter made every mint-count change
  rewrite unrelated proof output. Verified by doubling every temporary and
  observing zero snapshot changes. Keep them separate. A phase that stops
  *emitting* an already-requested mint does not even renumber the temporaries:
  `fresh_id` runs where the mint is asked for, so the dropped name leaves a gap.
* **View row counts must not move.** The `print-size` output in
  `files__shared_snapshot_*.snap` is the e-graph itself; this rework touches
  only proof tables, so any change there is a bug, not churn to bless. Proof
  *node* counts may move — the hash-consing key changes as columns come and go —
  but a view count changing means the e-graph diverged. Across phases 0–2a,
  zero shared snapshots changed; keep it that way.
* **Correctness is not lost at any phase.** Not "term mode may break and is
  repaired later" — every phase keeps the whole workspace green, term-encoding
  treatments included. That has held so far: the only thing behind
  `PROOF_REWORK_IN_PROGRESS` is the CSE prepass, and the one real term-mode
  divergence was fixed at its root (the `set-if-empty` read-your-writes bug)
  rather than suppressed. Phase 5 is "decide what to do about CSE", not "repair
  term mode".
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

**Site the top-level actions.** All four skeleton composites the encoder
statically knows are the identity now collapse before minting, on every path, so
what is left on the paths phase 2b leaves alone — top-level actions (`Fiat`) and
merge bodies — is the composites over a non-empty `Congr` chain, which are not
identities. Deleting those needs phase 2b's roled rows, and top-level actions are
**not sited yet** rather than unsiteable: the design gives them a program-site
index, the same mechanism extended from rule heads to top-level forms. Merge
bodies (`MergeIdx`) need nothing — they already mint no `@Ast` at all.

~~Two sites mint rows nothing ever consumes.~~ Both taken — see "A body `Fiat`
is deferred, like the `<S>Proof` read beside it". `lookup_global`'s dead
`set-if-empty` fallback is now a pair of bare fresh ids, and a body fact's
reflexive `Fiat` is deferred until a row names it, which covers the unreachable
`Fiat` an `arg_proofs` entry used to mint for a body primitive's argument.

~~**What is left at those sites is the `Congr`/`Sym`/`Trans` a body premise
composes over *view* proofs.**~~ Taken — see "The skeleton composites are
deferred too". Three claims made there were wrong: the count was 447 unnamed
(742 counting the chains behind them), not 322; a group *can* reference another
deferred group, so self-containment was not the obstacle; and the `(panic …)`
heads, which the count made look like the prize, cost nothing at runtime,
because a panic head never fires. The rows a firing actually wrote were in merge
bodies.

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

* **CSE being off makes the branch look *worse*, not better.** With the
  `set-if-empty` fix in, the treatments agree tuple-for-tuple, so a bounded
  `(run N)` does the same work either way. What differs is that the candidate
  interns a repeated subterm twice and dedups it, where the baseline's CSE
  builds it once — so every measured win is achieved carrying that handicap.
* `egglog/tests/files.rs` and `egglog-experimental/dd/tests/files.rs` write the
  same shared snapshot file with different metadata headers, so each rewrites
  the other's on every run.
* `INSTA_UPDATE=always` masks cross-treatment disagreement, because each suite
  simply rewrites the file. Only a clean re-run is meaningful.
* **Six corpus files do not reproduce their own row counts.** `eggcc-2mm`,
  `hardboiled_conv1d_32`, `integer_math`, `math-microbenchmark`,
  `math-microbenchmark-mini` and `web-demo/eqsolve` give different table sizes
  on two runs of the *same* binary — `math-microbenchmark`'s `@Sym` moves by
  ~3000 and `eggcc-2mm`'s `@SmallerView` by a couple of rows. They are also the
  six largest, so a single before/after pair over them shows swings in both
  directions that have nothing to do with the change. Compare a mean over
  repeated runs, or restrict to the other 146 files. The snapshots are not
  affected: what the tests assert is stable, only the internal table
  populations are not.

  The variance is confined to how many times a merge function runs, not to what
  the run computes. Over three runs of `math-microbenchmark.egg` under
  `--term-encoding --proofs`, `(print-size)` is byte-identical and every rule's
  `num matches` agrees exactly (1716352 in total); only the timing lines and the
  hash-ordered rule report differ. So the e-graph reaches the same fixed point by
  a different number of collisions, and a measurement keyed to user tables or to
  match counts is reproducible even on these six — it is the proof tables, one
  row per collision, that move. Diff the `(print-size)` block alone: a whole-output
  diff is dominated by timings and rule ordering and looks nondeterministic
  everywhere.
