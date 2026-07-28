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

* **Rule proof:** `RuleN(p1 … pN)` plus a conclusion-site index. Homogeneous
  `Proof` columns only.
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
| 2b | stop emitting the RHS `Congr`/`Trans`/`Sym` skeleton; reconstruction synthesizes it | zero snapshot changes |
| 3 | drop `@Ast` | ditto |
| 4 | rebuilding → `RebuildN` | ditto |
| 5 | re-enable CSE after encoding, repair term mode, re-measure | nothing left behind the switch |

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

## Standing rules

* **No `proofs/` test may fail at any phase.** That corpus is the only oracle
  for "same user-facing proof format".
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

Two sites mint rows nothing ever reads:

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
