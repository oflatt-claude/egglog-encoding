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
| 2 | switch rule proofs to `RuleN` + site index; delete RHS skeleton emission | printed proofs byte-identical |
| 3 | drop `@Ast` | ditto |
| 4 | rebuilding → `RebuildN` | ditto |
| 5 | re-enable CSE after encoding, repair term mode, re-measure | nothing left behind the switch |

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

## Known blocker: the `begin`-block / CSE defect

CSE runs *before* proof encoding and reshapes rule heads, so the encoder and
the proof checker see different heads and a site index assigned by one does not
resolve on the other. Proof encoding should run early enough that later passes
need not know proofs exist, so CSE moves after it; until then it is off.

Turning it off exposed a **pre-existing correctness bug**: with CSE disabled,
`integer_math.egg` (`(run 4)`) reaches `(Add 331)` natively and `(Add 121)`
under term encoding. `(run N)` is N iterations under either treatment, so the
counts must match. PR #35 (which merged the local `begin` block together with
the CSE prepass) records this in its own Correctness section — *"a naive block
without dedup regressed it; CSE fixes it"*. So CSE has been masking a defect in
the local-block change, not supplying something of its own.

This must be fixed in phase 5, because moving CSE after encoding removes the
masking. The cross-treatment check is suspended for `integer_math.egg` by name
in `tests/files.rs`; do not accept a snapshot recording the divergence.

## Available now, independent of the phases

Two sites mint rows nothing ever reads:

* `lookup_global` (`proof_encoding.rs`) mints 2 `Ast` + 1 `Fiat` + a wasted
  fresh id per firing, as fallback arguments to `set-if-empty` that a
  well-formed program never uses.
* The body-primitive branch of `instrument_fact` builds `arg_proofs` that only
  the *function* branch consumes, so every non-trivial argument of a body
  primitive mints 2 `Ast` + 1 `Fiat` that are unreachable.

## Measurement caveats

* **While CSE is off, bounded-schedule programs understate work done**, so a
  `(run N)` file is not comparable against main.
* `egglog/tests/files.rs` and `egglog-experimental/dd/tests/files.rs` write the
  same shared snapshot file with different metadata headers, so each rewrites
  the other's on every run.
* `INSTA_UPDATE=always` masks cross-treatment disagreement, because each suite
  simply rewrites the file. Only a clean re-run is meaningful.
