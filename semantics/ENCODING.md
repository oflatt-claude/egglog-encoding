# Encoding passes

## Agreed plan and scope

This is the working plan for PR #58. The implementation order is:

1. **Port completeness to the congruence pass.** Establish the execution invariants
   needed for source/target correspondence, retaining the current constructor-only
   source fragment (`Program.Fragment`). The paper's completeness theorem ends
   here. The compiled target uses functions, but extending the theorem to arbitrary
   source merge functions is deferred.
2. **Implement a sound source proof checker.** Check explicit propositions against
   the original program, initially in the constructor-only source fragment.
   `Fiat` must be justified by original globals; it cannot
   introduce an arbitrary constructor or discharge an unproved rule premise.
   Congruence must preserve evidence that the enclosing application exists. Prove
   that accepted certificates imply their source propositions, including existence.
3. **Add a separate provenance pass.** Instrument the congruence-compiled program
   like Datalog provenance, extended to function entries and merges. Record evidence
   for global entries, rule firings, and merge-derived entries. Rule-created terms
   must have rule evidence, and merge-created entries must retain the evidence for
   both inputs and the merge computation. Do not hide these cases behind `Fiat`.
4. **Lift certificates back to the original program.** Recognize generated rebuilding
   rules by their origin tags and UF operations by the generated table name.
   Translate their justifications into source reflexivity, symmetry, transitivity,
   and anchored congruence, as appropriate. View collisions also require a source
   justification. For source rules, recover premises by walking the original query
   in exactly the compiler's recursive order, unflattening nested applications with
   congruence. Both algorithms receive the original query; there is no saved
   flattening tree. Validate that all generated names and maintenance rules have
   disappeared from the resulting source justification.
5. **Validate the whole pipeline.** Check the *same lifted certificates* with both
   Lean and Rust checkers. Running Rust's own encoder on the same inputs is useful
   comparison evidence, but does not establish this interoperability. Include
   negative tests for invented globals, missing existence premises, malformed rule
   substitutions, and incorrect equality endpoints, alongside positive tests for
   nested queries, repeated applications, rebuilding, UF chains, and function
   merges. Run the complete Lean, Python, and Rust validation suites.

The two compiler passes have separate responsibilities: congruence compilation
encodes rebuilding, union find, and query flattening without proof annotations;
provenance records how its resulting entries were derived. Proof lifting is a third
algorithm that interprets that provenance against the original source program.
The congruence output must contain no built-in unions and must execute without
implicit congruence or other equality axioms. Structural identity and existence
tests remain available. Provenance and lifting need soundness and validation;
they do not need their own completeness theorem for the paper.

This refactor targets the Lean model and encoding. Existing Rust certificate
formats and the Rust checker provide the interoperability target; rewriting the
Rust parser or runtime is outside the agreed scope. Source syntax has no lets,
and function entries use full table atoms such as `(LowerBound expr bound)` in
queries and evaluation. Function entries are not nested term values or union
operands. The constructor-only theorem scope does not remove functions from the
target or from provenance.

Stop and discuss an actual design blocker rather than weakening a theorem,
accepting unjustified proof premises, or silently broadening the source fragment.
Update the status below as each obligation is discharged. Intermediate commits
and pushes to the PR are authorized, including before the proofs are complete.

## Current implementation

The Lean refactor separates congruence compilation, provenance instrumentation, and proof
lifting. The congruence pass is implemented in
[Congruence/Encode.lean](EgglogSemantics/Congruence/Encode.lean), provenance in
[Provenance/Encode.lean](EgglogSemantics/Provenance/Encode.lean), and lifting in
[Resugar/Lift.lean](EgglogSemantics/Resugar/Lift.lean).

## Congruence compilation

`Egglog.Congruence.encode : Program → Program` compiles constructor-source programs into
explicit tables:

| Table | Atom | Meaning |
| --- | --- | --- |
| `@UF` | `(@UF t parent)` | An explicit parent edge |
| `@fView` | `(@fView children… id)` | The id of a source constructor application |

Each table has one output column. Structural constructor terms serve as ids. Building
`f(cs…)` builds its children and writes `(@fView cs… (f cs…))`; it needs no table lookup,
temporary variable, proof term, or separate construction-history relation.

`min` is the only computation in the fragment: the smaller of two terms in the model's
structural order, egglog's `ordering-min`. A source union writes an edge from each of the
two ids to the smaller one; the edge from the smaller id to itself is not a union-find
edge. Both UF and view collisions keep the smaller output and write the same two edges.
Their merge specifications explicitly bind singleton parameters `old` and `new`. All output columns determine
whether a row changed, so no special identity-column setting is needed.

Maintenance rules compress paths, propagate changed output ids through views, and re-key
child columns. Rebuilding runs after each source action and run. Copies of the maintenance
rules join each source saturation ruleset, so rebuilding also happens between its rounds.

`Congruence.compile` returns commands with rule origins. Source rules are tagged with
their original command index; generated rules identify path compression, output
propagation, or the particular constructor child being re-keyed. Copies in another
ruleset retain the same tag. `tableRole` recognizes UF and source-constructor views.
These tags are for later resugaring and do not affect execution.

The output has no built-in `union` in commands, rule heads, or merge bodies. It also
needs no equality axioms from the target runtime. `Relational.exec` uses structural
identity and stored-value existence for matching and function-key collisions, and omits
implicit congruence rebuilding. `encode_relational` proves that this execution produces
exactly the same result as the general interpreter. Source equality is represented by
ordinary UF and view entries; target `(= x y)` is just an identity test with existence.

## Query traversal

Flattening visits conjuncts left to right. Within an application it recursively visits
children left to right, then emits the parent's view atom. Within equality it visits the
left expression, then the right, then emits equality of their resulting ids. Each
application occurrence gets one fresh variable, including repeated subexpressions.
Variable supplies are local to a rule; source names cannot use the generated `@` prefix.

For example, `(= (F (G x)) (H x))` becomes:

```text
(@GView x @v0)
(@FView @v0 @v1)
(@HView x @v2)
(= @v1 @v2)
```

Resugaring will receive the original query and repeat this traversal while consuming
premise proofs in order. No separate tree describing flattening is stored.

## Provenance instrumentation

`Provenance.encode` adds one proof output to each function. Proof constructors identify
the exact global command, rule action, or merge computation. Rule proofs carry the
substitution and ordered premises; merge proofs carry both input proofs. Their claims
are recovered by evaluating the original action or merge, without guessing endpoints.

Appending a proof output preserves the original merge parameter bindings. The pass
instruments actions and appends a result without renaming the original expressions; it
appends fresh `@prov:p0` and `@prov:p1` parameters for the two input proofs. The input
check requires distinct parameter names of the declared width and excludes the reserved
`@prov:` prefix, even for unused parameters. Scalar and tuple parameter spellings are
handled by the parser and emitter;
the [merge guide](MERGE.md#collisions-and-command-steps) gives the componentwise notation.

The pass accepts flat table queries and equality tests whose variables and existence
witnesses come from table premises. This covers the congruence compiler's output;
unanchored equality-only queries and constructor writes are outside its input
fragment. Function bodies and results may use `min` and
multiple output columns. Generated names use the reserved `@prov:` prefix.

Only original data columns determine merge conflicts. This also suppresses collisions
between distinct proofs of identical rows. A conflict records both inputs' proofs in
the result's proof, and body facts record the merge justification too. Proof metadata
therefore cannot trigger a data merge or cause an otherwise stable rule to accumulate
longer resident proofs.

Extraction decodes a proof constructor into a proof tree with explicit facts, then checks
it against the uninstrumented relational program, which has no `union`. Equality premises
use checked subterms of table facts as existence witnesses; no auxiliary existence
relation is needed. These are intermediate proofs, which lifting translates into source
proofs checked against the original program.

## Proof lifting

`Resugar.lift` checks a relational proof against the compiled program, then rebuilds it
recursively as a source proof tree. A view row `(@fView cs… id)` becomes the claim
`id = f(cs…)`, a UF row an equality, and a value its reflexivity. Global rows become
`fiat` nodes. Generated rules are recognized by their origin tags: path
compression is transitivity, output propagation symmetry and transitivity, and child
re-keying anchored congruence. A UF or view collision joins its two inputs the same way.
A source rule firing names the original command, restricts the substitution to the
original query's variables, and recovers its premises by walking the original query in
the compiler's order ([Resugar/Query.lean](EgglogSemantics/Resugar/Query.lean)),
consuming one flattened premise per application and equality and rebuilding nested
patterns with congruence. A subterm's existence comes from the derivation that introduced
it, never from a new `fiat`.

Each node is validated by `SourceProof.checkNode` as it is built, and the result is
checked again by `SourceProof.check`. `lift_sound` therefore inherits the source
checker's soundness: a lifted claim whose endpoints the source holds is a source
congruence.

`Resugar.Export` writes proofs as JSON certificates with the program as `.egg` source,
listing each tree's nodes in postorder with shared subtrees, and
[proof_certificate.rs](../egglog/src/proofs/proof_certificate.rs) replays them through
Rust egglog's proof checker. The fixtures in
[Resugar/Fixtures.lean](EgglogSemantics/Resugar/Fixtures.lean) pair lifted proofs with
hand-written proofs that both checkers must judge alike; their export is committed as
`egglog/tests/lean-certificates.json`, and `make lean-certificate-test` also exports and
checks the whole corpus.

## Proof status

The congruence pass has kernel-checked proofs for:

- Union-free output and equivalence with execution using structural identity only
  (`encode_unionFree`, `encode_relational`).
- Query flattening and matching in both directions (`sourceMatch_of_encodedQuery`,
  `encodedQuery_match_of_source`).
- Preservation of sound entries, descending UF edges, and the connection between
  retained entries and live rows through source actions, merges, and maintenance.
- Unique roots and normalized view readings at rebuilding fixed points
  (`Rebuilt.viewLeader`, `Rebuilt.viewsCover`).
- Source rule firings, aligned rounds, and saturation (`encodedRule_firing_reads`,
  `round_simulation`, `saturation_simulation`).
- Prelude initialization and global actions with interleaved merges and rebuilding
  (`prelude_state`, `global_cmd_simulation`).
- The executable reader and correspondence under explicit state invariants
  (`sameClassF_iff`, `Rebuilt.corresponds`).

**Step 1 is complete.** [Complete.lean](EgglogSemantics/Proofs/Congruence/Complete.lean) proves
`Egglog.Congruence.encode_corresponds`:

```lean
Cong src a b ↔ SameClass target.toDatabase a b
```

Its premises are `P.Fragment`, a source execution from empty, successful compiled
execution, and membership of both endpoints in the source. `encode_corresponds_relational`
gives the same theorem for execution using structural matching and table operations only.
Termination is not asserted.

**Step 2 is complete for the agreed constructor source fragment.**
[SourceProof/Soundness.lean](EgglogSemantics/Proofs/SourceProof/Soundness.lean) proves
`check_supported` and `check_sound` for the executable checker. Accepted claims have
source existence witnesses for every subterm. For endpoints held by the source,
acceptance implies its original `Cong` relation. The source state must be reached by
the original program, well formed, and saturated for every ruleset. No proof is accepted
by assuming an unproved intermediate term exists.

**Step 3 is implemented.** [Provenance/Soundness.lean](EgglogSemantics/Proofs/Provenance/Soundness.lean)
proves that every accepted relational fact exists in a well-formed, reached state
saturated for the original relational program's rules and merges. The corpus gate
checks data preservation and every retained function entry's extracted proof.

**Steps 4 and 5 are implemented.** [Resugar/Soundness.lean](EgglogSemantics/Proofs/Resugar/Soundness.lean)
proves `lift_sound` for lifted proofs. Every retained row of every in-domain corpus
program lifts to a proof the source checker accepts, and Rust egglog's checker accepts
the same proofs and rejects the same hand-written counterexamples
(`make lean-certificate-test`).

Source merge proofs are deferred: equality can produce another spelling of one
stored function row without establishing a second input to its merge body. The
[checker guide](CHECKER.md#source-merge-inputs) records the counterexample. This does not
affect the constructor-only completeness theorem or the relational provenance pass.

The source fragment is defined once, as `Program.Fragment`: constructor declarations, no
`min` and no generated source names, consistent arities, supported queries, scoped and
declared heads, and no literal unions. A query fact is an application, as in egglog's
syntax; a bare variable or literal fact is outside it. The completeness theorem assumes it
and the source proof checker accepts only programs in it. Arbitrary source merge functions
remain outside its scope.
See [Source.lean](EgglogSemantics/Source/Domain.lean) for the exact conditions.

## Validation

`make lean-check` builds the library, audits for proof holes, and runs the corpus gates.
The congruence gate compares every pair of held source terms against the compiled
program's reading, and checks that execution with and without equality reasoning agrees.
The provenance gate checks data preservation
and every retained row's extracted proof. The resugar gate lifts those proofs and checks
them against the original source program, and the certificate gate exports the same
proofs and checks them with Rust egglog. Failures, stuck executions, and
insufficient fuel fail the command. Out-of-domain cases are counted separately.

The corpus is the curated and generated programs in `DiffTest.lean` together with the
hand-written `.egg` programs under [`tests/`](tests), which `Program.ofEgg` parses. The
egg gate (`difftest egg`) checks each of those against its committed snapshots: the
congruence encoding in `<name>.congruence.egg`, the provenance encoding in
`<name>.provenance.egg`, and the lifted source proofs in `<name>.proofs.txt`.
`make lean-update-egg-snapshots` rewrites them after an intended change. A program that
unions a term with its own subterm does not saturate in the model, whose classes are sets
of explicit spellings, so the hand-written programs evaluate into separate constructors
instead.

From `semantics/`:

```sh
lake build difftest
.lake/build/bin/difftest congruence 64
.lake/build/bin/difftest congruence 64 both-2 rand-43 sat-hit
.lake/build/bin/difftest provenance 64
.lake/build/bin/difftest resugar 64
.lake/build/bin/difftest egg 64
.lake/build/bin/difftest export-certificates 64 /tmp/certificates.json
```

Executable regressions also check recursive traversal order, origin tags, rebuilding
necessity, and rejection of a rule firing whose constructor premise never existed.
