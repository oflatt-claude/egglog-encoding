# Encoding passes

## Agreed plan and scope

This is the working plan for PR #58. The implementation order is:

1. **Port completeness to the congruence pass.** Establish the execution invariants
   needed for source/target correspondence, retaining the current constructor-only
   source fragment (`Program.EncodeDomain`). The paper's completeness theorem ends
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
[Resugar/Lift.lean](EgglogSemantics/Resugar/Lift.lean). The old combined encoder remains
as a comparison reference; its proof annotations have known correctness defects.

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

A source union writes an edge from the larger structural id to the smaller one. Both UF
and view collisions keep the smaller output and write the displaced id's parent edge.
Their merge bodies use ordinary `old` and `new` bindings. All output columns determine
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

The pass accepts flat table queries and equality tests whose variables and existence
witnesses come from table premises. This covers the congruence compiler's output;
unanchored equality-only queries, constructor writes, and `:no-merge` declarations
are outside its input fragment. Function bodies and results may use primitives and
multiple output columns. Generated names use the reserved `@prov:` prefix.

Only original data columns determine merge conflicts. This also suppresses collisions
between distinct proofs of identical rows. If a merge result equals an input's data,
it retains that input's proof; a new result records both inputs. Body facts always
record the merge justification. Proof metadata therefore cannot trigger a data merge
or cause an otherwise stable rule to accumulate longer resident proofs.

Extraction produces a shared certificate with explicit facts, then checks it against
the uninstrumented relational program. Equality premises use checked subterms of table
facts as existence witnesses; no auxiliary existence relation is needed. These are
intermediate certificates, which lifting translates into source proofs.

## Proof lifting

`Resugar.lift` checks a relational certificate against the compiled program, then
rebuilds it node by node as a source certificate. A view row `(@fView cs… id)` becomes
the claim `id = f(cs…)`, a UF row an equality, and a value its reflexivity. Global rows
become `fiat` nodes. Generated rules are recognized by their origin tags: path
compression is transitivity, output propagation symmetry and transitivity, and child
re-keying anchored congruence. A UF or view collision joins its two inputs the same way.
A source rule firing names the original command, restricts the substitution to the
original query's variables, and recovers its premises by walking the original query in
the compiler's order ([Resugar/Query.lean](EgglogSemantics/Resugar/Query.lean)),
consuming one flattened premise per application and equality and rebuilding nested
patterns with congruence. A subterm's existence comes from the derivation that introduced
it, never from a new `fiat`.

Each node is validated by `SourceProof.checkNode` as it is added, and the result is
checked again by `SourceProof.check`. `lift_sound` therefore inherits the source
checker's soundness: a lifted claim whose endpoints the source holds is a source
congruence.

`Resugar.Export` writes certificates as JSON with the program as `.egg` source, and
[proof_certificate.rs](../egglog/src/proofs/proof_certificate.rs) replays them through
Rust egglog's proof checker. The fixtures in
[Resugar/Fixtures.lean](EgglogSemantics/Resugar/Fixtures.lean) pair lifted certificates
with hand-written certificates that both checkers must reject; their export is committed
as `egglog/tests/lean-certificates.json`, and `make lean-certificate-test` also exports
and checks the whole corpus.

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

**Step 1 is complete.** [Complete.lean](EgglogSemantics/Congruence/Complete.lean) proves
`Egglog.Congruence.encode_corresponds`:

```lean
Cong src a b ↔ SameClass target.toDatabase a b
```

Its premises are `P.EncodeDomain`, a source execution from empty, successful compiled
execution, and membership of both endpoints in the source. `encode_corresponds_relational`
gives the same theorem for execution using structural matching and table operations only.
Termination is not asserted.

**Step 2 is complete for the agreed constructor source fragment.**
[SourceProof/Soundness.lean](EgglogSemantics/SourceProof/Soundness.lean) proves
`check_supported` and `check_sound` for the executable checker. Accepted claims have
source existence witnesses for every subterm. For endpoints held by the source,
acceptance implies its original `Cong` relation. The source state must be reached by
the original program, well formed, and saturated for every ruleset. No proof is accepted
by assuming an unproved intermediate term exists.

**Step 3 is implemented.** [Provenance/Soundness.lean](EgglogSemantics/Provenance/Soundness.lean)
proves that every accepted relational fact exists in a well-formed, reached state
saturated for the original relational program's rules and merges. The corpus gate
checks data preservation and every retained function entry's extracted certificate.

**Steps 4 and 5 are implemented.** [Resugar/Soundness.lean](EgglogSemantics/Resugar/Soundness.lean)
proves `lift_sound` for lifted certificates. Every retained row of every in-domain corpus
program lifts to a certificate the source checker accepts, and Rust egglog's checker
accepts the same certificates and rejects the same hand-written counterexamples
(`make lean-certificate-test`).

Source merge proofs are deferred: equality can produce another spelling of one
stored function row without establishing a second input to its merge body. The
[checker guide](CHECKER.md#source-merge-inputs) records the counterexample. This does not
affect the constructor-only completeness theorem or the relational provenance pass.

The theorem retains `Program.EncodeDomain`: constructor declarations, no primitive
or generated source names, consistent arities, supported queries, scoped and declared
heads, and no literal unions. Arbitrary source merge functions remain outside its scope.
See [Source.lean](EgglogSemantics/Encoding/Source.lean) for the exact conditions.

## Legacy theorem and checker

[Encoding/Complete.lean](EgglogSemantics/Encoding/Complete.lean) retains the proved
`Egglog.encode_corresponds` theorem for the old, proof-carrying `Egglog.encode`:

```lean
theorem encode_corresponds {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) (a b : Term) (ha : a ∈ src.terms)
    (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass tgt.toDatabase a b
```

This theorem concerns data correspondence and never interprets proof annotations. It
remains valid despite the [legacy checker's unsoundness](CHECKER.md). Both endpoints must
exist in the source; generated view keys need not correspond to existing source terms.
Successful execution is assumed; termination is not proved.

## Validation

`make lean-check` builds the library, audits for proof holes, and runs the corpus gates.
The congruence gate compares every pair of held source terms against its reading and
compares all live data rows against the legacy encoder after dropping proof columns,
proof constructors, and history relations. The provenance gate checks data preservation
and every retained row's extracted certificate. The resugar gate lifts those certificates
and checks them against the original source program, and the certificate gate exports the
same certificates and checks them with Rust egglog. Failures, stuck executions, and
insufficient fuel fail the command. Out-of-domain cases are counted separately.

From `semantics/`:

```sh
lake build difftest
.lake/build/bin/difftest congruence 64
.lake/build/bin/difftest congruence 64 both-2 rand-43 sat-hit
.lake/build/bin/difftest provenance 64
.lake/build/bin/difftest resugar 64
.lake/build/bin/difftest export-certificates 64 /tmp/certificates.json
```

Executable regressions also check recursive traversal order, origin tags, rebuilding
necessity, and rejection of a rule firing whose constructor premise never existed.
