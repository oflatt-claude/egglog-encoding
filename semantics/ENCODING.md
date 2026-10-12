# Encoding passes

## Agreed plan and scope

This is the working plan for PR #58. The implementation order is:

1. **Port completeness to the congruence pass.** Establish the execution invariants
   needed for source/target correspondence, retaining the current constructor-only
   source fragment (`Program.EncodeDomain`). The paper's completeness theorem ends
   here. The compiled target uses functions, but extending the theorem to arbitrary
   source merge functions is deferred.
2. **Implement a sound source proof checker.** Check explicit propositions against
   the original program. `Fiat` must be justified by original globals; it cannot
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
resugaring. The congruence pass is implemented in
[Congruence/Encode.lean](EgglogSemantics/Congruence/Encode.lean). The latter two passes are
not implemented yet. The old combined encoder remains available while its execution
invariants are ported; its proof annotations have known correctness defects.

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

## Proof status

The new pass currently has kernel-checked proofs of:

- `encode_unionFree`: commands, rule heads, and merge bodies contain no built-in unions.
- `encodeQuery_flat` and `encodeQueryExpr_next`: flattened atoms contain only leaf
  columns, and each application occurrence consumes exactly one fresh id.
- `execM_encode_eqsRefl` and `encode_cong_iff`: built-in equality is exactly structural
  identity on stored terms.
- `encode_relational`: the target executes with the same result using no congruence
  closure or implicit re-keying, including during queries, merges, and saturation.
- `sourceMatch_of_encodedQuery`: sound view entries turn a flattened query match into
  an existing source query match, preserving the values needed by its rule head.
- `sameClassF_iff`: the executable reader agrees with `SameClass`, under its explicit
  subterm-closure and diagonal-equality hypotheses.
- `corresponds_of_invariants`: source congruence agrees with the target reading when view
  leaders, view coverage, recorded source unions, and view-entry soundness hold.

The execution proof establishing those invariants for `Congruence.encode` is **not yet
ported**. Thus the new pass does not yet have an end-to-end completeness theorem.
The paper's completeness theorem will stop at this pass; later instrumentation and
resugaring still require soundness.

The shared source restrictions are `Program.EncodeDomain` in
[Source.lean](EgglogSemantics/Encoding/Source.lean): constructor declarations, no primitive
or generated source names, consistent arities, supported queries, scoped and declared
heads, and no literal unions. This does not cover arbitrary source merge functions.
The semantic language itself supports function entries, including the generated tables.

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

`make lean-check` builds the library, audits for proof holes, and runs the congruence
corpus gate. The gate compares every pair of held source terms against the new reading
and compares all live data rows against the legacy encoder after dropping proof columns,
proof constructors, and history relations. Failures, stuck executions, and insufficient
fuel fail the command. Out-of-domain cases are counted separately.

From `semantics/`:

```sh
lake build difftest
.lake/build/bin/difftest congruence 64
.lake/build/bin/difftest congruence 64 both-2 rand-43 sat-hit
```

Executable regressions also check recursive traversal order, origin tags, rebuilding
necessity, and rejection of a rule firing whose constructor premise never existed.
