# Proof encoding

[Encode.lean](EgglogSemantics/Encoding/Encode.lean) defines `encode : Program → Program`.
It translates constructor programs into explicit tables that represent equivalence and
carry proofs. [Complete.lean](EgglogSemantics/Encoding/Complete.lean) proves the
correspondence between source congruence and the encoded target.

## Tables and proof terms

For each source constructor `f`, the target declares a view and a term relation, alongside
one shared union-find table:

| Table | Shape | Meaning |
| --- | --- | --- |
| `@UF` | `t ↦ (parent, proof)` | An edge proving `t = parent` |
| `@fView` | `children ↦ (id, proof)` | An entry proving `f(children) = id` |
| `@fTerm` | `(children, id) ↦ ()` | A record of a built application; the encoder never reads it |

Ids are structural terms: building `f` over children `cs` uses `.app f cs` as its id.
`encodeBuild` returns that expression and writes the term and view entries. It performs
no table lookup in an action. Rule queries read view entries and bind their id and proof
columns; `encodeQuery` flattens nested applications into those reads.

A source `union` writes an explicit `@UF` edge. Both `@UF` and the views have merge bodies
that retain the smaller id and write the displaced id's edge to it. The surviving row
keeps its proof; the displaced edge composes proofs with symmetry and transitivity.
`@Fiat`, `@Sym`, `@Trans`, `@Congr_k`, and `@Rule_i` are ordinary constructor terms, with
their propositions supplied by the rows that contain them. See the [checker](CHECKER.md)
for their interpretation.

The encoded program is `Program.UnionFree` (`encode_unionFree`). Its asserted equations
are therefore diagonal, and built-in target `Cong` relates only identical held terms.
Source equivalence is represented by the explicit tables.

## Rebuilding

The maintenance rules compress union-find paths and propagate changed ids through view
rows. `encodeCmd` schedules `Cmd.saturate @rebuild` after actions and runs.
`allMaintenanceRules` also copies the maintenance rules into every ruleset named by a
source `Cmd.saturate`, so rebuilding participates in its rounds. Rebuilding only after
the source ruleset settles would miss matches that require an earlier round's re-keyed
view rows.

Both `@UF` and the views declare `identityVals := some 1`: only the id column determines
whether a collision changes a row. A changed proof alone does not trigger another merge.
This matters because the language has no disequality guard to suppress redundant
maintenance firings. `MergeConflict` applies the same test in the specification.

## Correspondence theorem

The proved statement is:

```lean
theorem encode_corresponds {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) (a b : Term) (ha : a ∈ src.terms)
    (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass tgt.toDatabase a b
```

`SameClass` holds when both source terms have a common id through `ViewRepr`, which
recursively reads the target's views. Rebuilding propagates union-find edges into those
views; the relation itself performs no union-find walk.
[Correspond.lean](EgglogSemantics/Encoding/Correspond.lean) provides `sameClassF` and
proves that this executable decision procedure agrees with the relation.

`Program.EncodeDomain` requires constructor declarations, legal writes (hence no source
`set`), no primitive applications or generated `@` names, compatible function arities,
queries supported by the flattening, and declared and query-scoped rule heads. Its
`noLitUnion` condition prevents union operands from evaluating to literals.
The declaration's fields in `Encode.lean` give the exact restrictions.

Both implications are proved. The forward direction uses view coverage, rebuild closure,
and the recorded source unions. The reverse direction uses `execM_soundTerms` to justify
the terms added by the target's actions, rule firings, and merge phases against the source.
The theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The hypotheses matter:

- The target is the result of `execM (encode P)`, including its scheduled rebuilds.
  Arbitrary target states do not supply that guarantee.
- Both endpoints belong to `src.terms`. Generated target terms can share a class without
  having existed in the source, so an unrestricted equivalence is false.
- The theorem assumes successful executions. It does not prove that saturation terminates.
- The theorem concerns equality correspondence. General checker soundness and acceptance
  of every generated proof are separate, unproved obligations.

The Lean files retain executable witnesses and counterexamples beside these conditions,
including `encode_corresponds_witness`, `ncTgt_not_readsSelf`,
`ncTgt_not_viewsProduct`, and `bare_build_invents_equality`.

## Relation to the Rust implementation

This model follows the table-based encoding in
[egglog/src/proofs](../egglog/src/proofs/proof_encoding.rs), but uses structural ids and
ordinary proof terms. Rust uses allocated ids, packed proof representations, and a
conversion pipeline before checking. The Lean encoding does not model that pipeline,
containers, deletion, or nested schedules, and its source domain excludes merge functions.
The [merge interpreter's refinement](MERGE.md#interpreter-contracts) has its own hypotheses;
it does not establish the correspondence theorem for saturating encoded programs.

[Subst.lean](EgglogSemantics/Encoding/Subst.lean) contains ground-term substitution helpers
used by the generalized encoding proofs. The public `encode` starts with an empty
substitution; `EncStep.subst_empty` proves it remains empty in aligned executions.

Run `difftest correspond 64` as described in the [README](README.md#validation) to compare
source congruence with `sameClassF` over the executable corpus.
