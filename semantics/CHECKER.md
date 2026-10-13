# Proof checkers

[SourceProof.check](EgglogSemantics/SourceProof/Checker.lean) validates certificates with
explicit claims and references to earlier nodes. It accepts constructor programs without
primitive applications. Function declarations and merge justifications are rejected;
functions are handled in the separate relational provenance checker.

`Fiat` facts come only from original global actions. A rule proof identifies the original
command and supplies an exact substitution and one proof per original query conjunct, in
order. The checker does not flatten the query. Congruence requires a base proof for the
enclosing application and a proof for the replaced child. Invalid references, substitutions,
endpoints, and head conclusions are rejected.

[Soundness.lean](EgglogSemantics/SourceProof/Soundness.lean) proves `check_supported`:
every accepted claim retains source existence witnesses for all its subterms. Its
`check_sound` corollary gives `Cong db lhs rhs` when both endpoints are held by `db`.
Both theorems assume that `db` is reached by the original program, is well formed, and
is saturated for every ruleset. They do not assume validity of intermediate claims.

The [regressions](EgglogSemantics/SourceProof/Tests.lean) cover missing existence,
rule-created terms, nested queries, premise ordering, malformed substitutions, invalid
references, and anchored congruence. Rust interoperability remains a separate obligation.

## Relational provenance

[Provenance.check](EgglogSemantics/Provenance/Checker.lean) checks facts against the
uninstrumented relational program. It accepts original globals, rule consequences,
merge bodies and results, and subterms of established facts. It has no equality axioms.
Merge inputs must name established entries at the same structural key, with conflicting
output columns according to the original declaration.

[Provenance.check_sound](EgglogSemantics/Provenance/Soundness.lean) proves membership
in any well-formed, reached state saturated for the program's rules and merges. Extraction
decodes generated proof constructors into these explicit certificates and checks them.
This intermediate certificate still mentions generated tables; it is not a source proof.

## Legacy checker

[Checker.lean](EgglogSemantics/Encoding/Checker.lean) implements the old
`Proof.Checks P pf a b : Bool`. **It is known to be unsound** and is retained only as a
reference during the split into congruence compilation, provenance, and resugaring.
It is not a correctness oracle for the new congruence pass.

## The existence defect

The old encoder writes `@Fiat` in every newly built view row, including constructions
inside rule heads. That omits the rule justification establishing the term's existence.
The old checker compounds this by allowing `@Fiat` to justify arbitrary supplied
constructor reflexivities.

For example, build `A` and `B`, declare but never build `Missing`, and saturate this rule:

```text
(rule ((Missing)) ((union (A) (B))))
```

The source cannot fire the rule. Nevertheless, the legacy checker accepts
`(@Rule_0 (@Fiat))` as a proof of `A = B`: its `Fiat` premise invents the existence of
`Missing`. Requiring the final endpoints to exist does not justify intermediate terms.
The new congruence compiler's regression tests verify that this program keeps `A` and
`B` distinct and does not represent `Missing`.

There is also missing provenance in generated proofs: with both endpoints free, a
`Fiat` premise can only select from top-level equations, so it cannot recover a term
created by an earlier rule. This explains the rejected `both-2` and `rand-43` proofs.
Those rejections are not merely a less powerful checker; the encoder omitted necessary
construction justifications.

## Legacy representation

Nodes are ordinary constructor terms `@Fiat`, `@Sym`, `@Trans`, `@Congr_k`, and `@Rule_i`.
They contain no explicit claim. `Proof.props` guesses claims and substitutions from the
endpoints available to the caller. The checker independently flattens queries to match
this old format. Premises reading source merge-function entries are unsupported.

`Proof.Sound` and `Proof.SoundAt` describe the intended soundness contract. They are
unproved, and the current implementation does not satisfy the contract. The separate
`Egglog.encode_corresponds` theorem proves only data correspondence and does not depend
on this checker.

## Replacement and Rust compatibility

The new congruence pass emits no certificates. The separate instrumentation pass
records actual globals, rule firings, and merge derivations. Resugaring will reconstruct
source-level certificates with explicit claims, substitutions, and existence evidence,
following the same recursive order as query flattening.

Rust's [proof checker](../egglog/src/proofs/proof_checker.rs) does not permit arbitrary
eq-sort constructor reflexivity as `Fiat`. Its primitive-value reflexivity case is
restricted, and its [proof format](../egglog/src/proofs/proof_format.rs) carries explicit
propositions and anchored congruence. Rule-created constructions have rule provenance.

Compatibility will require checking the same resugared certificate in Lean and Rust.
Running their separate encoders on the same program does not establish that property.
Resugaring and the shared-certificate bridge are not implemented yet.

## Source merge inputs

A merge proof cannot infer an actual collision from two congruent row spellings alone.
For example, let `Table` have one output column and a merge body that unions `old` with
`C`, returning `old`. Store only `Table(A)`, assert `A = B`, and build `C`. Source
execution leaves `A` and `C` distinct: there is no conflicting second row.

Anchored congruence can nevertheless derive `Table(A) = Table(B)`, and symmetry and
transitivity give reflexivity for `Table(B)`. Passing `Table(A)` and `Table(B)` to a
merge justification would run the body and incorrectly conclude `A = C`.

The [merge-input regression](EgglogSemantics/SourceProof/Counterexamples.lean) reproduces
this mismatch. The source checker will first accept constructor-only programs;
source merge-input evidence is deferred. Functions remain necessary in the relational provenance pass,
whose input program has no implicit equality reasoning. The source semantics are unchanged.

`difftest check 64` still runs the legacy diagnostic; it is not an all-passing validation
gate. See the [encoding guide](ENCODING.md) for the new pass's validation and proof status.
