# Proof checkers

[SourceProof.check](EgglogSemantics/SourceProof/Checker.lean) validates proof trees
against the original program, unions included. Every node states its claim, and the
checker validates each node against the claims of its subproofs. It is the checker that
corresponds to Rust's. It accepts constructor programs without primitive applications
whose query facts are applications, as in egglog. Function declarations are rejected;
functions are handled in the separate relational provenance checker.

`Fiat` facts come only from original global actions. A rule proof identifies the original
command and supplies an exact substitution and one proof per original query conjunct, in
order. The checker does not flatten the query. Congruence requires a base proof for the
enclosing application and a proof for the replaced child. Invalid substitutions,
endpoints, and head conclusions are rejected.

[Soundness.lean](EgglogSemantics/Proofs/SourceProof/Soundness.lean) proves `check_supported`:
every accepted claim retains source existence witnesses for all its subterms. Its
`check_sound` corollary gives `Cong db lhs rhs` when both endpoints are held by `db`.
Both theorems assume that `db` is reached by the original program, is well formed, and
is saturated for every ruleset. They do not assume validity of intermediate claims.

The [regressions](EgglogSemantics/Tests/SourceProof.lean) cover missing existence,
rule-created terms, nested queries, premise ordering, malformed substitutions, wrong
claims, and anchored congruence. The [fixtures](EgglogSemantics/Resugar/Fixtures.lean)
hold the proofs that the Lean and Rust checkers must judge alike.

## Why `Fiat` is restricted

A checker that lets `Fiat` justify any constructor reflexivity is unsound. Build `A` and
`B`, declare but never build `Missing`, and saturate this rule:

```text
(rule ((Missing)) ((union (A) (B))))
```

The source cannot fire the rule, yet a `Fiat` premise inventing `Missing` would prove
`A = B`. Requiring the final endpoints to exist does not justify intermediate terms, and a
term created by an earlier rule needs that rule's proof. `Fiat` therefore comes only from
original globals, and every rule premise carries its own proof. The congruence compiler's
regression tests verify that this program keeps `A` and `B` distinct and does not
represent `Missing`.

## Relational provenance

[Provenance.check](EgglogSemantics/Provenance/Checker.lean) checks proof trees of facts
against the uninstrumented relational program, which is the compiled program and
therefore has no `union`. It is an intermediate step on the way to a source proof, not
the checker that corresponds to Rust's. It accepts original globals, rule consequences,
merge bodies and results, and subterms of established facts. It has no equality axioms.
Merge inputs must be established entries at the same structural key, with conflicting
output columns according to the original declaration.

[Provenance.check_sound](EgglogSemantics/Proofs/Provenance/Soundness.lean) proves membership
in any well-formed, reached state saturated for the program's rules and merges. Extraction
decodes generated proof constructors into these trees and checks them. This intermediate
proof still mentions generated tables; it is not a source proof.

## Rust compatibility

The instrumentation pass records actual globals, rule firings, and merge derivations, and
[lifting](EgglogSemantics/Resugar/Lift.lean) reconstructs source-level proofs with
explicit claims, substitutions, and existence evidence, following the same recursive
order as query flattening.

Rust's [proof checker](../egglog/src/proofs/proof_checker.rs) does not permit arbitrary
eq-sort constructor reflexivity as `Fiat`. Its primitive-value reflexivity case is
restricted, and its [proof format](../egglog/src/proofs/proof_format.rs) carries explicit
propositions and anchored congruence. Rule-created constructions have rule provenance.

The same lifted proofs are checked in Lean and Rust: `Resugar.Export` writes them as
JSON certificates and [proof_certificate.rs](../egglog/src/proofs/proof_certificate.rs)
replays them through Rust's checker. Running the two encoders separately on the same
program would not establish that property. A certificate lists the tree's nodes in
postorder with repeated subtrees shared, so every reference is to an earlier node; the
bridge rejects any other reference, since Rust's checker follows references recursively.

## Source merge inputs

A merge proof cannot infer an actual collision from two congruent row spellings alone.
For example, let `Table` have one output column and a merge body that unions `old` with
`C`, returning `old`. Store only `Table(A)`, assert `A = B`, and build `C`. Source
execution leaves `A` and `C` distinct: there is no conflicting second row.

Anchored congruence can nevertheless derive `Table(A) = Table(B)`, and symmetry and
transitivity give reflexivity for `Table(B)`. A merge justification taking `Table(A)` and
`Table(B)` as its inputs would run the body and incorrectly conclude `A = C`.

The [merge-input regression](EgglogSemantics/Proofs/SourceProof/Counterexamples.lean) reproduces
this mismatch. The source checker therefore accepts constructor-only programs and has no
merge justification; source merge-input evidence is deferred. Functions remain necessary
in the relational provenance pass, whose input program has no implicit equality reasoning.
The source semantics are unchanged.

See the [encoding guide](ENCODING.md) for validation and proof status.
