# Proof checker

[Checker.lean](EgglogSemantics/Encoding/Checker.lean) defines
`Proof.Checks P pf a b : Bool`. It checks the claim `a = b` using a proof term and the
source program. Its inputs contain no target database or union-find tables.

## Context and vocabulary

`Proof.ctxOf` reads declarations, equations produced by top-level actions, and rules in
program order. `procActions` evaluates a rule head under one fixed query substitution and
collects its equations, including reflexive equations for built subterms.

The encoding uses five justification kinds:

| Proof term | Meaning |
| --- | --- |
| `@Fiat` | An equation from top-level actions, or a reflexive claim |
| `@Sym p` | Reverse the claim justified by `p` |
| `@Trans p q` | Compose claims with a shared middle term |
| `@Congr_k p₁ … pₖ` | Congruence at a constructor, with one proof per child |
| `@Rule_i p₁ … pₙ` | Rule `i` derives the claim from the supplied premises |

A proof node contains no endpoints. `Proof.props` reconstructs the finite set of claims
it can justify under the endpoint constraints supplied by the caller. In particular,
transitivity must recover its middle term, and a rule proof must recover a substitution
whose head produces the claimed equation.

`Proof.flatQuery` independently flattens the source query into one premise per application.
Consequently, a nested pattern can need several premise proofs. Equality constraints
joining the flattened ids need no additional proof argument.
`DiffTest.lean`'s `premiseCount_eq_ruleProofArity` checks agreement with the encoder's
premise count.

The target's merge bodies use symmetry and transitivity to justify displaced union-find
edges. They do not need a separate merge justification in this constructor fragment.

## Proof status and limitations

`Proof.Sound P db` states that every accepted claim whose endpoints belong to `db.terms`
is derivable by `Cong db`. `Proof.SoundAt P` asks for this at well-formed states reached
by `P` in which every ruleset is saturated. These are definitions of the intended
contract; general checker soundness is not proved. Saturation is necessary because the
checker can accept a rule justification without a corresponding `run` in the source.

The executable checker also has known incompleteness:

- A congruence premise needs an endpoint from which to recover its constructor. With
  neither endpoint grounded, the checker cannot synthesize the claim.
- A `@Fiat` premise with both endpoints free can only draw on top-level equations. It
  cannot discover a term created by an earlier rule firing. This accounts for the
  rejected `both-2` and `rand-43` cases in `difftest check 64`.
- Premises that read merge-function rows are unsupported by the checker's expression
  evaluator; those source programs are outside `Program.EncodeDomain`.

[Checker.lean](EgglogSemantics/Encoding/Checker.lean) contains acceptance and rejection
guards. `difftest check 64` probes proofs recorded in encoded rows; it is a diagnostic
sweep, not an all-passing correctness gate. See the [README](README.md#validation) for
build and run commands.

## Relation to Rust proof checking

Rust extracts table data, parses its raw proof representation, and converts it before
checking. The relevant implementation is in
[proof_format.rs](../egglog/src/proofs/proof_format.rs) and
[proof_checker.rs](../egglog/src/proofs/proof_checker.rs). The Lean checker directly
interprets the ordinary proof terms emitted by the Lean encoder. It does not verify
Rust's extraction, packed skeletons, rule-link conversion, or proof simplification.
