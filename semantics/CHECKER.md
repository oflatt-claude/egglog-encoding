# Legacy proof checker

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

The new congruence pass emits no certificates. The planned generic instrumentation pass
will record actual globals, rule firings, and merge derivations. Resugaring will reconstruct
source-level certificates with explicit claims, substitutions, and existence evidence,
following the same recursive order as query flattening.

Rust's [proof checker](../egglog/src/proofs/proof_checker.rs) does not permit arbitrary
eq-sort constructor reflexivity as `Fiat`. Its primitive-value reflexivity case is
restricted, and its [proof format](../egglog/src/proofs/proof_format.rs) carries explicit
propositions and anchored congruence. Rule-created constructions have rule provenance.

Compatibility will require checking the same resugared certificate in Lean and Rust.
Running their separate encoders on the same program does not establish that property.
Neither the new instrumentation pass nor that shared-certificate bridge is implemented yet.

`difftest check 64` still runs the legacy diagnostic; it is not an all-passing validation
gate. See the [encoding guide](ENCODING.md) for the new pass's validation and proof status.
