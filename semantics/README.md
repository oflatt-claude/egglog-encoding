# EgglogSemantics

A Lean 4 model of egglog's semantics and proof encoding, originally ported from the
Redex model in [egglog PR #324](https://github.com/egraphs-good/egglog/pull/324).
The reference interpreter targets the extended egglog implementation in this workspace,
including multi-output functions and action blocks inside `:merge` bodies.

## Language and semantics

Programs declare functions and rules, assert expressions and function rows, union values,
and run or saturate named rulesets. Rule variables come from the query; merge bodies
use their old/new parameters. Actions evaluate in a fixed environment.

The specification records equations and derives congruence over the terms they mention.
Constructors build values; other functions store key/value entries. A complete atom such as
`(LowerBound expr bound)` reads an entry in a query and records one in an action. The
declaration determines the key/output split. Entries cannot be nested inside value
expressions or used as equality or union operands. Merge bodies can perform actions as
well as return values. The [merge semantics](MERGE.md) guide explains how this relates to the interpreter's row index,
its refinement contracts, and the limits of the model.

## Proof encoding

The encoder transforms constructor programs into explicit view and union-find tables,
with a proof attached to each recorded equality. `encode_corresponds` proves that source
congruence agrees with the encoded target's equivalence on source terms, under
`Program.EncodeDomain` and successful executions. The library permits no `sorry`.

The [encoding guide](ENCODING.md) describes the transformation and the theorem's hypotheses.
The [checker guide](CHECKER.md) describes the separate executable proof checker. General
checker soundness and acceptance of every generated proof remain unproved.

## Layout

| Directory | Contents |
| --- | --- |
| `EgglogSemantics/Spec/` | Syntax, databases, congruence, evaluation, matching, relational steps, scope |
| `EgglogSemantics/Impl/` | Finite reference interpreters and front-end checks |
| `EgglogSemantics/Proofs/` | Interpreter refinement, preservation, totality, and counterexamples |
| `EgglogSemantics/Encoding/` | Encoder, checker, correspondence, matching, and completeness proofs |
| `EgglogSemantics/Tests/` | Kernel-checked examples, executable guards, and `.egg` emission |
| `DiffTest.lean` | Curated and generated comparisons with egglog and encoding/checker probes |

Start with [Syntax.lean](EgglogSemantics/Spec/Syntax.lean),
[Eval.lean](EgglogSemantics/Spec/Eval.lean), and
[Step.lean](EgglogSemantics/Spec/Step.lean), then read
[Encode.lean](EgglogSemantics/Encoding/Encode.lean) and the final theorems in
[Complete.lean](EgglogSemantics/Encoding/Complete.lean).

## Validation

From the workspace root:

```sh
make check                 # Python and Rust formatting, checks, and tests
make lean-check            # full Lean build and zero-sorry audit
cargo build --release -p egglog
make lean-difftest          # compare Lean and egglog per-function row counts
```

Additional executable probes, from `semantics/`:

```sh
lake build difftest
.lake/build/bin/difftest correspond 64
.lake/build/bin/difftest check 64
```

The toolchain is pinned in [lean-toolchain](lean-toolchain), and Mathlib in
[lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json). Install `elan`,
then run `lake exe cache get` from this directory when setting up a fresh checkout.
