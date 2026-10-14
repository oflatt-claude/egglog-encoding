# EgglogSemantics

A Lean 4 model of egglog's semantics and proof encoding, originally ported from the
Redex model in [egglog PR #324](https://github.com/egraphs-good/egglog/pull/324).
The reference interpreter targets the extended egglog implementation in this workspace,
including multi-output functions and action blocks inside `:merge` bodies.

## Language and semantics

Programs declare functions and rules, assert expressions and function rows, union values,
run or saturate named rulesets, and check queries. A check succeeds without changing
the database or terminates the program with `checkFailed`. Rule variables come from the query; merge bodies
use their old/new parameters. Actions evaluate in a fixed environment.

The specification records equations and derives congruence over the terms they mention.
Constructors build values; other functions store key/value entries. A complete atom such as
`(LowerBound expr bound)` reads an entry in a query and records one in an action. The
declaration determines the key/output split. Entries cannot be nested inside value
expressions or used as equality or union operands. Merge bodies can perform actions as
well as return values. The [merge semantics](MERGE.md) guide explains how this relates to the interpreter's row index,
its refinement contracts, and the limits of the model.

## Encoding passes

The congruence compiler translates constructor programs into explicit union-find and view
tables. It handles query flattening and rebuilding, with one id output per table and no
proof annotations. A separate provenance pass adds proof columns for globals, rule firings,
and function merges, and proof lifting turns its proofs into source proofs
that both the Lean and Rust checkers accept.

The congruence pass proves
[`preservesObservations`](EgglogSemantics/Proofs/Congruence/AbstractComplete.lean):
for well-formed programs in the supported source fragment, terminating source and compiled
evaluations agree on success or check failure. Both sides use mathematical databases;
the proof derives its representation invariants from the actual executions and imports no
executable interpreter. Termination preservation remains a stretch goal, and interpreter
correctness is outside the paper. Executable correspondence and differential tests remain
sanity checks. This conditional theorem does not rule out a compiler introducing
divergence; the encoding guide includes mathematical non-vacuity examples and a
comparison with CompCert and CakeML. Both the constructor source checker and relational
provenance checker have proved soundness and existence support. The library permits no
`sorry`.

The [encoding guide](ENCODING.md) describes the current implementation, theorem status,
and source restrictions. The [checker guide](CHECKER.md) explains the certificate
boundaries.

## Layout

| Directory | Contents |
| --- | --- |
| `EgglogSemantics/Spec/` | Syntax, databases, congruence, evaluation, matching, relational steps, scope |
| `EgglogSemantics/Impl/` | Finite reference interpreters and front-end checks |
| `EgglogSemantics/Source/` | The source fragment the compiler accepts, and the generated names |
| `EgglogSemantics/Congruence/` | Congruence compiler and relational execution |
| `EgglogSemantics/SourceProof/` | Source proof format and checker |
| `EgglogSemantics/Provenance/` | Function provenance instrumentation, proof format, checker, and extraction |
| `EgglogSemantics/Resugar/` | Proof lifting to source proofs, fixtures, and JSON export |
| `EgglogSemantics/Proofs/` | Every theorem: interpreter refinement, the completeness proof, checker soundness, lifting soundness, counterexamples |
| `EgglogSemantics/Tests/` | Executable regressions, `.egg` parsing and emission, and proof rendering |
| `tests/` | Hand-written `.egg` programs with snapshots of their encodings and lifted proofs |
| `DiffTest.lean` | Curated and generated comparisons with egglog and encoding/checker probes |

Start with [Syntax.lean](EgglogSemantics/Spec/Syntax.lean),
[Eval.lean](EgglogSemantics/Spec/Eval.lean), and
[Step.lean](EgglogSemantics/Spec/Step.lean), then read
[Congruence/Encode.lean](EgglogSemantics/Congruence/Encode.lean) and
[Congruence/Correctness.lean](EgglogSemantics/Congruence/Correctness.lean).

## Validation

From the workspace root:

```sh
make check                 # Python and Rust formatting, checks, and tests
make lean-check            # Lean build, proof-hole audit, corpus gates, Rust certificate check
cargo build --release -p egglog
make lean-difftest          # compare Lean and egglog per-function row counts
```

Additional executable probes, from `semantics/`:

```sh
lake build difftest
.lake/build/bin/difftest congruence 64
.lake/build/bin/difftest provenance 64
.lake/build/bin/difftest resugar 64
```

The toolchain is pinned in [lean-toolchain](lean-toolchain), and Mathlib in
[lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json). Install `elan`,
then run `lake exe cache get` from this directory when setting up a fresh checkout.
