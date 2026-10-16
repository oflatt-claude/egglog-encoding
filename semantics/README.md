# EgglogSemantics

A Lean 4 model of egglog's semantics and proof encoding, originally ported from the
Redex model in [egglog PR #324](https://github.com/egraphs-good/egglog/pull/324).
The reference interpreter targets the extended egglog implementation in this workspace,
including multi-output functions and action blocks inside `:merge` bodies.

## Language and semantics

Programs declare functions and rules, run or saturate named rulesets, and check queries.
Actions occur in rule heads and merge bodies; initial facts use an empty-query rule and
one `run`. A check leaves the database unchanged or stops with `checkFailed`.
Rule variables come from the query; merge bodies use their old/new parameters.

The specification records equations and derives congruence over the terms they mention.
Constructors build values; other functions store key/value entries. A complete atom such as
`(LowerBound expr bound)` reads an entry in a query and records one in an action. The
declaration determines the key/output split. Entries cannot be nested inside value
expressions or used as equality or union operands. Merge bodies can perform actions as
well as return values. Definitions and brief rationale are in
[Spec/Step.lean](EgglogSemantics/Spec/Step.lean).

## Encoding passes

The congruence compiler translates constructor programs into explicit union-find and view
tables. It handles query flattening and rebuilding, with one id output per table and no
proof annotations. A separate provenance pass adds proof columns for globals, rule firings,
and function merges, and proof lifting turns its proofs into source proofs
that both the Lean and Rust checkers accept.

[`preservesBehaviors`](EgglogSemantics/Proofs/Congruence/Correctness.lean) proves that
well-formed supported source programs without `saturate` and their compilations have
exactly the same success, check-failure, and divergence behaviors. Both use mathematical
databases. Generated rebuilding and merging terminate under every permitted schedule;
termination is not a premise. Interpreter correctness remains a separate sanity check,
with legacy interpreter and certificate proofs still being ported.

The [encoding guide](ENCODING.md) describes the current implementation, theorem status,
and source restrictions. Brief certificate notes live with the
[source checker](EgglogSemantics/SourceProof/Checker.lean) and
[relational checker](EgglogSemantics/Provenance/Checker.lean).

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
