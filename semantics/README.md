# EgglogSemantics

A Lean 4 model of egglog's semantics and proof encoding, originally ported from the
Redex model in [egglog PR #324](https://github.com/egraphs-good/egglog/pull/324).
The reference interpreter targets the extended egglog implementation in this workspace,
including multi-output functions and action blocks inside `:merge` bodies.

## Let-free language

The Lean syntax has three actions: build an expression, union two expressions, and set a
function row. There are no global or local `let` bindings. Rule variables come from the
query; merge bodies use their declared old/new parameters. Reusing an expression means
writing it again, or matching its value in a rule query.

Rules are registered exactly as written. Action blocks do not extend their evaluation
environment, and commands preserve the ambient environment. A program starting at the
empty database therefore finishes with an empty environment. `Database.env` remains the
context used to evaluate a query substitution or merge parameters, rather than a store
of global bindings. The proof checker likewise processes a head under one fixed query
substitution and has no global-binding context.

Generic substitution helpers remain in the encoding proofs. `EncStep.subst_empty` proves
that actual encoded executions carry the empty substitution throughout; no command updates it.

This restriction applies to the Lean model, encoding, checker, and differential-test
programs. The Rust parser and runtime retain their existing syntax.

## Proofs and encoding

`Encoding/Encode.lean` transforms constructor programs into explicit view tables and a
union-find table. Each recorded equality carries a proof. Generated ids are structural
terms; generated variable names and rule-proof constructor names have separate counters.
The encoding inserts rebuild work after writes and into source saturation loops.

`Encoding/Complete.lean` proves `encode_corresponds`: source congruence agrees with the
encoded target's `SameClass` relation under `Program.EncodeDomain` and successful source
and target executions. The domain restricts the source to constructors, reserves generated
names, and checks arities, query shape, declaration order, and head scope. The library's
`make lean-check` target permits no `sorry`.

The executable proof checker is separate. Its `SoundAt` predicate states the intended
checker contract; defining that predicate does not prove general checker soundness.
The checker tests and `difftest check` exercise the implemented proof vocabulary and
report unsupported proof shapes.

## Layout

| Directory | Contents |
| --- | --- |
| `EgglogSemantics/Spec/` | Syntax, databases, congruence, evaluation, matching, relational steps, scope |
| `EgglogSemantics/Impl/` | Finite reference interpreters and front-end checks |
| `EgglogSemantics/Proofs/` | Interpreter refinement, preservation, totality, and counterexamples |
| `EgglogSemantics/Encoding/` | Encoder, checker, correspondence, matching, and completeness proofs |
| `EgglogSemantics/Tests/` | Kernel-checked examples, executable guards, and `.egg` emission |
| `DiffTest.lean` | Curated and generated comparisons with egglog and encoding/checker probes |

Read `Spec/Syntax.lean`, `Eval.lean`, and `Step.lean` first, then the definitions in
`Encoding/Encode.lean` and the final theorems in `Encoding/Complete.lean`.

The specification only adds equations. The merge interpreter maintains a row index that
can replace entries, so its general refinement contract is containment (`execM_contained`).
The constructor-only interpreter has the stronger `exec_programStep` contract.

`PLAN.md`, `MERGE.md`, `ENCODING.md`, and `CHECKER.md` retain design history, including
refuted candidate invariants. Their historical descriptions of global lets and parked
proof obligations predate the current model; use the Lean declarations for current contracts.

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

The toolchain is pinned in `lean-toolchain`, and Mathlib in `lakefile.toml` and
`lake-manifest.json`. Install `elan`, then run `lake exe cache get` from this directory
when setting up a fresh checkout.
