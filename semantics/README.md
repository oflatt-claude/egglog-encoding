# EgglogSemantics

A Lean 4 model of egglog's semantics, of the paper's compiler passes and proof
production, with the paper's theorems proved. Originally ported from the Redex model in
[egglog PR #324](https://github.com/egraphs-good/egglog/pull/324).
The reference interpreter targets the extended egglog implementation in this workspace.

## Language and semantics

The language is untyped and has no declarations. A program is a schedule, built from
runs of rule lists, saturations and sequences nested as in egglog's `run-schedule`, and
one check that decides its outcome; applying any name to any arguments builds a
term, and an initial fact is a run of an empty-query rule. A rule's query is a
conjunction of term patterns, equalities and disequalities, and its actions build terms,
assert equalities with `union`, and `subsume` rows. egglog's named rulesets are resolved by
the parser: a run of a ruleset fires the rules registered in it so far.

A state is an e-graph: a set of equations and a set of subsumed rows. Reflexive equations
record which terms exist, and congruence is derived over the terms the equations mention.
A query looks rows up and matches no subsumed row, in any spelling; a query variable is
bound to the representative of a class, its least stored spelling in the term order, as
egglog binds a variable to an e-class. A round fires every rule it names against the
pre-state and adds every write and every subsumed row, in no particular order. Definitions
and brief rationale are in [Spec/Step.lean](EgglogSemantics/Spec/Step.lean).

## Reading guide

Start with [ExtlogTheorems.lean](ExtlogTheorems.lean). It states every theorem the paper claims,
in full and in the vocabulary of the specification, and proves each by one reference into
`EgglogSemantics/Proofs/`:

| Theorem | Statement |
| --- | --- |
| `congruence_pass_correct` | A well-formed source program in the fragment and its compilation have the same outcome and the same divergence (paper `thm:congruence`). |
| `provenance_pass_correct` | Instrumenting a union-free program with keyed queries changes neither outcome nor divergence, and erasing the log from its final e-graph gives the original's (paper `thm:provenance`). |
| `passes_compose` | The fully compiled program has the source program's outcome and divergence. |
| `checker_sound` | A claim the proof checker accepts, between terms of the saturated final e-graph, holds there. |
| `log_proofs_checked` | Every proof read off the firing log is accepted by the checker. |
| `lifted_proofs_checked`, `lifted_proofs_sound` | Lifted proofs are accepted by the source checker, and their claims hold in the saturated source e-graph. |

Specification and proofs are separate: nothing outside `Proofs/`, `Tests/` and
`ExtlogTheorems.lean` imports a proof module. The `@[blueprint "def:…"]` and
`@[blueprint "thm:…"]` attributes carry the paper's labels and statements, and
`make paper-sync` writes them into the paper.

| Paper | Lean |
| --- | --- |
| Section 4, semantics | `EgglogSemantics/Spec/`: `Syntax` (programs, schedules, rules), `Term`, `Database` (an e-graph as equations and subsumed rows), `Congruence` (`Cong` and `terms`), `Match` (queries, representatives), `Eval` (expressions, actions), `Step` (rounds, schedules, outcomes: `Reach`, `Eval`), `Divergence`, `Behavior`, `Order` (the term order behind representatives) |
| Section 5, congruence pass | `Congruence/Encode.lean` (the pass `encode`, the maintenance rules, the view and phasing options), `Source/Domain.lean` and `Source/WellFormed.lean` (the fragment and well-formedness), `Congruence/Read.lean` (reading a compiled e-graph back) |
| Section 6, proofs | `SourceProof/Format.lean` and `Checker.lean` (proof terms and the checker), `Provenance/Encode.lean` (instrumentation) and `Log.lean` (proofs read off the log), `Resugar/Claim.lean`, `Query.lean`, `Lift.lean` (lifting), `Resugar/Execute.lean` (`prove`) |
| The proofs | `Proofs/Congruence/` (the simulation for Section 5; plan in [PROOF-PORT-S.md](PROOF-PORT-S.md)), `Proofs/Provenance/` ([PROOF-PORT-T.md](PROOF-PORT-T.md)), `Proofs/SourceProof/` and `Proofs/Resugar/` (checker and lifting soundness); the remaining modules are lemmas about the specification and the reference interpreter |
| Executable | `Impl/` (finite reference interpreter), `Congruence/Relational.lean` (execution without equality reasoning), `Tests/`, `DiffTest.lean` (comparisons with egglog and the corpus gates), `tests/` (`.egg` programs with snapshots of their encodings and lifted proofs) |

To check the theorems from this directory: `lake build` (the `assert_no_sorry` lines in
`ExtlogTheorems.lean` fail the build on any incomplete proof), `make lean-holes` (no `sorry`
anywhere), and `#print axioms ExtlogTheorems.congruence_pass_correct` and the others, which
show only `propext`, `Classical.choice` and `Quot.sound`.

## Encoding passes

The congruence compiler translates source programs, which use neither `subsume` nor
disequality, into an explicit union-find relation maintained by rules that subsume
a stale row and write its replacement; the output has no merge function. It handles query
flattening and rebuilding, with one id column per relation. The provenance pass adds a
firing log, one relation per rule recording the values each firing bound, and proofs are
reconstructed from the log afterwards. Proof lifting turns them into source proofs that
both the Lean and Rust checkers accept. The [encoding guide](ENCODING.md) describes the
encoding, the log, and the rationale; the corpus gates (`difftest congruence`,
`difftest provenance`) also check both correctness statements executably. Brief certificate
notes live with the [source checker](EgglogSemantics/SourceProof/Checker.lean) and
[relational checker](EgglogSemantics/Provenance/Checker.lean).

## Validation

From the workspace root:

```sh
make check                 # Python and Rust formatting, checks, and tests
make -C semantics lean-check            # Lean build, proof-hole audit, corpus gates, Rust certificate check
cargo build --release -p egglog
make -C semantics lean-difftest          # compare Lean and egglog per-function row counts
make -C semantics lean-compiled-difftest # run the compiled programs in egglog and compare e-node censuses
make -C semantics paper-sync             # regenerate the semantics section of ../extended-egglog-paper
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
