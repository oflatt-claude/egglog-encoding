# Task T: provenance pass correctness

## Scope

Prove that the provenance instrumentation (`Provenance/Encode.lean`) does not change a
program's behavior: `Egglog.Provenance.correctness : Correctness`
(`Provenance/Correctness.lean`) carries the paper's `thm:provenance` blueprint node. The
development lives under `Proofs/Provenance/`, next to the proof-extraction soundness
(`Soundness.lean`, `proofs_checked`), which is unchanged. The pass's precondition is made
explicit (`Instrumentable`, `Provenance/Encode.lean`), and the congruence compiler's output
is shown to satisfy it (`encode_instrumentable`, `Proofs/Provenance/Compiled.lean`), with
the corollary `correctness_compiled`.

## Statement

```lean
def Correctness : Prop :=
  ∀ P P' : Program, Instrumentable P → encode P = some P' →
    (∀ o : Result, Eval Database.empty P' o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty P'.schedule ↔ Diverges Database.empty P.schedule) ∧
    (∀ d e, Reach Database.empty P'.schedule d → Reach Database.empty P.schedule e →
      d.eraseLog.SameMeaning e)
```

The premise `Instrumentable P` is `programOk P = true` (union-free, and no name of `P` has
the `@fire:` prefix; this is exactly when `encode P` is `some`) together with
`Query.VarsKeyed` for every rule query and for the check: every query variable is an
argument of an application pattern. The keyed condition is what the proof needs and no
more: without it a rule `x ⇒ G(x)` or a check `x = y` would bind a variable to a log row in
the instrumented program, which builds `G(fire_i(…))` or succeeds where the original does
not. `Program.WellFormed` and `Program.Fragment` are not premises of the theorem itself;
they are the premises of `encode_instrumentable P hW hP : Instrumentable (Congruence.encode P)`
(`hW` is unused by that proof and kept for the paper's statement).

The state clause uses `Database.eraseLog d := ⟨{q ∈ d.eqs | isLog q.1 = false}, d.subsumed⟩`
(`Provenance/Log.lean`), the e-graph without the log rows. It is stated up to `SameMeaning`
because the instrumented program may run extra saturation passes after the original has
settled (a new log row is a change of meaning), and such a pass can assert a reflexive
equation the original never asserted, for a term the original already holds; the two
states hold the same terms and the same subsumed rows.

## Approach

A simulation between the original `Reach` and the instrumented `Reach`, up to the meaning
of the original state, as in the congruence proof (`PROOF-PORT-S.md`).

### The relation

For an original state `d` and an instrumented state `d'` (`Round.lean`):

- `Good d` (`Good.lean`): every equation is reflexive, and every subsumed row is an
  application the state holds. On such a state `reps = terms`, `live = terms \ subsumed`,
  and two good states have one meaning exactly when they hold the same terms and subsume
  the same rows (`Good.sameMeaning_iff`).
- `Inv P d`: `Good d`, finitely many equations, and every application held is a
  constructor of `P` (`Database.CtorsIn`); hence, with `programOk P`, no held term is a
  log row.
- `Rel P d d'`: `Inv P d`, `d'.subsumed = d.subsumed`, `d.eqs ⊆ d'.eqs`, and every other
  equation of `d'` is a log row `(fire_i(t̄), fire_i(t̄))` whose columns `t̄` are terms of
  `d`. Consequently `d'` is good, its data terms are exactly `d.terms`, and
  `d'.eraseLog = d` (`Rel.eraseLog`).
- `RelC P d d' := ∃ x, d.SameMeaning x ∧ Rel P x d'` (`Simulate.lean`): the partner `x`
  absorbs the extra reflexive equations of the instrumented passes.
- `Shadow d d'` (`Match.lean`): what matching sees of `d'`, the same subsumed rows and the
  same terms apart from log rows; both `Rel` and the intermediate states of an instrumented
  pass provide it.

### Lemma decomposition (`Proofs/Provenance/`)

- `Good.lean`: `IsLog`, `isPrefixOf_fireName`, the good states, their `live`/`reps`/meaning
  characterizations, `Good.runRules`, `Good.round_same` (a round from two good states with
  the same terms and subsumed rows gives two such states), `Reach.contained'`.
- `Match.lean`: `DataName`/`LogFree*` (names outside the log namespace), `Shadow`, keyed
  variables are bound inside live rows (`argVar_matched`, `pattern_argVar_matched`), and the
  matching correspondence `queryMatches_iff`: a keyed query of data names matches in the
  instrumented state under exactly the substitutions it matches in the original.
- `Round.lean`: `programOk` unpacked (`programOk_rule_unionFree`, `programOk_ctors`,
  `logFreeQuery_of_mem`, `logFreeQuery_check`), `Inv` and its preservation and transport
  (`Inv.runRules`, `Inv.reach`, `Inv.round_sameMeaning`, `Inv.reach_transport`), `Rel` and
  its consequences (`Rel.good'`, `Rel.mem_terms`, `Rel.terms_eq`, `Rel.eraseLog`,
  `Rel.sameMeaning_of_inst`), the instrumented head (`fireAction_write`,
  `Action.marks_append`, `encodeRule_writes_marks`: the original's writes plus the log row,
  the original's marks), `InstrRules`, and the round lemma `run_rel`.
- `Simulate.lean`: `Instr` (the instrumented schedule, relationally, since the log index
  depends on the rule's position), `encodeSchedule_instr`, `RelC`, the log bound
  (`Writable`, `LogBound`, `writable_finite`: the rows a pass can write under substitutions
  over a finite set of terms are finitely many), the forward and backward simulation
  statements `Fwd`/`Bwd` (the forward one returns the bound on the new log rows over the
  terms the original reaches), `run_fwd`, the extra passes after the original settles
  (`extra_passes`, by strong induction on the number of writable rows the instrumented
  state lacks; `extra_passes_bwd`), `stable_of_fixpoint`, `sim_fwd`, `sim_bwd`.
- `Diverge.lean`: `Div`, `infinitePasses_fwd`, `trace_bwd`, `not_diverges_after_fixpoint`
  (from `extra_passes`), `sim_div`.
- `Main.lean`: `check_corr` (the check on the final states with subsumption forgotten) and
  `encode_correct`, the three clauses from the empty states.
- `Compiled.lean`: the congruence compiler's output is instrumentable. Generated names
  start with `@` and a letter other than `f` (`dataName_of_second`, `dataName_freshVar`,
  `dataName_congName`) and source names avoid `@` (`dataName_of_not_at`); the constructors
  of compiled queries, heads and maintenance rules are the source's and `@UF`
  (`flat_ctors`, `build_ctors`, `maintenance_ctors`); the variables are the source's, fresh
  ones, or the maintenance rules' (`rule_vars`, `maintenance_vars`); every fresh variable of
  a flattened query is a column of the atom that introduces it (`flat_fresh_argVar`,
  `query_fresh_argVar`) and every source variable is read through a union-find edge
  (`query_argVar_atom` of `Proofs/Congruence/Flatten.lean`), so compiled queries are keyed
  (`keyed_encodeQuery`, `congruence_keyed`; the two union-find rules by `decide`).
- `Provenance/Correctness.lean`: `Correctness`, `theorem correctness`, `correctness_compiled`.

### What the proof reuses

`Proofs/Subsume.lean` (`Cong.iff_eq_and_mem_of_diag`, the `SameRow` lemmas),
`Proofs/DiagonalRound.lean` (`QueryMatches.sameMeaning`, `RunWrites.eq_of_sameMeaning_terms`),
`Proofs/Writes.lean` and `Proofs/Presentation.lean` (`RunRules.eq_pair`,
`Action.writes_append`), `Proofs/Schedule.lean` (`Reach.preserves`, `Reach.transport`),
`Proofs/Finite.lean` (`finite_lists`, `QueryMatches.finite`), `Proofs/Source/Ctors.lean`
(`Database.CtorsInState.runRules`), the generic divergence lemmas of
`Proofs/Congruence/Diverge.lean` (`Diverges.not_reach`), and for the compiled-program
premise the flattening equations of `Proofs/Congruence/Flatten.lean`, the build equations
of `Proofs/Congruence/Writes.lean`, `encode_unionFree` of `Properties.lean`,
`mem_maintenance` and `congruence_query` of `Rules.lean`, `mem_congruence_vars` of
`Firing.lean`, and `encode_schedule`/`encode_check` of `Simulate.lean`.

## Changes outside the proof

- `Provenance/Encode.lean`: the premise `Instrumentable`.
- `Provenance/Log.lean`: `isLog` (an application of a name with the `@fire:` prefix),
  `eraseLog` filters with it instead of `(fireIndex f).isNone`, and `Database.eraseLog`.
  The two tests agree on every name the pass generates and on every name a `programOk`
  program has; the list version changes only on names with the prefix and a non-numeric
  suffix, which no instrumented run holds. `firings`, `rowProofs` and `proofs` still use
  `fireIndex`.
- `EgglogPaper.lean` asserts `assert_no_sorry Egglog.Provenance.correctness`;
  `Makefile` adds `EgglogSemantics.Provenance.Correctness` to `PAPER_MODULES`;
  `paper/semantics.tex` inputs `thm:provenance` in a new `provenance-theorem` prose block
  after the `provenance` block.
- `README.md` and `ENCODING.md` describe the theorem and the premise.

## Validation

- `#print axioms Egglog.Provenance.correctness`:
  `'Egglog.Provenance.correctness' depends on axioms: [propext, Classical.choice, Quot.sound]`
  (likewise `correctness_compiled` and `encode_instrumentable`).
- `make -C semantics lean-check` (with `LAKE="lake --no-cache"`): exit 0. This is the
  build, the proof-hole audit (`lean-holes`), the congruence, provenance, resugar and egg
  gates (104, 104, 104 and 17 cases, no failures), and the certificate check: the exported
  fixtures equal `egglog/tests/lean-certificates.json`, and
  `cargo test -p egglog --test lean_certificates` passed.
- `make -C semantics lean-difftest`: exit 0 (104 passed, 0 failed, 0 skipped).
- `make -C semantics lean-compiled-difftest`: exit 0 (104 passed, 0 failed).
- `make -C semantics paper-check` (with `LAKE="lake --no-cache"`): exit 0; the extracted
  `thm:provenance` node is a theorem with a proof, input by the `provenance-theorem`
  block of `paper/semantics.tex`, and the paper builds without overfull boxes.
- Python and Rust sources are untouched, so the root `make nits` was not run.
