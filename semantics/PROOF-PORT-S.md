# Task S: congruence pass correctness

## Scope

Prove `Egglog.Congruence.Correctness` (`Congruence/Correctness.lean`) for the
view-free union-find encoding: for a well-formed program `P` in the source fragment,
`encode P` has the same finite outcomes as `P` from the empty state and diverges exactly
when `P` does. The development lives under `Proofs/Congruence/` and the theorem
`Egglog.Congruence.correctness : Correctness` carries the paper's `thm:congruence`
blueprint node. Afterwards the leftovers of the former merge-function encoding are
removed (see "Cleanup" below).

## Approach

A simulation between the source `Reach` and the compiled `Reach`, up to source meaning.
One source `run R` corresponds to the compiled `run R'` followed by the rebuild
saturation `saturate (run M_P)` (`encS`, `Simulate.lean`); sequences and saturations
correspond structurally (`encode_schedule`).

### The target state

For a compiled state `d` (always union-free, so `Cong d` is equality on `d.terms`):

- `Row d k p`: the reflexive pair of `@UF(k, p)` is asserted (live or stale);
  `Keys d` are the terms with a row; `Edge d k p` (from `Read.lean`) is the live row.
- `view d`: the rows read as equations; `liveView d`: the live rows read as equations.

### The simulation relation (`Rel src d`, `Invariant.lean`)

1. `d` is diagonal and every equation is the reflexive pair of a union-find row; every
   mark is a row (`diag`, `ufOnly`, `marks`).
2. `Keys d = src.terms`: the source terms are exactly the union-find keys (`keys`), and
   no source term mentions `@UF` (`avoids`).
3. `Cong src a b ↔ Cong (view d) a b`: the union-find, read as equations, generates
   exactly the source congruence (`cong`).
4. Every row `(k, p)` is in the congruence closure of the live rows (`liveCong`), so
   stale rows carry no information.
5. Edges go down the term order: `Row d k p → p = k ∨ p ≺ k` (`down`).
6. A stale row `(k, p)` has a witness `q ≺ p` with rows `(k, q)` and `(p, q)` (`marks`);
   hence the least parent of every key is live (`Rel.least_parent`).
7. Every endpoint of a row has a self-loop row (`selfLoop`).
8. `d.eqs` is finite (`finite`); `src.subsumed = ∅` (`srcSubsumed`).

`Canon d` (the rebuild fixpoint): every key has exactly one live edge, to a root, and two
applications of one constructor whose children have the same live parents have the same
live parent. At `Rel src d` with `Canon d` and a well-formed `src`, the live edge of a
key goes to the representative of its source class (`Rel.edge_iff_rep`).

### Lemma decomposition (`Proofs/Congruence/`)

- `Target.lean`: `Row`, `Keys`, `UfOnly`, `EndsFree`, `view`, `liveView`; an edge is a
  live row (`edge_iff`); membership and liveness of `@UF` rows and of source-shaped
  terms in a diagonal state.
- `Invariant.lean`: `Rel`, `Canon`, the strict order instance for `Term.blt`, `root`;
  the least live parent, roots are source representatives (`Rel.repr_root`,
  `Rel.repr_unique`, `Rel.edge_iff_rep`, `Rel.root_eq_of_cong`).
- `Atoms.lean`: inversion lemmas for matching one compiled atom (`matches_uf_iff`,
  `matches_eq_iff`, `matches_ne_iff`, `matches_eq_min_iff`, ...).
- `Rules.lean`: the maintenance rule list (`maintenance`, `rebuild_eq`) and the
  inversion of a firing of each maintenance rule (`compress_inv`, `collide_inv`,
  `congruence_inv`) with its writes and marks.
- `Maintenance.lean`: a round of `M_P` preserves `Rel` (`maint_round`): new rows are
  derivable from the old live rows (`MaintRow`), and the live-closure field by
  well-founded induction on the parent in the term order over the finite key set.
- `Firing.lean`: the environments under which the maintenance rules fire
  (`compress_fire`, `collide_fire`, `congruence_fire`).
- `Fixpoint.lean`: a round of `M_P` with the same meaning leaves the state canonical
  (`canon_of_fixpoint`); the rebuild saturation exists (`rebuild_exists`, by the rank
  of rows and marks missing from the finite key square, `rank_lt`) and preserves the
  relation (`rebuild_rel`).
- `Flatten.lean`: equations for query flattening, fresh variables (`FreshIn`,
  `NotFresh`), the variables of a flattened query (`query_vars_iff`), and every keyed
  source variable is the second column of a `@UF` atom (`query_argVar_atom`).
- `Sound.lean`: a compiled match reads source facts (`Reads`, `sound_expr`,
  `sound_pattern`, `sound_query`).
- `Complete.lean`: a source match extends to the fresh variables at a canonical state
  (`srep`, `Fresh`, `complete_expr`, `complete_args`).
- `QueryCorr.lean`: `QueryOk`; the query correspondence at a canonical state
  (`fire_complete`, `fire_sound`) through `restrict`.
- `Writes.lean`: the terms a compiled construction writes (`BuildTerm`, `build_writes`,
  `buildArgs_writes`).
- `Round.lean`: the compiled head writes (`HeadWrites`), `RuleOk`, the firing
  correspondence (`Firing`, `firing_of_compiled`, `firing_of_source`), and `Rel` after a
  source run and its compiled run (`run_rel`).
- `Vocab.lean`: the literal and constructor vocabulary of a program and the size bound
  on the terms a round builds (`RunRules.vocab`, `RunRules.nodeSize_le`).
- `Source.lean`: the source-side invariant (`SrcInv`: well-formed, no marks, finite,
  constructors and literals of `P`, ...), its preservation by rounds (`Rounds`), the
  fragment gives `RuleOk` (`ruleOk_of_fragment`), rounds preserve or change meaning
  (`round_sameMeaning`, `reach_transport`), and the bounded term universe
  (`terms_bounded`).
- `Simulate.lean`: `encS`, `encode_schedule`, `encode_check`; `RelC` (`Rel` up to
  source meaning); forward (`sim_fwd`) and backward (`sim_bwd`) simulation of
  schedules, with the extra compiled passes after a source fixpoint terminating because
  every term stays in a finite vocabulary-and-size universe (`bounded_universe`,
  `extra_passes`, `extra_passes_bwd`).
- `Diverge.lean`: divergence corresponds (`sim_div`): a diverging trace on one side is
  transported step by step to the other (`infinitePasses_fwd`, `trace_bwd`), and a
  saturation that terminates on one side terminates on the other
  (`not_diverges_after_fixpoint`).
- `Check.lean`: the compiled check on the final state with subsumption forgotten holds
  exactly when the source check holds (`check_corr`; compiled queries are monotone,
  `query_monotone`, `queryMatches_forget`).
- `Main.lean`: the empty states are related (`rel_empty`, `canon_empty`) and the theorem
  `encode_correct`, assembled from `fwd_relC`/`bwd_relC`, `check_corr`,
  `SourceMeaning.queryHolds_iff` and `sim_div`.
- `Congruence/Correctness.lean`: `theorem correctness : Correctness := fun P hW hP => encode_correct P hW hP`.

## Statement changes

- `Correctness` stays a `def ... : Prop`. The `thm:congruence` blueprint node moved from
  the definition to `theorem correctness : Correctness`; the label, title, statement text
  and `latexEnv := "theorem"` are unchanged, `hasProof := false` is dropped, and a
  `proof` docstring sketches the simulation.
- `EgglogPaper.lean` asserts `assert_no_sorry Egglog.Congruence.correctness`.
- The well-formedness premise `P.WellFormed` is not used by the proof; the fragment
  conditions (`P.Fragment`) carry the argument. The premise stays in the statement.
- No change to the compiler, the specification, or the existing proof modules.

## Cleanup

The leftovers of the former merge-function encoding were removed by declaration use. A
Lean script, run with `lake env lean` against the built library, computed the closure of
the roots under `Lean.Expr.getUsedConstants`: every declaration of a project module
outside `EgglogSemantics.Proofs.*` and `EgglogSemantics.Congruence.*` (the specification,
the interpreter, the source fragment, provenance, resugaring, `Tests/*`, `DiffTest.lean`,
`EgglogPaper.lean`), every `@[blueprint]` node with its explicit `uses`, and every
`assert_no_sorry` name of `EgglogPaper.lean`. Every primary declaration of the two
namespaces outside the closure was deleted, whole modules where every declaration was
unreachable:

- 13 modules, 936 lines: `Proofs/Merge.lean`, `Proofs/Entries.lean`,
  `Proofs/Assignments.lean`, `Proofs/Execution.lean`, `Proofs/MatchingCounterexamples.lean`,
  `Proofs/ActionMonotone.lean`, `Proofs/ActionProgram.lean`, `Proofs/Behavior.lean`,
  `Proofs/LiveTables.lean`, `Proofs/Setup.lean`, `Proofs/Source/FreshEnv.lean`,
  `Proofs/Source/Termination.lean`, `Proofs/SourceProof/Ledger.lean`;
- 435 declarations in 71 modules, including the option-free wrappers of
  `Congruence/Encode.lean` (`encodeRule`, `encodeSchedule`, `rebuild`, ...), the
  alternative statements `PreservesBehaviors`, `PreservesObservations` and
  `PreservesTermination` of `Congruence/Correctness.lean`, `Id` and `SameClass` of
  `Congruence/Read.lean`, and the helper lemmas of the new proof modules that the final
  proof did not use.

The two lemmas of `Merge.lean` the compiler proof uses were relocated:
`Conservativity.cong_replay` is `Cong.replay` in `Proofs/SemanticCong.lean`, and
`Database.mem_terms_of_eqs` is in `Proofs/Database.lean`. The historical names of
`Proofs/Lookup.lean` were renamed: its lemmas are about the pair
`e.eval σ = some t ∧ Expr.Matches db σ e`, so `Lookup.exists_cong`, `Lookup.of_eval`,
`Lookup.of_agreeOn`, `Lookup.mono_live` and `Lookup.transport` are
`Expr.Matches.eval_cong`, `Expr.Matches.of_eval`, `Expr.Matches.of_agreeOn`,
`Expr.Matches.mono_live` and `Expr.Matches.transport` (with `Expr.MatchesList.*` for the
list forms), `Expr.rows_agreeOn` is `Expr.matches_agreeOn`, and the module is
`Proofs/MatchEval.lean`; `Proofs/InterpLookup.lean`, the executable matcher against
`Matches`, is `Proofs/InterpMatch.lean`.

Four kinds of use are invisible to the constant closure, and the declarations they
concern stay: `@[simp]` lemmas proved by `rfl` and `rfl`-lemmas named in `simp only`
lists, which `simp` rewrites with definitionally and which therefore leave no trace in a
proof term (53 lemmas, such as `Database.addSubsumed_subsumed`, `Term.subtermList_app`,
`Expr.fns_app`); declarations used only by `example` and `#guard` commands in the tests
(`Congruence.encodeQuery`, `Relational.exec`, `StoredCong.mem_right`); the two `Coe`
instances of `Proofs/StoredCong.lean`, which elaboration unfolds; and the dead member of a
`mutual` block whose partner is used (39 lemmas, such as `Expr.MatchesList.mono_live`),
since the partner's source recurses through it. `Proofs/Provenance/Counterexamples.lean`
and `Proofs/SourceProof/Counterexamples.lean` are outside the closure as well; they document
the current provenance and source-proof checkers through `#guard` commands and stay.
Derived `Repr` and `DecidableEq` instances of `Congruence/Encode.lean` are kept with their
types.

## Validation

- `#print axioms Egglog.Congruence.correctness`:
  `'Egglog.Congruence.correctness' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `make -C semantics lean-check` (with `LAKE="lake --no-cache"`): exit 0. This is the
  build, the proof-hole audit (`lean-holes`), the congruence, provenance, resugar and egg
  gates, and the certificate check: the exported fixtures equal
  `egglog/tests/lean-certificates.json`, and `cargo test -p egglog --test lean_certificates`
  passed.
- `make -C semantics lean-difftest`: exit 0 (104 passed, 0 failed, 0 skipped).
- `make -C semantics lean-compiled-difftest`: exit 0 (104 passed, 0 failed).
- `make -C semantics paper-check` (with `LAKE="lake --no-cache"`): exit 0; the extracted
  `thm:congruence` node is a theorem with a proof.
- The dead-declaration analysis on the final tree reports 118 declarations of the two
  namespaces outside the closure, all of them in the kept categories above (53 `rfl`
  simp lemmas, 39 members of `mutual` blocks with a used partner, 13 declarations of the
  two counterexample modules, 7 derived or `where`-nested declarations, 3 declarations
  used by `example` or `#guard` in the tests, 2 `Coe` instances, and `encodeActions_nil`,
  an `rfl`-lemma named in a `simp` list).
- Python and Rust sources are untouched, so the root `make nits` was not run.
