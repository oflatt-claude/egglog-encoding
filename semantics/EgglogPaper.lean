import EgglogSemantics.Spec.Step
import EgglogSemantics.Spec.Divergence
import EgglogSemantics.Spec.Congruence
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Provenance.Log
import EgglogSemantics.Provenance.Checker
import EgglogSemantics.SourceProof.Checker
import EgglogSemantics.Resugar.Lift
import EgglogSemantics.Proofs.Congruence.Main
import EgglogSemantics.Proofs.Provenance.Main
import EgglogSemantics.Proofs.Provenance.Compiled
import EgglogSemantics.Proofs.Provenance.Soundness
import EgglogSemantics.Proofs.SourceProof.Soundness
import EgglogSemantics.Proofs.Resugar.Soundness
import EgglogSemantics.Proofs.SemanticCong
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.OrderFinite
import EgglogSemantics.Proofs.Subsume
import EgglogSemantics.Proofs.InterpSubsume
import EgglogSemantics.Proofs.Provenance.GeneratedSoundness
import Architect
import Mathlib.Util.AssertNoSorry

/-!
# The paper's theorems

Every theorem the paper claims, stated in full in the vocabulary of the specification
(`EgglogSemantics/Spec/`) and of the passes, and proved by one reference into
`EgglogSemantics/Proofs/`. Nothing in the specification or the passes imports a proof.

* Section 4 (semantics): `Spec/Syntax`, `Term`, `Database`, `Congruence`, `Match`, `Eval`,
  `Step` (rounds, schedules, outcomes), `Divergence`, `Behavior`, `Order`.
* Section 5 (congruence pass): `Congruence/Encode` (the pass), `Source/Domain` and
  `Source/WellFormed` (its fragment and well-formedness); proof under `Proofs/Congruence/`.
* Section 6 (proofs): `SourceProof/Format` and `Checker` (proof terms and the checker),
  `Provenance/Encode` and `Log` (instrumentation, proofs read off the firing log),
  `Resugar/Claim`, `Query`, `Lift` (lifting); proofs under `Proofs/Provenance/`,
  `Proofs/SourceProof/`, `Proofs/Resugar/`.

The `@[blueprint "thm:…"]` attributes below carry the paper's statements; `make paper-sync`
writes them into the paper. `assert_no_sorry` fails the build if any theorem's proof is
incomplete, and `#print axioms` on each shows only `propext`, `Classical.choice` and
`Quot.sound`.
-/

namespace Egglog.Paper

/-! ## Section 5: the congruence pass -/

/-- **Congruence pass correctness.** A well-formed source program in the fragment and its
compilation have the same outcome, `ok` or `error`, and the compiled schedule has a
nonterminating execution exactly when the source schedule has one. Both sides run on
mathematical e-graphs from the empty one; no interpreter or fuel bound appears. -/
@[blueprint "thm:congruence"
  (title := /-- Congruence pass correctness -/)
  (statement := /-- Let $P$ be a well-formed program in the source fragment and
  $P\leadsto P'$. Then $\langle P',\emptyset\rangle\Downarrow o\iff
  \langle P,\emptyset\rangle\Downarrow o$ for each outcome $o\in\{\kw{ok},\kw{error}\}$,
  and $P'$ has a nonterminating execution if and only if $P$ has one. -/)
  (proof := /-- By a simulation between the source and the compiled schedules up to the
  meaning of the source state. A source run corresponds to its compiled run followed by the
  rebuild saturation, which terminates and leaves the union-find canonical: every key has
  one live edge, to the representative of its source class, so the compiled queries match
  exactly when the source queries do. A compiled saturation may run further passes after
  the source has settled; they terminate because the related source states keep one meaning
  and build terms of bounded size. -/)
  (latexEnv := "theorem")]
theorem congruence_pass_correct (P : Program) (hW : P.WellFormed) (hF : P.Fragment) :
    (∀ o : Result, Eval Database.empty (Congruence.encode P) o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty (Congruence.encode P).schedule ↔
      Diverges Database.empty P.schedule) :=
  Congruence.encode_correct P hW hF

/-! ## Section 6: proof production -/

/-- **Provenance pass correctness.** Instrumenting a union-free program whose names avoid the
log prefix and whose query and check variables are all arguments of application patterns
(`Provenance.Instrumentable`) changes neither its outcome nor its divergence, and erasing
the `fire` rows from the e-graph the instrumented schedule reaches gives, up to meaning,
the e-graph the original reaches. -/
@[blueprint "thm:provenance"
  (title := /-- Provenance pass correctness -/)
  (statement := /-- Let $P'$ be a union-free program whose names avoid the
  $\mathtt{fire}$ prefix and in which every variable of a rule query or of the check is
  an argument of an application pattern, and let $P''=\operatorname{instrument}(P')$ be its
  instrumentation. Then for each outcome $o\in\{\kw{ok},\kw{error}\}$,
  \[
    \langle P'',\emptyset\rangle\Downarrow o\iff\langle P',\emptyset\rangle\Downarrow o,
  \]
  $P''$ has a nonterminating execution if and only if $P'$ has one, and if
  $\langle P'',\emptyset\rangle\Downarrow G''$ and $\langle P',\emptyset\rangle\Downarrow G'$
  then erasing the $\mathtt{fire}_i$ rows from $G''$ gives an e-graph equivalent to $G'$. -/)
  (proof := /-- By a simulation between the original and the instrumented schedules up to
  the meaning of the original state. An instrumented state is the original state plus log
  rows; no query or check names a log row and every query variable is an argument of an
  application pattern, so the rules fire under the same substitutions, write the same data
  rows and subsume the same rows. An instrumented saturation may run passes after the
  original has settled, since a log row changes the meaning of the state, but they write
  only log rows from a finite set, so they terminate. -/)
  (latexEnv := "theorem")]
theorem provenance_pass_correct {P P' : Program} (hI : Provenance.Instrumentable P)
    (h : Provenance.encode P = some P') :
    (∀ o : Result, Eval Database.empty P' o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty P'.schedule ↔ Diverges Database.empty P.schedule) ∧
    (∀ d e, Reach Database.empty P'.schedule d → Reach Database.empty P.schedule e →
      d.eraseLog.SameMeaning e) :=
  Provenance.encode_correct hI h

/-- **The passes compose.** The congruence pass's output satisfies the provenance pass's
premise (`Provenance.encode_instrumentable`), so the fully compiled program has the source
program's outcome and divergence. -/
theorem passes_compose (P : Program) (hW : P.WellFormed) (hF : P.Fragment) {P'' : Program}
    (h : Provenance.encode (Congruence.encode P) = some P'') :
    (∀ o : Result, Eval Database.empty P'' o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty P''.schedule ↔ Diverges Database.empty P.schedule) := by
  obtain ⟨h₁, h₂⟩ := congruence_pass_correct P hW hF
  obtain ⟨h₃, h₄, -⟩ := provenance_pass_correct (Provenance.encode_instrumentable P hW hF) h
  exact ⟨fun o => (h₃ o).trans (h₁ o), h₄.trans h₂⟩

/-- **Proof checker soundness.** Let `db` be the e-graph a program's schedule reaches, and let
it be closed under every rule the schedule runs (as it is when every run is saturated). A
proof the checker accepts for a claim between two terms of `db` proves an equality that
holds in `db`. -/
theorem checker_sound {P : Program} {db : Database} {pf : SourceProof.Proof}
    {c : SourceProof.Claim} (hs : Reach Database.empty P.schedule db)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs db) (h : SourceProof.check P pf = some c)
    (hl : c.lhs ∈ db.terms) (hr : c.rhs ∈ db.terms) : Cong db c.lhs c.rhs :=
  (SourceProof.check_sound hs (hs.wf Database.WF.empty) hclosed h hl hr).toCong

/-- **Proofs read off the log are checked.** Every proof `Provenance.proofs` reconstructs
from the firing log of an instrumented program is accepted by the checker for that program,
with the row it was reconstructed for as its claim. -/
theorem log_proofs_checked {P : Program} {terms : List Term} {facts : Provenance.Facts}
    (h : Provenance.proofs P terms = some facts) :
    ∀ tp ∈ facts, Provenance.check P tp.2 = some tp.1 :=
  Provenance.proofs_checked h

/-- **Lifted proofs are checked.** Every proof lifted back to a source program is accepted by
the source checker with its own claim. -/
theorem lifted_proofs_checked {P : Program} {terms : List Term}
    {outputs : List SourceProof.Proof} (h : Resugar.sourceProofs P terms = some outputs) :
    ∀ output ∈ outputs, SourceProof.check P output = some output.claim :=
  Resugar.sourceProofs_checked h

/-- **Lifted proofs are sound.** By the two theorems above, a lifted proof's claim between
terms of the saturated source e-graph holds there. -/
theorem lifted_proofs_sound {P : Program} {db : Database} {terms : List Term}
    {outputs : List SourceProof.Proof} (hs : Reach Database.empty P.schedule db)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs db)
    (h : Resugar.sourceProofs P terms = some outputs) :
    ∀ output ∈ outputs, output.claim.lhs ∈ db.terms → output.claim.rhs ∈ db.terms →
      Cong db output.claim.lhs output.claim.rhs :=
  fun output ho hl hr => checker_sound hs hclosed (lifted_proofs_checked h output ho) hl hr

end Egglog.Paper

/-! ## No holes

The build fails if any theorem above, or any supporting result the paper relies on, has an
incomplete proof. -/

assert_no_sorry Egglog.Paper.congruence_pass_correct
assert_no_sorry Egglog.Paper.provenance_pass_correct
assert_no_sorry Egglog.Paper.passes_compose
assert_no_sorry Egglog.Paper.checker_sound
assert_no_sorry Egglog.Paper.log_proofs_checked
assert_no_sorry Egglog.Paper.lifted_proofs_checked
assert_no_sorry Egglog.Paper.lifted_proofs_sound

-- Supporting results. The term order the compiled rebuilding uses, and the representatives
-- it picks.
assert_no_sorry Egglog.Term.blt_admissible
assert_no_sorry Egglog.Database.reps_subset_terms

-- Matching, subsumption, rounds, schedules, and evaluation agree with their presentations
-- and are deterministic.
assert_no_sorry Egglog.queryHolds_iff_validQuerySubst
assert_no_sorry Egglog.RunRules.eq_pair
assert_no_sorry Egglog.RunMarks.eq_empty
assert_no_sorry Egglog.RunRules.eq_addEqs
assert_no_sorry Egglog.RunRules.eq_sUnion
assert_no_sorry Egglog.RunRules.wf
assert_no_sorry Egglog.Reach.det
assert_no_sorry Egglog.Eval.det
assert_no_sorry Egglog.SourceMeaning.completion_closed_of_saturated

-- The reference interpreter refines the specification, up to meaning, for subsume-free
-- programs and for union-free programs with subsumption (the compiler's output), and
-- decides the final check as the specification does.
assert_no_sorry Egglog.patternHolds_iff
assert_no_sorry Egglog.FDatabase.holds_iff_queryHolds
assert_no_sorry Egglog.exec_programStep
assert_no_sorry Egglog.exec_complete
assert_no_sorry Egglog.observe_eval
assert_no_sorry Egglog.exec_programStep_noUnions
assert_no_sorry Egglog.exec_complete_noUnions
assert_no_sorry Egglog.observe_eval_noUnions
assert_no_sorry Egglog.Congruence.exec_encode_programStep

-- Certificates in the stronger, inferred form, and the generated union-find rows.
assert_no_sorry Egglog.SourceProof.check_infers
assert_no_sorry Egglog.Provenance.Generated.check_uf_infers
assert_no_sorry Egglog.Resugar.sourceProofs_infers
assert_no_sorry Egglog.Resugar.certificates_infers
