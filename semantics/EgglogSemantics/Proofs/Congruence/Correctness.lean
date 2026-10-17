import EgglogSemantics.Proofs.Congruence.AbstractTerminationComplete
import EgglogSemantics.Proofs.Congruence.LiveProgramTermination
import EgglogSemantics.Proofs.Behavior

/-! Top-level congruence compiler correctness: success, check failure, and divergence. -/

namespace Egglog.Congruence

/-- All success, failure, and divergence behaviors agree, without evaluation premises. -/
@[blueprint "thm:congruence"
  (title := /-- Congruence compiler correctness -/)
  (statement := /-- For every well-formed program $P$ in the supported constructor
  source fragment with no saturation commands, and every observation $b$,
  \[\operatorname{Behaves}(\varnothing,\operatorname{encode}(P),b)
    \quad\Longleftrightarrow\quad\operatorname{Behaves}(\varnothing,P,b).\]
  Neither side's termination is a premise. The compiled program may saturate its
  rebuilding rules; no such generated rebuilding or merge schedule diverges. -/)
  (hasProof := false) (latexEnv := "theorem")]
theorem preservesBehaviors : PreservesBehaviors := by
  intro P hw hp hn behavior
  cases behavior with
  | success =>
      rw [behaves_success_iff, behaves_success_iff]
      exact observations_iff P hw hp hn true
  | checkFailed =>
      rw [behaves_failure_iff, behaves_failure_iff]
      exact observations_iff P hw hp hn false
  | diverges =>
      exact ⟨fun h => (not_encode_diverges hp hn h).elim,
        fun h => (not_programDiverges_of_allConstructors
          Database.CtorState.empty.sig hp.ctorsOnly hn h).elim⟩

/-- Bounded source schedules and every compiled merge/rebuild schedule are nondivergent. -/
theorem neither_diverges {P : Program} (hp : P.Fragment) (hn : P.NoSaturate) :
    ¬ ProgramDiverges Database.empty P ∧ ¬ ProgramDiverges Database.empty (encode P) :=
  ⟨not_programDiverges_of_allConstructors Database.CtorState.empty.sig hp.ctorsOnly hn,
    not_encode_diverges hp hn⟩

end Egglog.Congruence
