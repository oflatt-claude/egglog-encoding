import EgglogSemantics.Proofs.Congruence.AbstractTerminationComplete
import EgglogSemantics.Proofs.Congruence.LiveProgramTermination
import EgglogSemantics.Proofs.Behavior

namespace Egglog.Congruence

/-- All success, failure, and divergence behaviors agree, without evaluation premises. -/
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
