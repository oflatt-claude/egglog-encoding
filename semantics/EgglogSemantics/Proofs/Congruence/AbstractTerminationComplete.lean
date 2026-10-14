import EgglogSemantics.Proofs.Congruence.AbstractTerminationCommands
import EgglogSemantics.Proofs.Congruence.AbstractSaturationTermination

/-! Mathematical termination preservation and finite observation preservation. -/

namespace Egglog.Congruence.Abstract

/-- Every successful command in a finite source prefix has a finite compiled block. -/
theorem commandsTerminate {P : Program} (hp : P.Fragment) : CommandsTerminate P := by
  intro pre rest c src post d hP hpre htpre hsrc
  have h := boundary_prefix hp hP hpre htpre
  by_cases hsat : ∃ R, c = .saturate R
  · obtain ⟨R, rfl⟩ := hsat
    exact saturate_command_exists hp hP hpre htpre h hsrc
  · exact h.nonSaturate_exists hp hP hpre htpre hsrc
      (fun R he => hsat ⟨R, he⟩)

end Egglog.Congruence.Abstract

namespace Egglog.Congruence

/-- Every finite source evaluation has a finite compiled evaluation. This proves the
original mathematical contract, including failure before an unreachable suffix. -/
theorem preservesTermination : PreservesTermination := by
  intro P _hw hp source hs
  exact Abstract.termination_of_commands hp (Abstract.commandsTerminate hp) hs

/-- A terminating source program has a terminating compiled program with the same
success/failure observation; target termination is now a conclusion. -/
theorem preservesFiniteObservations (P : Program) (hw : P.WellFormed) (hp : P.Fragment)
    (source : Result) (hs : Eval Database.empty P source) :
    ∃ target, Eval Database.empty (encode P) target ∧
      source.succeeded = target.succeeded := by
  obtain ⟨target, ht⟩ := preservesTermination P hw hp source hs
  exact ⟨target, ht, preservesObservations P hw hp source target hs ht⟩

end Egglog.Congruence
