import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Spec.Step

/-! The paper's compiler-correctness obligation. Both evaluations use mathematical
`Database` states. No executable interpreter or fuel bound occurs in the statement.
`Proofs/Congruence/AbstractComplete.lean` proves `preservesObservations` against this
contract. `Proofs/Congruence/AbstractTerminationComplete.lean` separately proves
`preservesTermination` and combines them in `preservesFiniteObservations`. -/

namespace Egglog.Congruence

/-- For a well-formed supported source program, every pair of finite evaluations agrees
on success versus check failure. This does not assert either evaluation exists. -/
def PreservesObservations : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ source target : Result,
    Eval Database.empty P source → Eval Database.empty (encode P) target →
      source.succeeded = target.succeeded

/-- A finite source evaluation has a finite compiled evaluation.
A failed check is a finite evaluation even when its unreachable suffix would diverge.
This asserts existence of a finite target run, not termination of every target schedule;
it makes no assertion about source programs without a finite evaluation. -/
def PreservesTermination : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ source : Result,
    Eval Database.empty P source → ∃ target, Eval Database.empty (encode P) target

end Egglog.Congruence
