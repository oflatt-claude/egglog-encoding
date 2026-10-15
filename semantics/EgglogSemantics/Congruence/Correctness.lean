import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Spec.Step

/-! The paper's compiler-correctness obligation. Both evaluations use mathematical
`Database` states. No executable interpreter or fuel bound occurs in the statement.
`Proofs/Congruence/AbstractComplete.lean` proves `preservesObservations` against this
contract. The paper's source programs use bounded rounds; only compiled rebuilding
uses saturation. -/

namespace Egglog.Congruence

/-- For a well-formed supported source program, every pair of finite evaluations agrees
on success versus check failure. This does not assert either evaluation exists. -/
def PreservesObservations : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ source target : Result,
    Eval Database.empty P source → Eval Database.empty (encode P) target →
      source.succeeded = target.succeeded

/-- Bounded source schedules have finite compiled evaluations. Generated rebuilding
may saturate; this asserts existence, not termination of every merge schedule. -/
def PreservesTermination : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → P.NoSaturate → ∀ source : Result,
    Eval Database.empty P source → ∃ target, Eval Database.empty (encode P) target

end Egglog.Congruence
