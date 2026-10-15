import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Spec.Behavior

/-! The paper's compiler-correctness obligation. Both evaluations use mathematical
`Database` states. No executable interpreter or fuel bound occurs in the statement.
`Proofs/Congruence/AbstractBehaviorComplete.lean` proves `preservesBehaviors`.
The paper's source programs use bounded rounds; only compiled rebuilding
uses saturation. -/

namespace Egglog.Congruence

/-- Compilation preserves success, failed checks, and divergence. Neither side's
termination is a premise; source schedules use bounded rounds. -/
def PreservesBehaviors : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → P.NoSaturate → ∀ behavior : Behavior,
    Behaves Database.empty (encode P) behavior ↔ Behaves Database.empty P behavior

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
