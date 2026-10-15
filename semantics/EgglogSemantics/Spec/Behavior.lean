import EgglogSemantics.Spec.Divergence

namespace Egglog

inductive Behavior where
  | success
  | checkFailed
  | diverges

/-- Finite outcomes and infinite execution, observed without exposing the final store. -/
def Behaves (db : Database) (P : Program) : Behavior → Prop
  | .success => ∃ d, Eval db P (.ok d)
  | .checkFailed => Eval db P .checkFailed
  | .diverges => ProgramDiverges db P

end Egglog
