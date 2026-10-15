import EgglogSemantics.Spec.Step

/-! Divergence of the staged semantics. Rule firing remains an atomic `RunRules` step. -/

namespace Egglog

def InfiniteTrace (rel : Database → Database → Prop) (d : Database) : Prop :=
  ∃ trace : Nat → Database, trace 0 = d ∧ ∀ n, rel (trace n) (trace (n + 1))

def MergeDiverges (d : Database) : Prop := InfiniteTrace MergeStep d

def ChangingRunStep (R : RulesetName) (d e : Database) : Prop :=
  RunStep R d e ∧ ¬ d.SameMeaning e

/-- Saturation can diverge between completed rounds or inside a reached merge phase. -/
def SaturateDiverges (R : RulesetName) (d : Database) : Prop :=
  InfiniteTrace (ChangingRunStep R) d ∨
    ∃ mid, Relation.ReflTransGen (ChangingRunStep R) d mid ∧
      MergeDiverges (RunRules R mid)

inductive CmdDiverges (d : Database) : Cmd → Prop where
  | saturate {R : RulesetName} : SaturateDiverges R d → CmdDiverges d (.saturate R)
  | merge {c : Cmd} {mid : Database} :
      (∀ q, c ≠ .check q) → (∀ R, c ≠ .saturate R) →
      cmdReach d c mid → MergeDiverges mid → CmdDiverges d c

/-- A finite command list diverges at a command after a successful finite prefix. -/
inductive ProgramDiverges : Database → Program → Prop where
  | head {d : Database} {c : Cmd} {cs : Program} :
      CmdDiverges d c → ProgramDiverges d (c :: cs)
  | tail {d mid : Database} {c : Cmd} {cs : Program} :
      CmdStep d c mid → ProgramDiverges mid cs → ProgramDiverges d (c :: cs)

end Egglog
