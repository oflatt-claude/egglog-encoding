import EgglogSemantics.Spec.Step

/-! Divergence, used by the Lean statement of compiler correctness. The paper states
nontermination in prose instead. Rule firing remains an atomic `RunRules` step. -/

namespace Egglog

def InfiniteTrace (rel : Database → Database → Prop) (d : Database) : Prop :=
  ∃ trace : Nat → Database, trace 0 = d ∧ ∀ n, rel (trace n) (trace (n + 1))

def MergeDiverges (d : Database) : Prop := InfiniteTrace MergeStep d

/-- A run that changes congruence, so saturation continues past it. -/
def ChangingRunStep (R : RulesetName) (d e : Database) : Prop :=
  RunStep R d e ∧ Cong d ≠ Cong e

/-- Saturation can diverge between rounds or inside a reached merge phase. -/
def SaturateDiverges (R : RulesetName) (d : Database) : Prop :=
  InfiniteTrace (ChangingRunStep R) d ∨
    ∃ mid, Relation.ReflTransGen (ChangingRunStep R) d mid ∧
      MergeDiverges (RunRules R mid)

/-- Only runs and saturations can diverge. -/
inductive CmdDiverges (d : Database) : Cmd → Prop where
  | run {R : RulesetName} : MergeDiverges (RunRules R d) → CmdDiverges d (.run R)
  | saturate {R : RulesetName} : SaturateDiverges R d → CmdDiverges d (.saturate R)

/-- A finite command list diverges at a command after a successful finite prefix. -/
inductive ProgramDiverges : Database → Program → Prop where
  | head {d : Database} {c : Cmd} {cs : Program} :
      CmdDiverges d c → ProgramDiverges d (c :: cs)
  | tail {d mid : Database} {c : Cmd} {cs : Program} :
      CmdStep d c mid → ProgramDiverges mid cs → ProgramDiverges d (c :: cs)

end Egglog
