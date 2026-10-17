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
@[blueprint "def:divergence"
  (statement := /--
  \[
  \begin{gathered}
  \mathcal I_r(D)\iff\exists(D_n)_{n\in\mathbb N}.\ D_0=D\land\forall n.\ D_n\mathrel r D_{n+1}
  \qquad D\leadsto_R D'\iff D\xrightarrow R D'\land D\not\simeq D'\\
  \operatorname{Div}(\kw{saturate}\ R,D)\iff
    \mathcal I_{\leadsto_R}(D)\lor
    \exists D_0.\ D\leadsto_R^*D_0\land\mathcal I_{\to_m}(\fire_R(D_0))\\
  \operatorname{Div}(C,D)\iff\exists D_0.\ \delta(D,C)=D_0\land\mathcal I_{\to_m}(D_0)
    \quad(\forall R.\ C\ne\kw{saturate}\ R)\\
  \operatorname{Div}(P,D)\iff\exists P_0,C,P_1,D_0.\
    P=P_0;C;P_1\land\langle P_0,D\rangle\Downarrow D_0\land\operatorname{Div}(C,D_0)
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive ProgramDiverges : Database → Program → Prop where
  | head {d : Database} {c : Cmd} {cs : Program} :
      CmdDiverges d c → ProgramDiverges d (c :: cs)
  | tail {d mid : Database} {c : Cmd} {cs : Program} :
      CmdStep d c mid → ProgramDiverges mid cs → ProgramDiverges d (c :: cs)

end Egglog
