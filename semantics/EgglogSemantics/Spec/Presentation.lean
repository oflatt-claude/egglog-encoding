import EgglogSemantics.Spec.Behavior

namespace Egglog

/-- Actions take an explicit substitution and restore the surrounding environment. -/
@[blueprint "def:actions"
  (statement := /--
\[
  \ir{Add}{\aval e=t}{D,\sigma\vdash e\Downarrow D+(t,t)}\quad
  \ir{Union}{\eval{e_1}=s\\\eval{e_2}=t}
    {D,\sigma\vdash\kw{union}(e_1,e_2)\Downarrow D+(s,t)}\quad
  \ir{Empty}{}{D,\sigma\vdash\epsilon\Downarrow D}\quad
  \ir{Sequence}{D,\sigma\vdash h\Downarrow D_1\\D_1,\sigma\vdash H\Downarrow D_2}
    {D,\sigma\vdash h;H\Downarrow D_2}
  \]
  -/)
  (latexEnv := "paperfragment")]
def ActionsEval (db : Database) (σ : Env) (as : List Action) (db' : Database) : Prop :=
  ∃ d, evalActions { db with env := σ } as = some d ∧ db' = { d with env := db.env }

end Egglog
