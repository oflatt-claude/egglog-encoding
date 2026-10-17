import EgglogSemantics.Spec.Presentation
import EgglogSemantics.Proofs.Query
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Proofs.Step

namespace Egglog

theorem ActionsEval.env {db db' : Database} {σ : Env} {as : List Action}
    (h : ActionsEval db σ as db') : db'.env = db.env := by
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- At command boundaries, the explicit-substitution judgment is the original evaluator. -/
theorem actionsEval_iff_evalLocalActions {db db' : Database} {σ : Env} {as : List Action}
    (h : db.env = []) :
    ActionsEval db σ as db' ↔ evalLocalActions db as σ = some db' := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hr := evalActions_rules hd
    simp only [evalLocalActions, h, List.append_nil, hd, Option.map_some, Option.some.injEq]
    have hr : d.rules = db.rules := hr
    simp only [hr]
  · intro he
    obtain ⟨d, hd, rfl⟩ := evalLocalActions_eq_some he
    have hr := evalActions_rules hd
    change d.rules = db.rules at hr
    refine ⟨d, ?_, ?_⟩
    · simpa only [h, List.append_nil] using hd
    · simp only [hr]

/-- Paper rule instances yield exactly the same database contributions. -/
theorem mem_ruleResults_iff_actionsEval {db d : Database} {r : Rule} (h : db.env = []) :
    d ∈ RuleResults db r ↔ ∃ σ, QueryMatches db r.query σ ∧ ActionsEval db σ r.actions d := by
  rw [mem_ruleResults_iff_queryMatches]
  simp only [actionsEval_iff_evalLocalActions h]

/-- Successful execution preserves the environment at every command boundary. -/
theorem Eval.env {db d : Database} {P : Program} (h : Eval db P (.ok d)) :
    d.env = db.env := (Eval.ok_iff.mp h).env

theorem Eval.empty_env {d : Database} {P : Program} (h : Eval Database.empty P (.ok d)) :
    d.env = [] := h.env

end Egglog
