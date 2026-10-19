import EgglogSemantics.Spec.Behavior
import EgglogSemantics.Proofs.Query
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Proofs.Step

namespace Egglog

mutual

/-- The checked constructor evaluator agrees with structural evaluation. -/
theorem Expr.eval_eq_evaluate {sig : Signature} {σ : Env} (e : Expr)
    (hf : e.Evaluable sig) : e.eval sig σ = e.evaluate σ := by
  match e with
  | .lit _ | .var _ => rfl
  | .app f args =>
    have hc := hf f (by simp [Expr.fns])
    have ha := Expr.evalList_eq_evaluateList (σ := σ) args
      (fun g hg => hf g (by simp [Expr.fns, hg]))
    simp only [Expr.eval, Expr.evaluate, if_pos hc, ha]
  | .min a b =>
    have ha := Expr.eval_eq_evaluate (σ := σ) a (fun g hg => hf g (by simp [Expr.fns, hg]))
    have hb := Expr.eval_eq_evaluate (σ := σ) b (fun g hg => hf g (by simp [Expr.fns, hg]))
    simp only [Expr.eval, Expr.evaluate, ha, hb]
  | .ite lhs rhs yes no =>
    have hl := Expr.evalList_eq_evaluateList (σ := σ) lhs
      (fun g hg => hf g (by simp [Expr.fns, hg]))
    have hr := Expr.evalList_eq_evaluateList (σ := σ) rhs
      (fun g hg => hf g (by simp [Expr.fns, hg]))
    have hy := Expr.eval_eq_evaluate (σ := σ) yes (fun g hg => hf g (by simp [Expr.fns, hg]))
    have hn := Expr.eval_eq_evaluate (σ := σ) no (fun g hg => hf g (by simp [Expr.fns, hg]))
    simp only [Expr.eval, Expr.evaluate, hl, hr, hy, hn]

theorem Expr.evalList_eq_evaluateList {sig : Signature} {σ : Env} (es : List Expr)
    (hf : ∀ f ∈ Expr.fnsList es, sig.IsCtor f) :
    Expr.evalList sig es σ = Expr.evaluateList es σ := by
  match es with
  | [] => rfl
  | e :: es =>
    have he := Expr.eval_eq_evaluate (σ := σ) e (fun g hg => hf g (by simp [Expr.fnsList, hg]))
    have hs := Expr.evalList_eq_evaluateList (σ := σ) es
      (fun g hg => hf g (by simp [Expr.fnsList, hg]))
    simp only [Expr.evalList, Expr.evaluateList, he, hs]

end

/-- Complete rows use the same evaluator when declarations, widths, and nesting are valid. -/
theorem Expr.evalAtom_eq_evaluate {sig : Signature} {σ : Env} (e : Expr)
    (hf : e.AtomEvaluable sig) (hw : e.AtomWidthOk sig) :
    e.evalAtom sig σ = e.evaluate σ := by
  match e with
  | .lit _ | .var _ => rfl
  | .app f cols =>
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hf.1
    rw [Expr.evalAtom_app_decl hd (Or.inr (hw.1 d hd)),
      Expr.evaluate, Expr.evalList_eq_evaluateList cols hf.2]
  | .min a b =>
    exact Expr.eval_eq_evaluate (.min a b) hf
  | .ite lhs rhs yes no =>
    have hl := Expr.evalList_eq_evaluateList (σ := σ) lhs (fun g hg => by
      obtain ⟨e, he, hg⟩ := Expr.mem_fnsList hg
      exact hf.1 e (List.mem_append_left _ he) g hg)
    have hr := Expr.evalList_eq_evaluateList (σ := σ) rhs (fun g hg => by
      obtain ⟨e, he, hg⟩ := Expr.mem_fnsList hg
      exact hf.1 e (List.mem_append_right _ he) g hg)
    have hy := Expr.evalAtom_eq_evaluate (σ := σ) yes hf.2.1 hw.2.2.1
    have hn := Expr.evalAtom_eq_evaluate (σ := σ) no hf.2.2 hw.2.2.2
    simp only [Expr.evalAtom, Expr.evaluate, hl, hr, hy, hn]

/-- The paper treats one action as a singleton sequence of actions. -/
theorem Action.writes_singleton (sig : Signature) (σ : Env) (a : Action) :
    Action.writes sig σ [a] = (a.write sig σ).map (fun p => {p}) := by
  cases h : a.write sig σ <;> simp [Action.writes, h]

/-- Concatenating action sequences unions their writes. -/
theorem Action.writes_append (sig : Signature) (σ : Env) (as bs : List Action) :
    Action.writes sig σ (as ++ bs) =
      (Action.writes sig σ as).bind fun A =>
        (Action.writes sig σ bs).map fun B => A ∪ B := by
  induction as with
  | nil => simp [Action.writes]
  | cons a as ih =>
    simp only [List.cons_append, Action.writes, ih]
    cases a.write sig σ <;>
      cases Action.writes sig σ as <;>
      cases Action.writes sig σ bs <;>
      simp [Set.insert_union]

/-- Successful execution preserves the environment at every command boundary. -/
theorem Eval.env {db d : Database} {P : Program} (h : Eval db P (.ok d)) :
    d.env = db.env := (Eval.ok_iff.mp h).env

theorem Eval.empty_env {d : Database} {P : Program} (h : Eval Database.empty P (.ok d)) :
    d.env = [] := h.env

end Egglog
