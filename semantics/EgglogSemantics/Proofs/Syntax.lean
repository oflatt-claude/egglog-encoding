import Mathlib.Data.List.Basic
import EgglogSemantics.Spec.Syntax

namespace Egglog
/-! ### Signatures -/
/-- With `mergeOf` defaulting an undeclared name to `.union`, `AllConstructors` says
exactly that every function is a constructor. This is why "everything up to M8" is
literally the all-constructors case and not merely analogous to it. -/
theorem Signature.mergeOf_eq_union {sig : Signature} (h : sig.AllConstructors)
    (f : FnName) : sig.mergeOf f = MergeSpec.union := by
  unfold Signature.mergeOf
  cases hf : sig f with
  | none => rfl
  | some d => exact h f d hf

namespace Expr
@[simp] theorem vars_lit {l : Lit} : (Expr.lit l).vars = [] := rfl

@[simp] theorem vars_var {v : Var} : (Expr.var v).vars = [v] := rfl

@[simp] theorem vars_app {f : FnName} {args : List Expr} :
    (Expr.app f args).vars = Expr.varsList args := rfl

@[simp] theorem varsList_nil : Expr.varsList ([] : List Expr) = [] := rfl

@[simp] theorem varsList_cons {e : Expr} {es : List Expr} :
    Expr.varsList (e :: es) = e.vars ∪ Expr.varsList es := rfl

/-- A variable of an argument list is a variable of one of its arguments. -/
theorem mem_varsList {v : Var} {es : List Expr} (h : v ∈ Expr.varsList es) :
    ∃ e ∈ es, v ∈ e.vars := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    rw [varsList_cons, List.mem_union_iff] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', hv⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', hv⟩

@[simp] theorem fns_lit {l : Lit} : (Expr.lit l).fns = [] := rfl

@[simp] theorem fns_var {v : Var} : (Expr.var v).fns = [] := rfl

@[simp] theorem fns_app {f : FnName} {args : List Expr} :
    (Expr.app f args).fns = f :: Expr.fnsList args := rfl

@[simp] theorem fnsList_nil : Expr.fnsList ([] : List Expr) = [] := rfl

@[simp] theorem fnsList_cons {e : Expr} {es : List Expr} :
    Expr.fnsList (e :: es) = e.fns ∪ Expr.fnsList es := rfl

/-- A function name of an argument list is a function name of one of its arguments. -/
theorem mem_fnsList {f : FnName} {es : List Expr} (h : f ∈ Expr.fnsList es) :
    ∃ e ∈ es, f ∈ e.fns := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    rw [fnsList_cons, List.mem_union_iff] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', hv⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', hv⟩

end Expr
@[simp] theorem Query.vars_nil : Query.vars [] = [] := rfl

@[simp] theorem Query.vars_cons {p : Pattern} {ps : Query} :
    Query.vars (p :: ps) = p.vars ∪ Query.vars ps := rfl

end Egglog
