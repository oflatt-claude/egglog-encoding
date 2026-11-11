import EgglogSemantics.Proofs.Match

/-! Keyed, order-free queries and held bindings. -/

namespace Egglog

theorem Expr.var_mem_varsList {v : Var} :
    ∀ {es : List Expr}, Expr.var v ∈ es → v ∈ Expr.varsList es
  | [], h => by simp at h
  | e :: es, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp [Expr.varsList, Expr.vars]
      · exact List.mem_union_iff.mpr (Or.inr (Expr.var_mem_varsList h))

end Egglog
