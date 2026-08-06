import EgglogSemantics.Spec.Syntax

namespace Egglog
namespace Expr
@[simp] theorem vars_lit {l : Lit} : (Expr.lit l).vars = [] := rfl

@[simp] theorem vars_var {v : Var} : (Expr.var v).vars = [v] := rfl

@[simp] theorem vars_app {f : FnName} {args : List Expr} :
    (Expr.app f args).vars = Expr.varsList args := rfl

@[simp] theorem varsList_nil : Expr.varsList ([] : List Expr) = [] := rfl

@[simp] theorem varsList_cons {e : Expr} {es : List Expr} :
    Expr.varsList (e :: es) = e.vars ∪ Expr.varsList es := rfl

end Expr
@[simp] theorem Query.vars_nil : Query.vars [] = [] := rfl

@[simp] theorem Query.vars_cons {p : Pattern} {ps : Query} :
    Query.vars (p :: ps) = p.vars ∪ Query.vars ps := rfl

end Egglog
