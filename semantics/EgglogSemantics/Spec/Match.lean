import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import EgglogSemantics.Spec.Eval

/-!
# Substitutions

The vocabulary e-matching is stated in: which variables a pattern leaves for the matcher
to assign, how the substitutions of several patterns are joined, and what it means for one
to be well formed against a database.

The matching relation itself is `Spec/Merge.lean`'s `MValidSubst`, since a pattern matches
up to `MCong`. It is declarative rather than a search procedure: a substitution matches
when the pattern's *instance* is provably equal to some **witness** the database already
holds. Enumerating those substitutions is the executable layer's job —
`Impl/Interp.lean`'s `matchQuery`.
-/

namespace Egglog
mutual

/-- The variables of `e` not already bound in `σ`.

A pattern variable that *is* bound in `σ` is not a match variable — it denotes its
value. That is how egglog treats a global variable appearing in a rule body. -/
def Expr.freeVars : Expr → Env → List Var
  | .lit _, _ => []
  | .var v, σ => if (Env.lookup v σ).isSome then [] else [v]
  | .app _ args, σ => Expr.freeVarsList args σ

/-- `Expr.freeVars` over an argument list, deduplicated. -/
def Expr.freeVarsList : List Expr → Env → List Var
  | [], _ => []
  | e :: es, σ => e.freeVars σ ∪ Expr.freeVarsList es σ

end

def Pattern.freeVars : Pattern → Env → List Var
  | .expr e, σ => e.freeVars σ
  | .eq e₁ e₂, σ => e₁.freeVars σ ∪ e₂.freeVars σ
  | .values vs _ as, σ => Expr.freeVarsList vs σ ∪ Expr.freeVarsList as σ

namespace Env
/-- Append, requiring the two to agree wherever both bind.

`σ₁`'s bindings are kept even when `σ₂` has them too, so the result can bind a variable
twice — always to the same term, so `lookup` cannot tell. -/
def Union2 (σ₁ σ₂ σ : Env) : Prop :=
  (∀ b ∈ σ₁, ∀ t, lookup b.1 σ₂ = some t → b.2 = t) ∧ σ = σ₁ ++ σ₂

/-- The left fold of `Union2`, which fails if any step does. -/
inductive UnionAll : List Env → Env → Prop where
  | nil : UnionAll [] []
  | single (σ : Env) : UnionAll [σ] σ
  | step {σ₁ σ₂ σr σ : Env} {σs : List Env} :
      Union2 σ₁ σ₂ σr → UnionAll (σr :: σs) σ → UnionAll (σ₁ :: σ₂ :: σs) σ

end Env
/-! ### Well-formed substitutions -/
/-- `σ` binds exactly `vars`, each to a term the database holds. `Perm` rather than
equality, so the definition does not depend on the order `Expr.freeVars` happens to
produce; substitutions differing only by a permutation are indistinguishable to
`lookup`. -/
def ValidEnv (vars : List Var) (db : Database) (σ : Env) : Prop :=
  (Env.dom σ).Perm vars ∧ ∀ b ∈ σ, b.2 ∈ db.terms

end Egglog
