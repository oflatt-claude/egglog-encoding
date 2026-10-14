import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import EgglogSemantics.Spec.Eval

/-!
# E-matching

Which variables a pattern leaves for the matcher to assign, how the substitutions of
several patterns are joined, when one is well formed against a database, and the matching
relation itself. What a match *does* is `Spec/Step.lean`'s `RuleResults`.
-/

namespace Egglog
mutual

/-- The variables of `e` not already bound in `σ`. A pattern variable that *is* bound in
`σ` is not a match variable: it denotes its value. -/
def Expr.freeVars : Expr → Env → List Var
  | .lit _, _ => []
  | .var v, σ => if (Env.lookup v σ).isSome then [] else [v]
  | .app _ args, σ => Expr.freeVarsList args σ
  | .min a b, σ => a.freeVars σ ∪ b.freeVars σ

/-- `Expr.freeVars` over an argument list, deduplicated. -/
def Expr.freeVarsList : List Expr → Env → List Var
  | [], _ => []
  | e :: es, σ => e.freeVars σ ∪ Expr.freeVarsList es σ

end

def Pattern.freeVars : Pattern → Env → List Var
  | .expr e, σ => e.freeVars σ
  | .eq e₁ e₂, σ => e₁.freeVars σ ∪ e₂.freeVars σ

namespace Env
/-- Append, requiring the two to agree wherever both bind. The result may bind a variable
twice, always to the same term. -/
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
equality, so the order `Expr.freeVars` produces does not matter. -/
def ValidEnv (vars : List Var) (db : Database) (σ : Env) : Prop :=
  (Env.dom σ).Perm vars ∧ ∀ b ∈ σ, b.2 ∈ db.terms

/-! ### Matching -/
/-- A pattern **matches** under `σ` when its instance is congruent to a term the database
holds. The **witness** `w` is drawn from the *original* terms: without one, the reflexive
equation `withOperands` adds for the instance would match everything.

`σ` is the whole evaluation environment for the query. Rule registration stores the query
as written, and a match supplies all of its variables. The database's ambient environment
is not consulted. -/
inductive Matches (db : Database) : Pattern → Env → Prop where
  | expr {e : Expr} {σ : Env} {w t : Term} :
      w ∈ db.terms → e.evalAtom db.sig σ = some t → CongOn db [t] w t →
      Matches db (.expr e) σ
  | eq {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term} :
      w ∈ db.terms →
      e₁.eval db.sig σ = some t₁ → e₂.eval db.sig σ = some t₂ →
      CongOn db [t₁, t₂] w t₁ → CongOn db [t₁, t₂] t₁ t₂ →
      Matches db (.eq e₁ e₂) σ

/-- A substitution binds exactly the pattern's variables and makes the pattern match.
Every query variable is local to the match. -/
def ValidSubst (db : Database) (p : Pattern) (σ : Env) : Prop :=
  ValidEnv (p.freeVars []) db σ ∧ Matches db p σ

/-- The substitutions a whole query admits: one per pattern, unioned. -/
def ValidQuerySubst (db : Database) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (ValidSubst db) q σs ∧ Env.UnionAll σs σ

/-- The whole query has a compatible substitution. Check variables are existential and
local to the query; evaluating a check exports no bindings and builds no terms. -/
def QueryHolds (db : Database) (q : Query) : Prop := ∃ σ, ValidQuerySubst db q σ

end Egglog
