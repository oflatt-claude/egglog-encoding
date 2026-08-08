import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import EgglogSemantics.Spec.Eval

/-!
# E-matching

Ports the Redex `free-vars`, `Env-Union`, `valid-env`, `valid-subst` and
`valid-query-subst`.

The Redex defines e-matching declaratively rather than by a search procedure: a
substitution matches a pattern when the pattern's *instance* is provably equal to
some **witness** term the database already holds. The witness is what stops a
pattern from matching a term the e-graph does not contain — the instance is added
to the database before congruence is consulted, so without a witness drawn from the
original terms, reflexivity would match everything.

The Redex `valid-subst-faster` gives an operational alternative; porting it and
proving the two agree is deferred (see `PLAN.md`, M8).
-/

namespace Egglog
mutual

/-- The Redex `free-vars`: the variables of `e` not already bound in `σ`.

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

/-- The free variables of a pattern. -/
def Pattern.freeVars : Pattern → Env → List Var
  | .expr e, σ => e.freeVars σ
  | .eq e₁ e₂, σ => e₁.freeVars σ ∪ e₂.freeVars σ
  | .values vs _ as, σ => Expr.freeVarsList vs σ ∪ Expr.freeVarsList as σ

namespace Env
/-- The Redex `Env-Union2`: append, requiring the two to agree wherever both bind.

`σ₁`'s bindings are kept even when `σ₂` has them too, so the result can bind a
variable twice — always to the same term, so `lookup` cannot tell. This is a
relation rather than a function because the side condition is an equality on terms
and this development carries no decidable equality for them. -/
def Union2 (σ₁ σ₂ σ : Env) : Prop :=
  (∀ b ∈ σ₁, ∀ t, lookup b.1 σ₂ = some t → b.2 = t) ∧ σ = σ₁ ++ σ₂

/-- The Redex `Env-Union`: the left fold of `Union2`, which fails if any step does. -/
inductive UnionAll : List Env → Env → Prop where
  | nil : UnionAll [] []
  | single (σ : Env) : UnionAll [σ] σ
  | step {σ₁ σ₂ σr σ : Env} {σs : List Env} :
      Union2 σ₁ σ₂ σr → UnionAll (σr :: σs) σ → UnionAll (σ₁ :: σ₂ :: σs) σ

end Env
/-! ### Valid substitutions -/
/-- The Redex `valid-env`: `σ` binds exactly `vars`, each to a term the database
holds.

The Redex pins `σ`'s bindings to the order of `vars`; `Perm` is used here so the
definition does not depend on the order `varset-union` happens to produce. The extra
substitutions that admits are permutations of Redex ones, which no `lookup` can
distinguish (`Expr.eval_agree`). -/
def ValidEnv (vars : List Var) (db : Database) (σ : Env) : Prop :=
  (Env.dom σ).Perm vars ∧ ∀ b ∈ σ, b.2 ∈ db.terms

/-- The Redex `valid-subst`.

Both cases add the pattern's instance (or instances) to the database before asking
`Cong`, mirroring the Redex
`restore-congruence (U_d Database_1 ((tset Term_res) …))`. The witness is drawn from
the *original* terms.

The witness premises stay spelled out rather than reading `CongOn`, because the extended
database they ask over is the one *both* instances are added to; only the `eq` case's
final premise, which relates the two instances themselves, is `CongOn`. -/
inductive ValidSubst (db : Database) : Pattern → Env → Prop where
  | expr {e : Expr} {σ : Env} {w t : Term} :
      ValidEnv (e.freeVars db.env) db σ → w ∈ db.terms →
      e.eval (db.env ++ σ) = some t → Cong (db.addTerm t) w t →
      ValidSubst db (.expr e) σ
  | eq {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term} :
      ValidEnv (e₁.freeVars db.env ∪ e₂.freeVars db.env) db σ → w ∈ db.terms →
      e₁.eval (db.env ++ σ) = some t₁ → e₂.eval (db.env ++ σ) = some t₂ →
      Cong ((db.addTerm t₁).addTerm t₂) w t₁ → CongOn db t₁ t₂ →
      ValidSubst db (.eq e₁ e₂) σ
  /-- A tuple destructure matches a row whose key and value columns are congruent to the
  operands, which is egglog joining on canonical ids.

  The operands are added to the database before congruence is consulted, exactly as the
  `expr` and `eq` cases add theirs. An operand is an *expression*, so it may denote a term
  the program never built; the extension is what makes such an operand matchable, and it
  is how this model captures egglog's flattening of a nested fact into one atom per
  subterm (`PLAN.md`, "Reading is a query atom").

  Adding the operands is conservative, not permissive: `Cong.congr` still needs *both*
  applications present, so a hypothesized operand reaches an existing class only through a
  row the database really holds.

  There is no `w ∈ db.terms` witness: the row itself is what forbids matching something
  the database does not hold. -/
  | values {vs : List Expr} {f : FnName} {as : List Expr} {σ : Env}
      {us ts ws bs : List Term} :
      ValidEnv (Expr.freeVarsList vs db.env ∪ Expr.freeVarsList as db.env) db σ →
      Expr.evalList vs (db.env ++ σ) = some us →
      Expr.evalList as (db.env ++ σ) = some ts →
      CongList ((db.addTerms ts).addTerms us) ts bs →
      CongList ((db.addTerms ts).addTerms us) us ws → Row.mk f bs ws ∈ db.rows →
      ValidSubst db (.values vs f as) σ

/-- The Redex `valid-query-subst`: one substitution per pattern, unioned. -/
def ValidQuerySubst (db : Database) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (ValidSubst db) q σs ∧ Env.UnionAll σs σ

end Egglog
