import EgglogSemantics.Spec.Match

/-!
# Substitution helpers

Ground-term substitution into expressions and queries. These are proof-level operations;
rule registration in the let-free semantics stores the rule unchanged.
-/

namespace Egglog

mutual

/-- Substitute the terms in `σ` into `e`: a name `σ` binds becomes the expression that rebuilds
its value, and one it does not is a match variable. -/
def Expr.resolveGlobals (σ : Env) : Expr → Expr
  | .lit l => .lit l
  | .var v => match Env.lookup v σ with
      | some t => t.toExpr
      | none => .var v
  | .app f args => .app f (Expr.resolveGlobalsList σ args)

/-- `Expr.resolveGlobals` over an argument list. -/
def Expr.resolveGlobalsList (σ : Env) : List Expr → List Expr
  | [] => []
  | e :: es => Expr.resolveGlobals σ e :: Expr.resolveGlobalsList σ es

end

@[simp] theorem Expr.resolveGlobals_lit (σ : Env) (l : Lit) :
    Expr.resolveGlobals σ (.lit l) = .lit l := rfl

theorem Expr.resolveGlobals_var (σ : Env) (v : Var) :
    Expr.resolveGlobals σ (.var v)
      = match Env.lookup v σ with | some t => t.toExpr | none => .var v := rfl

@[simp] theorem Expr.resolveGlobals_var_none {σ : Env} {v : Var}
    (h : Env.lookup v σ = none) : Expr.resolveGlobals σ (.var v) = .var v := by
  rw [Expr.resolveGlobals_var, h]

@[simp] theorem Expr.resolveGlobals_var_some {σ : Env} {v : Var} {t : Term}
    (h : Env.lookup v σ = some t) : Expr.resolveGlobals σ (.var v) = t.toExpr := by
  rw [Expr.resolveGlobals_var, h]

@[simp] theorem Expr.resolveGlobals_app (σ : Env) (f : FnName) (args : List Expr) :
    Expr.resolveGlobals σ (.app f args) = .app f (Expr.resolveGlobalsList σ args) := rfl

@[simp] theorem Expr.resolveGlobalsList_nil (σ : Env) :
    Expr.resolveGlobalsList σ [] = [] := rfl

@[simp] theorem Expr.resolveGlobalsList_cons (σ : Env) (e : Expr) (es : List Expr) :
    Expr.resolveGlobalsList σ (e :: es)
      = Expr.resolveGlobals σ e :: Expr.resolveGlobalsList σ es := rfl

/-- `Expr.resolveGlobals` over a pattern. -/
def Pattern.resolveGlobals (σ : Env) : Pattern → Pattern
  | .expr e => .expr (e.resolveGlobals σ)
  | .eq e₁ e₂ => .eq (e₁.resolveGlobals σ) (e₂.resolveGlobals σ)
  | .values vs f as =>
      .values (Expr.resolveGlobalsList σ vs) f (Expr.resolveGlobalsList σ as)

/-- `Pattern.resolveGlobals` over a query. -/
def Query.resolveGlobals (σ : Env) (q : Query) : Query := q.map (Pattern.resolveGlobals σ)

/-- Substitute in a rule query while preserving its head and ruleset. -/
def Rule.resolveGlobals (σ : Env) (r : Rule) : Rule :=
  { r with query := Query.resolveGlobals σ r.query }

@[simp] theorem Rule.resolveGlobals_actions (σ : Env) (r : Rule) :
    (r.resolveGlobals σ).actions = r.actions := rfl

@[simp] theorem Rule.resolveGlobals_query (σ : Env) (r : Rule) :
    (r.resolveGlobals σ).query = Query.resolveGlobals σ r.query := rfl

@[simp] theorem Rule.resolveGlobals_ruleset (σ : Env) (r : Rule) :
    (r.resolveGlobals σ).ruleset = r.ruleset := rfl

@[simp] theorem Query.resolveGlobals_nil (q : Query) : Query.resolveGlobals [] q = q := by
  have hE : ∀ e : Expr, Expr.resolveGlobals [] e = e := by
    intro e
    induction e using Expr.rec
      (motive_2 := fun es => Expr.resolveGlobalsList [] es = es) with
    | lit l => rfl
    | var v => rfl
    | app f args ih => rw [Expr.resolveGlobals, ih]
    | nil => rfl
    | cons e es ihe ihes => rw [Expr.resolveGlobalsList, ihe, ihes]
  have hP : ∀ p : Pattern, Pattern.resolveGlobals [] p = p := by
    have hL : ∀ es : List Expr, Expr.resolveGlobalsList [] es = es := by
      intro es; induction es with
      | nil => rfl
      | cons e es ih => rw [Expr.resolveGlobalsList, hE, ih]
    intro p
    cases p with
    | expr e => rw [Pattern.resolveGlobals, hE]
    | eq e₁ e₂ => rw [Pattern.resolveGlobals, hE, hE]
    | values vs f as => rw [Pattern.resolveGlobals, hL, hL]
  rw [Query.resolveGlobals]
  induction q with
  | nil => rfl
  | cons p ps ih => rw [List.map_cons, hP, ih]

@[simp] theorem Rule.resolveGlobals_nil (r : Rule) : r.resolveGlobals [] = r := by
  rw [Rule.resolveGlobals, Query.resolveGlobals_nil]

/-- A resolved global is closed, so resolving again leaves it alone. -/
theorem Expr.resolveGlobals_toExpr (σ : Env) :
    ∀ t : Term, Expr.resolveGlobals σ t.toExpr = t.toExpr := by
  intro t
  induction t using Term.rec
    (motive_2 := fun ts => Expr.resolveGlobalsList σ (Term.toExprList ts)
      = Term.toExprList ts) with
  | lit l => rfl
  | app f ts ih => rw [Term.toExpr_app, Expr.resolveGlobals_app, ih]
  | nil => rfl
  | cons t ts iht ihts =>
      rw [Term.toExprList_cons, Expr.resolveGlobalsList_cons, iht, ihts]

/-- **Resolving twice resolves through the concatenation.** A rule registered under `σ₀` and
resolved again under `σ₁` reads as one resolution, which is why a state's rules are always
`Rule.resolveGlobals`'d source text. -/
theorem Expr.resolveGlobals_resolveGlobals (σ₀ σ₁ : Env) :
    ∀ e : Expr,
      (e.resolveGlobals σ₀).resolveGlobals σ₁ = e.resolveGlobals (σ₀ ++ σ₁) := by
  intro e
  induction e using Expr.rec
    (motive_2 := fun es => Expr.resolveGlobalsList σ₁ (Expr.resolveGlobalsList σ₀ es)
      = Expr.resolveGlobalsList (σ₀ ++ σ₁) es) with
  | lit l => rfl
  | var v =>
      cases h₀ : Env.lookup v σ₀ with
      | some t =>
          rw [Expr.resolveGlobals_var_some h₀, Expr.resolveGlobals_toExpr,
            Expr.resolveGlobals_var_some (Env.lookup_append_of_some h₀)]
      | none =>
          rw [Expr.resolveGlobals_var_none h₀]
          cases h₁ : Env.lookup v σ₁ with
          | some t =>
              rw [Expr.resolveGlobals_var_some h₁,
                Expr.resolveGlobals_var_some (σ := σ₀ ++ σ₁)
                  (by rw [Env.lookup_append_of_none h₀]; exact h₁)]
          | none =>
              rw [Expr.resolveGlobals_var_none h₁,
                Expr.resolveGlobals_var_none (σ := σ₀ ++ σ₁)
                  (by rw [Env.lookup_append_of_none h₀]; exact h₁)]
  | app f args ih =>
      rw [Expr.resolveGlobals_app, Expr.resolveGlobals_app, ih, Expr.resolveGlobals_app]
  | nil => rfl
  | cons e es ihe ihes =>
      rw [Expr.resolveGlobalsList_cons, Expr.resolveGlobalsList_cons, ihe, ihes,
        Expr.resolveGlobalsList_cons]

@[inherit_doc Expr.resolveGlobals_resolveGlobals]
theorem Expr.resolveGlobalsList_resolveGlobalsList (σ₀ σ₁ : Env) :
    ∀ es : List Expr, Expr.resolveGlobalsList σ₁ (Expr.resolveGlobalsList σ₀ es)
      = Expr.resolveGlobalsList (σ₀ ++ σ₁) es := by
  intro es
  induction es with
  | nil => rfl
  | cons e es ih =>
      rw [Expr.resolveGlobalsList_cons, Expr.resolveGlobalsList_cons,
        Expr.resolveGlobals_resolveGlobals, ih, Expr.resolveGlobalsList_cons]

@[inherit_doc Expr.resolveGlobals_resolveGlobals]
theorem Pattern.resolveGlobals_resolveGlobals (σ₀ σ₁ : Env) (p : Pattern) :
    Pattern.resolveGlobals σ₁ (Pattern.resolveGlobals σ₀ p)
      = Pattern.resolveGlobals (σ₀ ++ σ₁) p := by
  cases p with
  | expr e => rw [Pattern.resolveGlobals, Pattern.resolveGlobals, Pattern.resolveGlobals,
      Expr.resolveGlobals_resolveGlobals]
  | eq e₁ e₂ => rw [Pattern.resolveGlobals, Pattern.resolveGlobals, Pattern.resolveGlobals,
      Expr.resolveGlobals_resolveGlobals, Expr.resolveGlobals_resolveGlobals]
  | values vs f as => rw [Pattern.resolveGlobals, Pattern.resolveGlobals,
      Pattern.resolveGlobals, Expr.resolveGlobalsList_resolveGlobalsList,
      Expr.resolveGlobalsList_resolveGlobalsList]

@[inherit_doc Expr.resolveGlobals_resolveGlobals]
theorem Query.resolveGlobals_resolveGlobals (σ₀ σ₁ : Env) (q : Query) :
    Query.resolveGlobals σ₁ (Query.resolveGlobals σ₀ q)
      = Query.resolveGlobals (σ₀ ++ σ₁) q := by
  rw [Query.resolveGlobals, Query.resolveGlobals, Query.resolveGlobals, List.map_map]
  exact List.map_congr_left fun p _ => Pattern.resolveGlobals_resolveGlobals σ₀ σ₁ p

@[inherit_doc Expr.resolveGlobals_resolveGlobals]
theorem Rule.resolveGlobals_resolveGlobals (σ₀ σ₁ : Env) (r : Rule) :
    (r.resolveGlobals σ₀).resolveGlobals σ₁ = r.resolveGlobals (σ₀ ++ σ₁) := by
  simp only [Rule.resolveGlobals, Rule.resolveGlobals_query,
    Query.resolveGlobals_resolveGlobals]

end Egglog
