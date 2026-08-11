import Mathlib.Logic.Function.Basic
import EgglogSemantics.Spec.Term

/-!
# The front end's static checks

Four checks: `Scoped` — every variable used is bound; `Evaluable` — every applied name is
a declared constructor; `SetLegal` — no `set` writes a constructor; `DeclsFresh` — no name
is declared twice. `Scoped` threads a `Scope`, extended by a `let` and by a query; the
other three thread a `Signature`, moved only by `Cmd.sigBind`.
-/

namespace Egglog

/-! ### Scope -/

/-- The variables in scope. -/
abbrev Scope := List Var

/-- Every variable of `e` is in scope. -/
def Expr.Scoped (e : Expr) (Γ : Scope) : Prop := ∀ v ∈ e.vars, v ∈ Γ

/-- `e` is an application. Query facts and `expr` actions are restricted to applications;
an `.eq` fact is not. -/
def Expr.IsApp : Expr → Prop
  | .app _ _ => True
  | _ => False

/-- A query fact carries the application restriction and nothing else: a fact never fails
to scope, and what it binds is `Query.bind`. A `.values` head is unconstrained. -/
def Pattern.Scoped : Pattern → Prop
  | .expr e => e.IsApp
  | .eq _ _ => True
  | .values _ _ _ => True

/-- An action scopes when each expression it evaluates does, plus the application
restriction on a bare `expr`. -/
def Action.Scoped : Action → Scope → Prop
  | .expr e, Γ => e.IsApp ∧ e.Scoped Γ
  | .letBind _ e, Γ => e.Scoped Γ
  | .union e₁ e₂, Γ => e₁.Scoped Γ ∧ e₂.Scoped Γ
  | .set _ args out, Γ => (∀ e ∈ args, e.Scoped Γ) ∧ ∀ e ∈ out, e.Scoped Γ

/-- The scope after an action: only a `let` extends it, and it may shadow. -/
def Action.bind : Action → Scope → Scope
  | .letBind v _, Γ => v :: Γ
  | _, Γ => Γ

/-- The scope a query's patterns bind. -/
def Query.bind (q : Query) (Γ : Scope) : Scope := Γ ∪ Query.vars q

/-- The scope after a command: only a top-level `let` extends it. -/
def Cmd.bind : Cmd → Scope → Scope
  | .action a, Γ => a.bind Γ
  | _, Γ => Γ

/-- Each action in the scope the earlier ones leave. -/
@[simp] def Actions.Scoped : List Action → Scope → Prop
  | [], _ => True
  | a :: as, Γ => a.Scoped Γ ∧ Actions.Scoped as (a.bind Γ)

/-- Its facts, then its head in the scope the query binds. -/
@[simp] def Rule.Scoped (r : Rule) (Γ : Scope) : Prop :=
  (∀ p ∈ r.query, p.Scoped) ∧ Actions.Scoped r.actions (Query.bind r.query Γ)

/-- A `:merge` body is **not** walked into, here or in any of the checks below: it runs in
the environment `mergeEnv` builds rather than in the ambient context. -/
@[simp] def Cmd.Scoped : Cmd → Scope → Prop
  | .action a, Γ => a.Scoped Γ
  | .rule r, Γ => r.Scoped Γ
  | .run, _ => True
  | .decl _ _, _ => True

/-- Each command in the scope the earlier ones leave. -/
@[simp] def Program.Scoped : Program → Scope → Prop
  | [], _ => True
  | c :: cs, Γ => c.Scoped Γ ∧ Program.Scoped cs (c.bind Γ)

/-- A program with no free variables: `Program.Scoped` from the empty scope. -/
def WellScoped (p : Program) : Prop := Program.Scoped p []

/-! ### Evaluability

`Scoped` is not enough for `Expr.eval` to return a term: an application may be a *lookup*
or a *primitive*. `Evaluable` rules both out. -/

/-- The signature after a command: only a declaration writes it, as in `CmdStep`. -/
def Cmd.sigBind : Cmd → Signature → Signature
  | .decl f d, sig => Function.update sig f (some d)
  | _, sig => sig

/-- Every application in `e` **builds**: its head is a declared constructor and not a
primitive, so evaluating `e` cannot get stuck on it. -/
def Expr.Evaluable (e : Expr) (sig : Signature) : Prop :=
  ∀ f ∈ e.fns, Prim.ofName f = none ∧ sig.IsCtor f

/-- `Action.Scoped`'s companion: every expression the action evaluates builds. -/
def Action.Evaluable : Action → Signature → Prop
  | .expr e, sig => e.Evaluable sig
  | .letBind _ e, sig => e.Evaluable sig
  | .union e₁ e₂, sig => e₁.Evaluable sig ∧ e₂.Evaluable sig
  | .set _ args out, sig => (∀ e ∈ args, e.Evaluable sig) ∧ ∀ e ∈ out, e.Evaluable sig

@[simp] def Actions.Evaluable : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Evaluable sig ∧ Actions.Evaluable as sig

/-- Nothing is asked of a query fact, which is matched rather than evaluated. -/
@[simp] def Rule.Evaluable (r : Rule) (sig : Signature) : Prop :=
  Actions.Evaluable r.actions sig

@[simp] def Cmd.Evaluable : Cmd → Signature → Prop
  | .action a, sig => a.Evaluable sig
  | .rule r, sig => r.Evaluable sig
  | .run, _ => True
  | .decl _ _, _ => True

/-- Each command in the signature the earlier ones leave. -/
@[simp] def Program.Evaluable : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.Evaluable sig ∧ Program.Evaluable cs (c.sigBind sig)

/-! ### `set` legality -/

/-- `(set (f …) …)` is legal only when `f` is a declared `:merge` or `:no-merge` function,
which is what keeps a constructor's entries the width `FnDecl.entryWidth` gives them. -/
def Action.SetLegal : Action → Signature → Prop
  | .set f _ _, sig => sig.mergeOf f ≠ none
  | _, _ => True

@[simp] def Actions.SetLegal : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.SetLegal sig ∧ Actions.SetLegal as sig

@[simp] def Rule.SetLegal (r : Rule) (sig : Signature) : Prop :=
  Actions.SetLegal r.actions sig

@[simp] def Cmd.SetLegal : Cmd → Signature → Prop
  | .action a, sig => a.SetLegal sig
  | .rule r, sig => r.SetLegal sig
  | .run, _ => True
  | .decl _ _, _ => True

@[simp] def Program.SetLegal : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.SetLegal sig ∧ Program.SetLegal cs (c.sigBind sig)

/-! ### Freshness of a declaration

A redeclaration changes what the signature says of a name the state already has terms of,
breaking `Database.DeclaredTerms`. -/

@[simp] def Cmd.DeclFresh : Cmd → Signature → Prop
  | .decl f _, sig => sig f = none
  | .action _, _ => True
  | .rule _, _ => True
  | .run, _ => True

/-- Each command is asked **before** `Cmd.sigBind` installs its declaration; asked after,
the check would read back `Function.update`'s own entry and always fail. -/
@[simp] def Program.DeclsFresh : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.DeclFresh sig ∧ Program.DeclsFresh cs (c.sigBind sig)

end Egglog
