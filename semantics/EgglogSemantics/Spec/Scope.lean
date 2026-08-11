import Mathlib.Logic.Function.Basic
import EgglogSemantics.Spec.Term

/-!
# The front end's static checks

Four checks, each an instance of the one walk `Check` below: `Scoped` — every variable used
is bound; `Evaluable` — every applied name is a declared constructor; `SetLegal` — no `set`
writes a constructor; `DeclsFresh` — no name is declared twice. `Scoped` threads a `Scope`,
the other three a `Signature`.
-/

namespace Egglog

/-! ### One walk -/

/-- A static check as a walk over a program: what it asks at the three sites a program
presents, and how the context they read is threaded. Unasked sites default to `True`. -/
structure Check (C : Type) where
  /-- Asked of each fact of a rule's query. -/
  fact : Pattern → C → Prop := fun _ _ => True
  /-- Asked of each action, in the context the actions before it leave. -/
  action : Action → C → Prop := fun _ _ => True
  /-- Asked of a declaration, in the context before it is installed. -/
  decl : FnName → FnDecl → C → Prop := fun _ _ _ => True
  /-- What an action adds to the context. -/
  bindAction : Action → C → C := fun _ c => c
  /-- What a query binds for the rule's head. -/
  bindQuery : Query → C → C := fun _ c => c
  /-- What a command leaves for the commands after it. -/
  bindCmd : Cmd → C → C

variable {C : Type}

/-- Each action in the context the earlier ones leave. -/
@[simp] def Check.actions (K : Check C) : List Action → C → Prop
  | [], _ => True
  | a :: as, c => K.action a c ∧ K.actions as (K.bindAction a c)

/-- A rule: its facts, then its head in the context the query binds. -/
@[simp] def Check.rule (K : Check C) (r : Rule) (c : C) : Prop :=
  (∀ p ∈ r.query, K.fact p c) ∧ K.actions r.actions (K.bindQuery r.query c)

/-- One command. A `:merge` body is **not** walked into: it runs in the environment
`mergeEnv` builds rather than in the ambient context. -/
@[simp] def Check.cmd (K : Check C) : Cmd → C → Prop
  | .action a, c => K.action a c
  | .rule r, c => K.rule r c
  | .run, _ => True
  | .decl f d, c => K.decl f d c

/-- Each command in the context the earlier ones leave. -/
@[simp] def Check.program (K : Check C) : Program → C → Prop
  | [], _ => True
  | c :: cs, x => K.cmd c x ∧ K.program cs (K.bindCmd c x)

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

/-- Every variable used is bound. -/
abbrev Check.scoped : Check Scope where
  fact p _ := p.Scoped
  action := Action.Scoped
  bindAction := Action.bind
  bindQuery := Query.bind
  bindCmd := Cmd.bind

@[inherit_doc Check.scoped] abbrev Actions.Scoped := Check.scoped.actions
@[inherit_doc Check.scoped] abbrev Rule.Scoped := Check.scoped.rule
@[inherit_doc Check.scoped] abbrev Cmd.Scoped := Check.scoped.cmd
@[inherit_doc Check.scoped] abbrev Program.Scoped := Check.scoped.program

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

/-- Every applied name is a declared constructor. Nothing is asked of a query fact, which
is matched rather than evaluated. -/
abbrev Check.evaluable : Check Signature where
  action := Action.Evaluable
  bindCmd := Cmd.sigBind

@[inherit_doc Check.evaluable] abbrev Actions.Evaluable := Check.evaluable.actions
@[inherit_doc Check.evaluable] abbrev Rule.Evaluable := Check.evaluable.rule
@[inherit_doc Check.evaluable] abbrev Cmd.Evaluable := Check.evaluable.cmd
@[inherit_doc Check.evaluable] abbrev Program.Evaluable := Check.evaluable.program

/-! ### `set` legality -/

/-- `(set (f …) …)` is legal only when `f` is a declared `:merge` or `:no-merge` function,
which is what keeps a constructor's entries the width `FnDecl.entryWidth` gives them. -/
def Action.SetLegal : Action → Signature → Prop
  | .set f _ _, sig => sig.mergeOf f ≠ none
  | _, _ => True

/-- No `set` writes a constructor. -/
abbrev Check.setLegal : Check Signature where
  action := Action.SetLegal
  bindCmd := Cmd.sigBind

@[inherit_doc Check.setLegal] abbrev Actions.SetLegal := Check.setLegal.actions
@[inherit_doc Check.setLegal] abbrev Rule.SetLegal := Check.setLegal.rule
@[inherit_doc Check.setLegal] abbrev Cmd.SetLegal := Check.setLegal.cmd
@[inherit_doc Check.setLegal] abbrev Program.SetLegal := Check.setLegal.program

/-! ### Freshness of a declaration

A redeclaration changes what the signature says of a name the state already has terms of,
breaking `Database.DeclaredTerms`. -/

/-- Every declaration names something the signature does not already have, asked *before*
`Cmd.sigBind` installs the name. -/
abbrev Check.declFresh : Check Signature where
  decl f _ sig := sig f = none
  bindCmd := Cmd.sigBind

@[inherit_doc Check.declFresh] abbrev Cmd.DeclFresh := Check.declFresh.cmd
@[inherit_doc Check.declFresh] abbrev Program.DeclsFresh := Check.declFresh.program

end Egglog
