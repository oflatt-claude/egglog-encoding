import EgglogSemantics.Spec.Step

/-!
# Scope checking

Ports the Redex `typed-expr`, `typed-query-expr`, `typed-action`, `typed-pattern`,
`typed-query`, `typed-actions`, `typed-rule` and `typed-program`.

The Redex has a single type, `no-type`, so its `TypeEnv` is a list of variables and
its judgments check nothing but scope. `Scope` is that list of variables with the
type erased; real sorts arrive with `:merge` functions, which need base-sorted
outputs (`PLAN.md`, M9).

Two things the Redex's judgments make relational are functions here:

* `typed-query-expr` always succeeds — its variable rule adds an unbound variable
  rather than rejecting it — so what it computes is just the scope extended with
  the pattern's variables. `Query.bind` is that.
* `typed-action`'s `let` rule carries the side condition
  `(not (member (TypeBinding ...) (TypeBinding ...)))`, which asks whether a *list*
  of bindings occurs as an *element* of itself. That is never true, so the negation
  always holds and the condition is vacuous; a `let` may shadow.

The payoff is `runProgram_isSome`: a well-scoped program never gets stuck.
`runRules` cannot get stuck either way — it drops firings whose actions fail — so
the corresponding statement about rules is
`evalLocalActions_isSome_of_scoped`: a well-scoped rule contributes on every
substitution its query admits.
-/

namespace Egglog
/-- The variables in scope. The Redex `TypeEnv`, with its one type erased. -/
abbrev Scope := List Var

/-- The scope describes the environment's domain exactly. Maintained across a run by
`runProgram_isSome`. -/
def Scope.Models (Γ : Scope) (σ : Env) : Prop := ∀ v, v ∈ Γ ↔ v ∈ Env.dom σ

/-- The Redex `typed-expr`: every variable of `e` is in scope. -/
def Expr.Scoped (e : Expr) (Γ : Scope) : Prop := ∀ v ∈ e.vars, v ∈ Γ

/-- `e` is a constructor application.

Query facts and `expr` actions are required to be applications, which the Redex does not
require: there a bare variable is a legal fact, matching any term, and a legal action,
adding one already present. egglog's grammar admits neither, so allowing them would leave
every later phase handling a case the real system cannot express. This is the one place
`WellScoped` is deliberately stricter than the Redex `typed-program`. -/
def Expr.IsApp : Expr → Prop
  | .app _ _ => True
  | _ => False

instance (e : Expr) : Decidable e.IsApp := by cases e <;> simp only [Expr.IsApp] <;>
  infer_instance

/-- The scope a query's patterns bind, i.e. what the Redex `typed-query` returns. -/
def Query.bind (q : Query) (Γ : Scope) : Scope := Γ ∪ Query.vars q

/-- A query fact. Only the application restriction; the Redex `typed-query` never fails,
and what it computes is `Query.bind`. -/
def Pattern.Scoped : Pattern → Prop
  | .expr e => e.IsApp
  | .eq _ _ => True

/-- The Redex `typed-action`, minus its vacuous side condition and plus the application
restriction on a bare `expr`. -/
def Action.Scoped : Action → Scope → Prop
  | .expr e, Γ => e.IsApp ∧ e.Scoped Γ
  | .letBind _ e, Γ => e.Scoped Γ
  | .union e₁ e₂, Γ => e₁.Scoped Γ ∧ e₂.Scoped Γ

/-- The scope after an action: only a `let` extends it. -/
def Action.bind : Action → Scope → Scope
  | .expr _, Γ => Γ
  | .letBind v _, Γ => v :: Γ
  | .union _ _, Γ => Γ

/-- The Redex `typed-actions`: each action is scoped in what the earlier ones bind. -/
def Actions.Scoped : List Action → Scope → Prop
  | [], _ => True
  | a :: as, Γ => a.Scoped Γ ∧ Actions.Scoped as (a.bind Γ)

/-- The scope after a sequence of actions. -/
def Actions.bind : List Action → Scope → Scope
  | [], Γ => Γ
  | a :: as, Γ => Actions.bind as (a.bind Γ)

/-- The Redex `typed-rule`: the actions are scoped in the query's bindings. -/
def Rule.Scoped (r : Rule) (Γ : Scope) : Prop :=
  (∀ p ∈ r.query, p.Scoped) ∧ Actions.Scoped r.actions (Query.bind r.query Γ)

/-- The Redex `typed-program`, one command at a time. -/
def Cmd.Scoped : Cmd → Scope → Prop
  | .action a, Γ => a.Scoped Γ
  | .rule r, Γ => r.Scoped Γ
  | .run, _ => True
  | .decl _ _, _ => True

/-- The scope after a command: only a top-level `let` extends it. -/
def Cmd.bind : Cmd → Scope → Scope
  | .action a, Γ => a.bind Γ
  | .rule _, Γ => Γ
  | .run, Γ => Γ
  | .decl _ _, Γ => Γ

/-- The Redex `typed-program`. -/
def Program.Scoped : Program → Scope → Prop
  | [], _ => True
  | c :: cs, Γ => c.Scoped Γ ∧ Program.Scoped cs (c.bind Γ)

/-- The scope after a program. -/
def Program.bind : Program → Scope → Scope
  | [], Γ => Γ
  | c :: cs, Γ => Program.bind cs (c.bind Γ)

/-- A program with no free variables: the Redex `(typed-program Program TypeEnv)`
starting from the empty environment. -/
def WellScoped (p : Program) : Prop := Program.Scoped p []

end Egglog
