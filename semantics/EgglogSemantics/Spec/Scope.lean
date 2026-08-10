import Mathlib.Logic.Function.Basic
import EgglogSemantics.Spec.Term

/-!
# Scope checking

These judgments check **scope and nothing else**: `Scope` is a list of variables,
threaded by `Cmd.bind`, and a `Scoped` judgment says one thing only — every variable
used is bound. There are no sorts yet; they arrive with `:merge` functions, which need
base-sorted outputs (`PLAN.md`, M9).

Whether an application can be *evaluated* is a fact about the declarations rather than
about scope, so it is a judgment of its own: `Evaluable`, below, which reads a
`Signature` where `Scoped` reads a `Scope`.

Two things are functions rather than judgments, because neither can fail:

* A query's patterns always scope — an unbound pattern variable is a *match* variable,
  not an error — so what a query does is extend the scope with its variables.
  `Query.bind` is that.
* A `let` may shadow a variable already in scope, so `Action.bind` just prepends.

The payoff is `run_isSome`: a scoped, evaluable program never gets stuck.
`runRules` cannot get stuck either way — it drops firings whose actions fail — so
the corresponding statement about rules is
`evalLocalActions_isSome_of_scoped`: such a rule contributes on every
substitution its query admits.
-/

namespace Egglog
/-- The variables in scope. -/
abbrev Scope := List Var

/-- Every variable of `e` is in scope.

Scope and nothing else. Whether `e` can be evaluated is `Expr.Evaluable`, which is a
question about the declarations and is answered separately. -/
def Expr.Scoped (e : Expr) (Γ : Scope) : Prop := ∀ v ∈ e.vars, v ∈ Γ

/-- `e` is a constructor application.

Query facts and `expr` actions are required to be applications because **egglog's
grammar admits nothing else there**: a bare variable is `parse error: expected fact` as
a query fact, `parse error: expected action` in a rule head and `parse error: expected
command` at top level, and a literal is rejected the same way. Allowing them would leave
every later phase handling a case the real system cannot express. An `.eq` fact is
unrestricted, matching egglog, which accepts `(= a b)` between two bound variables. -/
def Expr.IsApp : Expr → Prop
  | .app _ _ => True
  | _ => False

instance (e : Expr) : Decidable e.IsApp := by cases e <;> simp only [Expr.IsApp] <;>
  infer_instance

/-- The scope a query's patterns bind. -/
def Query.bind (q : Query) (Γ : Scope) : Scope := Γ ∪ Query.vars q

/-- A query fact. Only the application restriction: a fact never fails to scope, and
what it binds is `Query.bind`. -/
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

/-- The scope after an action: only a `let` extends it. -/
def Action.bind : Action → Scope → Scope
  | .expr _, Γ => Γ
  | .letBind v _, Γ => v :: Γ
  | .union _ _, Γ => Γ
  | .set _ _ _, Γ => Γ

/-- Each action is scoped in what the earlier ones bind. -/
def Actions.Scoped : List Action → Scope → Prop
  | [], _ => True
  | a :: as, Γ => a.Scoped Γ ∧ Actions.Scoped as (a.bind Γ)

/-- The scope after a sequence of actions. -/
def Actions.bind : List Action → Scope → Scope
  | [], Γ => Γ
  | a :: as, Γ => Actions.bind as (a.bind Γ)

/-- A rule: the actions are scoped in the query's bindings. -/
def Rule.Scoped (r : Rule) (Γ : Scope) : Prop :=
  (∀ p ∈ r.query, p.Scoped) ∧ Actions.Scoped r.actions (Query.bind r.query Γ)

/-- One command.

A `:merge` body is deliberately unchecked: it runs in the environment `mergeEnv` builds
from the two colliding rows, never in the ambient scope, so `Γ` says nothing about it. -/
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

/-- Each command is scoped in what the earlier ones bind. -/
def Program.Scoped : Program → Scope → Prop
  | [], _ => True
  | c :: cs, Γ => c.Scoped Γ ∧ Program.Scoped cs (c.bind Γ)

/-- The scope after a program. -/
def Program.bind : Program → Scope → Scope
  | [], Γ => Γ
  | c :: cs, Γ => Program.bind cs (c.bind Γ)

/-- A program with no free variables: `Program.Scoped` from the empty scope. -/
def WellScoped (p : Program) : Prop := Program.Scoped p []

/-! ### Evaluability

`Scoped` is not enough for `Expr.eval` to return a term: an application may be a
*lookup*, which has no evaluation rule at all, or
a *primitive*, which may be handed operands of the wrong sort. `Evaluable` rules both
out. `run_isSome` carries it beside `WellScoped` rather than folding it in, so that
"scoped" goes on meaning scope.

Like `SetLegal` below it reads the signature and not the scope, threaded by `Cmd.sigBind`.
-/
/-- The signature after a command: only a declaration writes it. `Cmd.bind` for
signatures, and exactly what `stepCmd`'s `.decl` case does. -/
def Cmd.sigBind : Cmd → Signature → Signature
  | .decl f d, sig => Function.update sig f (some d)
  | _, sig => sig

/-- Every application in `e` **builds**, so evaluating `e` cannot get stuck on one.

An application is one of four things, decided by the name: *undeclared*, which is an
error, and which this rules out — so `Program.Evaluable` is declare-before-use and needs
no separate check; a *lookup* if the function is a declared merge function, which egglog
rejects in a rule head (`check_no_function_lookups_in_actions`) and this model rejects
everywhere, since reading is the query atom `Pattern.values`; a *primitive*, which
computes; or a declared constructor, which builds. Only the last always succeeds, and this
admits only the last.

**Primitives are excluded rather than sort-checked**, which is where this is stricter than
egglog: `(min 1 2)` is a legal egglog action, and `(min (A) (B))` is a type error there,
and with no sorts in this model (`PLAN.md`, base sorts) nothing here can tell the two
apart. A `:merge` body — the one position primitives exist for — is not checked at all
(`Cmd.Evaluable`, `.decl`), so nothing the model relies on is lost.

`Impl/Check.lean`'s `Expr.noLookup` is the front end's `Bool` transcription of the
constructor half. This is the half the semantics consumes. -/
def Expr.Evaluable (e : Expr) (sig : Signature) : Prop :=
  ∀ f ∈ e.fns, Prim.ofName f = none ∧ sig.IsCtor f

/-- `Action.Scoped`'s companion: every expression the action evaluates builds. -/
def Action.Evaluable : Action → Signature → Prop
  | .expr e, sig => e.Evaluable sig
  | .letBind _ e, sig => e.Evaluable sig
  | .union e₁ e₂, sig => e₁.Evaluable sig ∧ e₂.Evaluable sig
  | .set _ args out, sig => (∀ e ∈ args, e.Evaluable sig) ∧ ∀ e ∈ out, e.Evaluable sig

/-- Every action in the list. Unlike `Actions.Scoped` this needs no threading: no action
changes the signature. -/
def Actions.Evaluable : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Evaluable sig ∧ Actions.Evaluable as sig

/-- A rule's head. A query is matched rather than evaluated, so it is unconstrained. -/
def Rule.Evaluable (r : Rule) (sig : Signature) : Prop := Actions.Evaluable r.actions sig

/-- `Cmd.Scoped`'s companion.

A `:merge` body is unchecked here too, and for the sharper reason: it is the one position
primitives exist for, so demanding that it build would forbid the feature. `MergeStep` is
a relation, and a body that gets stuck simply does not step. -/
def Cmd.Evaluable : Cmd → Signature → Prop
  | .action a, sig => a.Evaluable sig
  | .rule r, sig => r.Evaluable sig
  | .run, _ => True
  | .decl _ _, _ => True

/-- `Program.Scoped`'s companion: each command is checked against the signature the
earlier ones leave, as `Program.Scoped` checks against the scope they leave. -/
def Program.Evaluable : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.Evaluable sig ∧ Program.Evaluable cs (c.sigBind sig)

/-! ### `set` legality

A third static check, additive and deliberately kept apart: `Evaluable` says what an
expression may *build*, this says what an action may *write*. Both read the signature and
neither reads the scope, so the triple to carry is
`WellScoped p ∧ p.Evaluable sig ∧ p.SetLegal sig`; `PLAN.md`, "`set` legality is a
separate predicate, for now", says when to fold them together.
-/
/-- `(set (f …) …)` is legal only when `f` is a declared `:merge` or `:no-merge`
function — the one thing that has a merge specification to consult. A constructor and an
undeclared name are both excluded, which is egglog's `SetConstructorDisallowed` and its
"unbound function".

It is what keeps `Database.CtorRows` an invariant. A `set` writes the row
`⟨f, as, [v]⟩` for whatever `v` its out expression denotes, and `Database.ctorRowsOf`
holds no such row unless `v` is `.app f as`. -/
def Action.SetLegal : Action → Signature → Prop
  | .expr _, _ => True
  | .letBind _ _, _ => True
  | .union _ _, _ => True
  | .set f _ _, sig => sig.mergeOf f ≠ none

/-- Every action in the list is a legal `set`. Unlike `Actions.Scoped` this needs no
threading: no action changes the signature. -/
def Actions.SetLegal : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.SetLegal sig ∧ Actions.SetLegal as sig

/-- A rule is legal when its head is; a query writes nothing. -/
def Rule.SetLegal (r : Rule) (sig : Signature) : Prop := Actions.SetLegal r.actions sig

/-! There is deliberately no companion restriction on a `Pattern.values` atom — reading a
non-constructor is what it is *for*. `PLAN.md`, "Arity checking", says why that is safe. -/

/-- `Cmd.Scoped`'s companion for `set`. -/
def Cmd.SetLegal : Cmd → Signature → Prop
  | .action a, sig => a.SetLegal sig
  | .rule r, sig => r.SetLegal sig
  | .run, _ => True
  | .decl _ _, _ => True

/-- `Program.Scoped`'s companion for `set`: each command is checked against the
signature the earlier ones leave, as `Program.Scoped` checks against the scope they
leave. -/
def Program.SetLegal : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.SetLegal sig ∧ Program.SetLegal cs (c.sigBind sig)

/-! ### Freshness of a declaration

The other half of declare-before-use: `Evaluable` says a name must be declared *before* it
is applied, this says a name is declared *once*. Nothing in the dynamics forbids a
redeclaration — `Cmd.sigBind` is `Function.update` — but a redeclaration can change what
`Signature.IsCtor` says of a name the state already has rows of, which is a derivation
`Spec/Merge.lean`'s `MCong.fd` had and loses. `Proofs/Merge.lean`'s `CmdStep.mono_recorded`
is the one place that bites, and `Proofs/Counterexamples.lean`'s
`mono_recorded_decl_false` is the redeclaration that breaks it.
-/
/-- `c` declares a name the signature does not already have. -/
def Cmd.DeclFresh : Cmd → Signature → Prop
  | .decl f _, sig => sig f = none
  | _, _ => True

/-- Every declaration in the program is fresh at the point it happens, threaded by
`Cmd.sigBind` as `Program.Evaluable` is. -/
def Program.DeclsFresh : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.DeclFresh sig ∧ Program.DeclsFresh cs (c.sigBind sig)

/-- `c` declares only constructors.

Separate from `SetLegal` because it constrains a different thing: `SetLegal` says what a
head may write, this says what the signature may become. `Database.CtorRows` needs both
— declaring a `:merge` function makes rows *already present* a `MergeStep` collision,
whose combined row need not be a constructor row, and no `set` is involved. -/
def Cmd.CtorDecl : Cmd → Prop
  | .decl _ d => d.merge = none
  | _ => True

/-- Every declaration in the program declares a constructor. -/
def Program.CtorDecls (p : Program) : Prop := ∀ c ∈ p, c.CtorDecl

/-! ### The front end's static checks

Two further static checks — a use's column counts against the declaration, and "every
read is a query atom" — live in `Impl/Check.lean`. They are about what egglog *rejects*
rather than what a program *means*, and nothing in the semantics consumes them. The tuple
to carry is
`WellScoped p ∧ p.Evaluable sig ∧ p.DeclsFresh sig ∧ p.SetLegal sig ∧ WellArity p ∧
ReadsAreAtoms p`. -/

end Egglog
