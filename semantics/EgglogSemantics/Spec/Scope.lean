import Mathlib.Logic.Function.Basic
import EgglogSemantics.Spec.Term

/-!
# The front end's static checks

**What this file says is: egglog's front end accepts this program** — every variable
bound, every applied name a declared constructor, no `set` on a constructor, no name
declared twice. Four checks, each transcribing one a real front end runs:

| check | asks | reads |
| --- | --- | --- |
| `Scoped` | every variable used is bound | the scope |
| `Evaluable` | every applied name is a declared constructor | the signature |
| `SetLegal` | no `set` writes a constructor | the signature |
| `DeclsFresh` | no name is declared twice | the signature |

Between them they are what makes an accepted program mean something: `programStep_isSome`
— such a program never gets stuck — needs the first two, and the invariance of
`Database.CtorRows` needs the third. They stay four rather than one because the theorems
need them apart: handing `execM_contained` the bundle would hand it hypotheses it does not
use. `WellFormed`, at the end, is the conjunction, for a reader who wants one name.

All four are **one walk**, `Check` below: a check is fixed by what it asks at the three
sites a program presents — a query fact, an action, a declaration — and by the context it
threads. Everything else — that a rule's head is checked in what its query binds, that a
command is checked in what the earlier ones leave — is said once, in the walk.

Two more front-end checks are `Bool` and live in `Impl/Check.lean`, because they say what
egglog *rejects* rather than what a program *means*: `arityOk`, a use's column counts
against its declaration, and `noLookup`, "every read is a query atom". Those two walk into
a `:merge` body; nothing here does.
-/

namespace Egglog

/-! ### One walk -/

/-- A static check, as the front end runs it over a program: three questions, and how the
context they read is threaded. Unasked sites default to `True`, so each check below lists
only the sites it cares about.

`bindCmd` against `decl` is where declare-before-use lives: a declaration is asked about
at the context *before* it is installed, which is what lets `DeclsFresh` mean "not already
declared", while every command after it sees the context including it. -/
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
`mergeEnv` builds from the two colliding rows rather than in the ambient context, and it
is the one position primitives exist for, so demanding that it build would forbid the
feature. `MergeStep` is a relation, and a body that gets stuck simply does not step. -/
@[simp] def Check.cmd (K : Check C) : Cmd → C → Prop
  | .action a, c => K.action a c
  | .rule r, c => K.rule r c
  | .run, _ => True
  | .decl f d, c => K.decl f d c

/-- Each command in the context the earlier ones leave. -/
@[simp] def Check.program (K : Check C) : Program → C → Prop
  | [], _ => True
  | c :: cs, x => K.cmd c x ∧ K.program cs (K.bindCmd c x)

/-! ### Scope

**Scope and nothing else**: every variable used is bound. There are no sorts yet; they
arrive with `:merge` functions, which need base-sorted outputs (`PLAN.md`, M9). This is
the one check that threads a `Scope`, and the one that asks anything of a query fact.

Its two binders are functions rather than judgments because neither can fail: an unbound
*pattern* variable is a match variable rather than an error, so a query only extends the
scope, and a `let` may shadow. -/

/-- The variables in scope. -/
abbrev Scope := List Var

/-- Every variable of `e` is in scope. -/
def Expr.Scoped (e : Expr) (Γ : Scope) : Prop := ∀ v ∈ e.vars, v ∈ Γ

/-- `e` is a constructor application.

Query facts and `expr` actions are required to be applications because **egglog's grammar
admits nothing else there**: a bare variable is `parse error: expected fact` as a query
fact, `parse error: expected action` in a rule head and `parse error: expected command` at
top level, and a literal is rejected the same way. Allowing them would leave every later
phase handling a case the real system cannot express. An `.eq` fact is unrestricted, as in
egglog, which accepts `(= a b)` between two bound variables. -/
def Expr.IsApp : Expr → Prop
  | .app _ _ => True
  | _ => False

/-- A query fact carries the application restriction and nothing else: a fact never fails
to scope, and what it binds is `Query.bind`.

**A `.values` atom's head function is deliberately unconstrained, here and in `Evaluable`**:
reading a non-constructor is what the atom is *for*, and it is the only legal read.
`PLAN.md`, "Arity checking", says why that is safe. -/
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

`Scoped` is not enough for `Expr.eval` to return a term: an application may be a *lookup*,
which has no evaluation rule at all, or a *primitive*, which may be handed operands of the
wrong sort. `Evaluable` rules both out, and `programStep_isSome` carries it beside
`WellScoped` rather than folding it in, so that "scoped" goes on meaning scope. It is the
first of the three checks that read a `Signature`, all threading it by `Cmd.sigBind`. -/

/-- The signature after a command: only a declaration writes it. `Cmd.bind` for
signatures, and exactly what `CmdStep`'s `.decl` case does. -/
def Cmd.sigBind : Cmd → Signature → Signature
  | .decl f d, sig => Function.update sig f (some d)
  | _, sig => sig

/-- Every application in `e` **builds**, so evaluating `e` cannot get stuck on one.

An application is one of four things, decided by the name: *undeclared*, which is an error
and which this rules out, so that `Program.Evaluable` is declare-before-use and needs no
separate check; a *lookup*, if the name is a declared merge function, which egglog rejects
in a rule head (`check_no_function_lookups_in_actions`) and this model rejects everywhere,
since reading is the query atom `Pattern.values`; a *primitive*, which computes; or a
declared constructor, which builds. Only the last always succeeds, and only the last is
admitted.

**Primitives are excluded rather than sort-checked**, which is where this is stricter than
egglog: `(min 1 2)` is a legal egglog action and `(min (A) (B))` a type error there, and
with no sorts in this model (`PLAN.md`, base sorts) nothing here can tell the two apart.
The one position primitives exist for is a `:merge` body, which is not walked into at all,
so nothing the model relies on is lost. `Impl/Check.lean`'s `Expr.noLookup` is the `Bool`
transcription of the constructor half; this is the half the semantics consumes. -/
def Expr.Evaluable (e : Expr) (sig : Signature) : Prop :=
  ∀ f ∈ e.fns, Prim.ofName f = none ∧ sig.IsCtor f

/-- `Action.Scoped`'s companion: every expression the action evaluates builds. -/
def Action.Evaluable : Action → Signature → Prop
  | .expr e, sig => e.Evaluable sig
  | .letBind _ e, sig => e.Evaluable sig
  | .union e₁ e₂, sig => e₁.Evaluable sig ∧ e₂.Evaluable sig
  | .set _ args out, sig => (∀ e ∈ args, e.Evaluable sig) ∧ ∀ e ∈ out, e.Evaluable sig

/-- Every applied name is a declared constructor. Nothing is asked of a query fact: a
query is *matched* rather than evaluated. -/
abbrev Check.evaluable : Check Signature where
  action := Action.Evaluable
  bindCmd := Cmd.sigBind

@[inherit_doc Check.evaluable] abbrev Actions.Evaluable := Check.evaluable.actions
@[inherit_doc Check.evaluable] abbrev Rule.Evaluable := Check.evaluable.rule
@[inherit_doc Check.evaluable] abbrev Cmd.Evaluable := Check.evaluable.cmd
@[inherit_doc Check.evaluable] abbrev Program.Evaluable := Check.evaluable.program

/-! ### `set` legality

Kept apart from `Evaluable` because it is additive: that says what an expression may
*build*, this says what an action may *write*. -/

/-- `(set (f …) …)` is legal only when `f` is a declared `:merge` or `:no-merge`
function — the one thing that has a merge specification to consult. A constructor and an
undeclared name are both excluded, which is egglog's `SetConstructorDisallowed` and its
"unbound function".

It is what keeps `Database.CtorRows` an invariant. A `set` writes the row `⟨f, as, [v]⟩`
for whatever `v` its out expression denotes, and `Database.ctorRowsOf` holds no such row
unless `v` is `.app f as`. -/
def Action.SetLegal : Action → Signature → Prop
  | .set f _ _, sig => sig.mergeOf f ≠ none
  | _, _ => True

/-- No `set` writes a constructor. Nothing is asked of a query fact, which writes
nothing. -/
abbrev Check.setLegal : Check Signature where
  action := Action.SetLegal
  bindCmd := Cmd.sigBind

@[inherit_doc Check.setLegal] abbrev Actions.SetLegal := Check.setLegal.actions
@[inherit_doc Check.setLegal] abbrev Rule.SetLegal := Check.setLegal.rule
@[inherit_doc Check.setLegal] abbrev Cmd.SetLegal := Check.setLegal.cmd
@[inherit_doc Check.setLegal] abbrev Program.SetLegal := Check.setLegal.program

/-! ### Freshness of a declaration

The other half of declare-before-use: `Evaluable` says a name must be declared *before* it
is applied, this says a name is declared *once*. Nothing in the dynamics forbids a
redeclaration — `Cmd.sigBind` is `Function.update` — but one can change what
`Signature.IsCtor` says of a name the state already has rows of, which is a derivation
`Spec/Merge.lean`'s `MCong.fd` had and loses. `Proofs/Merge.lean`'s `CmdStep.mono_recorded`
is where that bites; `Proofs/Counterexamples.lean`'s `mono_recorded_decl_false` is the
redeclaration that breaks it. -/

/-- Every declaration names something the signature does not already have. The walk asks
this *before* `Cmd.sigBind` installs the name; after, it would be reading back
`Function.update`'s own entry and would always fail. -/
abbrev Check.declFresh : Check Signature where
  decl f _ sig := sig f = none
  bindCmd := Cmd.sigBind

@[inherit_doc Check.declFresh] abbrev Cmd.DeclFresh := Check.declFresh.cmd
@[inherit_doc Check.declFresh] abbrev Program.DeclsFresh := Check.declFresh.program

/-! ### All four together -/

/-- **The front end accepts `p`.** One name for the four, for a reader who wants one; the
theorems take the projections instead, each only the ones it needs — `programStep_isSome`
is `wellScoped` and `evaluable`, `execM_contained` is `setLegal` alone — since taking the
bundle would be taking hypotheses they do not use. With `Impl/Check.lean`'s two, what a
front end demands in full is `WellFormed p sig ∧ WellArity p ∧ ReadsAreAtoms p`. -/
structure WellFormed (p : Program) (sig : Signature) : Prop where
  wellScoped : WellScoped p
  evaluable : p.Evaluable sig
  setLegal : p.SetLegal sig
  declsFresh : p.DeclsFresh sig

end Egglog
