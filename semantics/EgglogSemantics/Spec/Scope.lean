import Mathlib.Logic.Function.Basic
import EgglogSemantics.Spec.Term

/-!
# The front end's static checks

Six checks: `Scoped` — every variable used is bound; `Evaluable` — every applied name is a
declared constructor; `UnionLegal` — no `union` operand is a literal; `WidthOk` — every
application carries its declaration's column counts; `DeclsFresh` — no name is declared
twice; `MergeDeclared` — every name a `:merge` applies is declared. `Scoped` checks each
block in a fixed `Scope`; queries bind their pattern variables; `UnionLegal` reads no
context; the other four thread a `Signature`, moved only by `Cmd.sigBind`.
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

/-- An action scopes when each expression it evaluates does, plus the application
restriction on a bare `expr`. -/
def Action.Scoped : Action → Scope → Prop
  | .expr e, Γ => e.IsApp ∧ e.Scoped Γ
  | .union e₁ e₂, Γ => e₁.Scoped Γ ∧ e₂.Scoped Γ

/-- The scope a query's patterns bind. -/
def Query.bind (q : Query) (Γ : Scope) : Scope := Γ ∪ Query.vars q

/-- Every action in the same scope. -/
@[simp] def Actions.Scoped : List Action → Scope → Prop
  | [], _ => True
  | a :: as, Γ => a.Scoped Γ ∧ Actions.Scoped as Γ

/-- Its facts, then its head in the scope the query binds. -/
@[simp] def Rule.Scoped (r : Rule) (Γ : Scope) : Prop :=
  (∀ p ∈ r.query, p.Scoped) ∧ Actions.Scoped r.actions (Query.bind r.query Γ)

/-- A `:merge` body is walked into by `MergeDeclared` alone: it runs in the environment
`mergeEnv` builds rather than in the ambient context, so `Scoped` and `Evaluable` say
nothing about one. -/
@[simp] def Cmd.Scoped : Cmd → Scope → Prop
  | .action a, Γ => a.Scoped Γ
  | .rule r, Γ => r.Scoped Γ
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl _ _, _ => True

/-- Every command in the same initial scope. -/
@[simp] def Program.Scoped : Program → Scope → Prop
  | [], _ => True
  | c :: cs, Γ => c.Scoped Γ ∧ Program.Scoped cs Γ

/-- A program with no free variables: `Program.Scoped` from the empty scope. -/
def WellScoped (p : Program) : Prop := Program.Scoped p []

/-! ### Evaluability

`Scoped` is not enough for `Expr.eval` to return a term: an application may be a *lookup*
or a *primitive*. `Evaluable` rules both out. -/

/-- The signature after a command: only a declaration writes it, as in `CmdStep`. -/
def Cmd.sigBind : Cmd → Signature → Signature
  | .decl f d, sig => Function.update sig f (some d)
  | _, sig => sig

/-- Every application in `e` **builds**: its head is a declared constructor, so evaluating
`e` cannot get stuck on it. -/
def Expr.Evaluable (e : Expr) (sig : Signature) : Prop :=
  ∀ f ∈ e.fns, sig.IsCtor f

/-- A complete atom has a declared head and value-producing columns. -/
def Expr.AtomEvaluable : Expr → Signature → Prop
  | .app f cols, sig => (sig f).isSome = true ∧ ∀ g ∈ Expr.fnsList cols, sig.IsCtor g
  | e, sig => e.Evaluable sig

/-- `Action.Scoped`'s companion: every expression the action evaluates builds, and a
`union` operand is an application — the strongest sound stand-in for egglog's eq-sort
requirement, which `evalAction` refuses dynamically. A variable operand may hold a literal,
since a query binds one under a literal argument, so no check reading the expression alone
admits it. -/
def Action.Evaluable : Action → Signature → Prop
  | .expr e, sig => e.AtomEvaluable sig
  | .union e₁ e₂, sig => (e₁.IsApp ∧ e₁.Evaluable sig) ∧ e₂.IsApp ∧ e₂.Evaluable sig

@[simp] def Actions.Evaluable : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Evaluable sig ∧ Actions.Evaluable as sig

/-- Nothing is asked of a query fact, which is matched rather than evaluated. -/
@[simp] def Rule.Evaluable (r : Rule) (sig : Signature) : Prop :=
  Actions.Evaluable r.actions sig

@[simp] def Cmd.Evaluable : Cmd → Signature → Prop
  | .action a, sig => a.Evaluable sig
  | .rule r, sig => r.Evaluable sig
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl _ _, _ => True

/-- Each command in the signature the earlier ones leave. -/
@[simp] def Program.Evaluable : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.Evaluable sig ∧ Program.Evaluable cs (c.sigBind sig)

/-! ### `union` legality

egglog rejects a `union` on a sort that is not an eq sort statically (`constraint.rs:697-701`
against `typechecking.rs:966-969`, and `core.rs:514` of the lowering) where `Spec/Eval.lean`'s
`evalAction` only gets stuck on it. The typed rule needs base sorts, which this model does not
have, so this is its syntactic half: an operand is not a literal *expression*.
`Action.Evaluable` asks the stronger `Expr.IsApp` of one and its docstring records the same gap,
so the reach this adds is a `:merge` body, which no `Evaluable` walks into. -/

/-- Neither operand of a `union` is a literal. -/
def Action.UnionLegal : Action → Prop
  | .union e₁ e₂ => (∀ l, e₁ ≠ .lit l) ∧ ∀ l, e₂ ≠ .lit l
  | _ => True

@[simp] def Actions.UnionLegal : List Action → Prop
  | [] => True
  | a :: as => a.UnionLegal ∧ Actions.UnionLegal as

/-- `res` is evaluated rather than run. -/
@[simp] def MergeSpec.UnionLegal : MergeSpec → Prop
  | .merge body _ => Actions.UnionLegal body

/-- Its actions, and its `:merge` bodies: a `union` runs in either. -/
@[simp] def Cmd.UnionLegal : Cmd → Prop
  | .action a => a.UnionLegal
  | .rule r => Actions.UnionLegal r.actions
  | .run _ => True
  | .saturate _ => True
  | .decl _ d => ∀ ms ∈ d.merge, ms.UnionLegal

@[simp] def Program.UnionLegal : Program → Prop
  | [] => True
  | c :: cs => c.UnionLegal ∧ Program.UnionLegal cs

/-! ### Column widths

A complete atom carries every declared column; its children, and equality or union
operands, use value-expression widths. Evaluability and widths are separate because
`Expr.Evaluable` records names rather than application argument counts. -/

mutual

/-- Every application in `e` carries the argument count its declaration fixes. A name with
no entry has nothing to disagree with; that a program declares what it applies is
`Evaluable`'s business. -/
def Expr.WidthOk : Expr → Signature → Prop
  | .lit _, _ => True
  | .var _, _ => True
  | .app f args, sig =>
      (∀ d, sig f = some d → args.length = d.arity) ∧ Expr.WidthOkList args sig
  | .min a b, sig => Expr.WidthOk a sig ∧ Expr.WidthOk b sig

/-- `Expr.WidthOk` over an argument list. -/
def Expr.WidthOkList : List Expr → Signature → Prop
  | [], _ => True
  | e :: es, sig => Expr.WidthOk e sig ∧ Expr.WidthOkList es sig

end

/-- A complete atom uses the entry width at its root and value widths in its columns. -/
def Expr.AtomWidthOk : Expr → Signature → Prop
  | .app f cols, sig =>
      (∀ d, sig f = some d → cols.length = d.entryWidth) ∧ Expr.WidthOkList cols sig
  | .min a b, sig => Expr.WidthOk a sig ∧ Expr.WidthOk b sig
  | _, _ => True

/-- Complete atoms have their declared entry width; union operands use value widths. -/
def Action.WidthOk : Action → Signature → Prop
  | .expr e, sig => e.AtomWidthOk sig
  | .union e₁ e₂, sig => e₁.WidthOk sig ∧ e₂.WidthOk sig

@[simp] def Actions.WidthOk : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.WidthOk sig ∧ Actions.WidthOk as sig

/-- Nothing is asked of a query fact, which is matched rather than evaluated. -/
@[simp] def Rule.WidthOk (r : Rule) (sig : Signature) : Prop :=
  Actions.WidthOk r.actions sig

/-- One result expression per value column: `res` is what `MergeStep` writes into them.
This is the one check besides `MergeDeclared` that walks into a `:merge`, for the reason
`MergeDeclared`'s own heading gives — the body and `res` are where a merge writes. -/
@[simp] def MergeSpec.WidthOk : MergeSpec → Nat → Signature → Prop
  | .merge body res, n, sig =>
      res.length = n ∧ Actions.WidthOk body sig ∧ Expr.WidthOkList res sig

/-- Asked of the signature the declaration **installs**, as `Cmd.MergeDeclared` and unlike
`Cmd.DeclFresh`, so a `:merge` may name the function it resolves. -/
@[simp] def Cmd.WidthOk : Cmd → Signature → Prop
  | .action a, sig => a.WidthOk sig
  | .rule r, sig => r.WidthOk sig
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl f d, sig => ∀ ms ∈ d.merge, ms.WidthOk d.outArity ((Cmd.decl f d).sigBind sig)

/-- Check each command in the signature left by the earlier commands. -/
@[simp] def Program.WidthOk : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.WidthOk sig ∧ Program.WidthOk cs (c.sigBind sig)

/-! ### Freshness of a declaration

A redeclaration changes what the signature says of a name the state already has terms of,
breaking `Database.DeclaredTerms`. -/

@[simp] def Cmd.DeclFresh : Cmd → Signature → Prop
  | .decl f _, sig => sig f = none
  | .action _, _ => True
  | .rule _, _ => True
  | .run _, _ => True
  | .saturate _, _ => True

/-- Each command is asked **before** `Cmd.sigBind` installs its declaration; asked after,
the check would read back `Function.update`'s own entry and always fail. -/
@[simp] def Program.DeclsFresh : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.DeclFresh sig ∧ Program.DeclsFresh cs (c.sigBind sig)

/-! ### Declaredness of a `:merge`

The one check that walks into a `:merge`. `Evaluable` is the wrong demand there: a merge
body may `set` another merge function. -/

/-- Every name applied in `e` is a declared function, of any kind. -/
def Expr.Declared (e : Expr) (sig : Signature) : Prop :=
  ∀ f ∈ e.fns, sig f ≠ none

/-- A `set` head must be declared outright. -/
def Action.Declared : Action → Signature → Prop
  | .expr e, sig => e.Declared sig
  | .union e₁ e₂, sig => e₁.Declared sig ∧ e₂.Declared sig

@[simp] def Actions.Declared : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Declared sig ∧ Actions.Declared as sig

@[simp] def MergeSpec.Declared : MergeSpec → Signature → Prop
  | .merge body res, sig => Actions.Declared body sig ∧ ∀ e ∈ res, e.Declared sig

/-- Asked of the signature the declaration **installs**, so a `:merge` may name the function
it resolves. The opposite of `Cmd.DeclFresh`, which is asked before. -/
@[simp] def Cmd.MergeDeclared : Cmd → Signature → Prop
  | .decl f d, sig => ∀ ms ∈ d.merge, ms.Declared ((Cmd.decl f d).sigBind sig)
  | .action _, _ => True
  | .rule _, _ => True
  | .run _, _ => True
  | .saturate _, _ => True

@[simp] def Program.MergeDeclared : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.MergeDeclared sig ∧ Program.MergeDeclared cs (c.sigBind sig)

/-! ### Union-freedom

The one check that reads no signature, because it is about *positions* rather than names:
where a program may assert an equation. `Action.union` is the only action that asserts one
between distinct terms — every other write goes through `Database.addTerm`, which records
reflexive pairs alone — so a program with none keeps every state it reaches **diagonal**,
and on a diagonal state nothing is congruent to anything but itself. That is what makes
`Database.Recorded` and `Database.Contained` agree there, which is one of the two things
`Proofs/Merge.lean`'s two `Recorded` transports can be given; `Database.Diag` is the
state-level reading and `Proofs/Merge.lean` carries it. The other is `OrderingFree` below,
and neither condition implies the other.

It walks into a rule and into a `:merge`, since a `union` runs in either. -/

/-- The action that asserts an equation between distinct terms, ruled out. -/
def Action.UnionFree : Action → Prop
  | .union _ _ => False
  | _ => True

@[simp] def Actions.UnionFree : List Action → Prop
  | [] => True
  | a :: as => a.UnionFree ∧ Actions.UnionFree as

@[simp] def Rule.UnionFree (r : Rule) : Prop := Actions.UnionFree r.actions

/-- `res` is evaluated rather than run. -/
@[simp] def MergeSpec.UnionFree : MergeSpec → Prop
  | .merge body _ => Actions.UnionFree body

/-- A declaration is union-free when its `:merge` body is: the body is what a collision
runs. -/
def FnDecl.UnionFree (d : FnDecl) : Prop := ∀ ms ∈ d.merge, ms.UnionFree

/-- Every declared function's `:merge` body is union-free. Read of a *signature* because a
`MergeStep` reads the body it runs from one. -/
def Signature.UnionFree (sig : Signature) : Prop := ∀ f d, sig f = some d → d.UnionFree

@[simp] def Cmd.UnionFree : Cmd → Prop
  | .action a => a.UnionFree
  | .rule r => r.UnionFree
  | .run _ => True
  | .saturate _ => True
  | .decl _ d => d.UnionFree

/-- No signature threading: which actions a command carries does not depend on what is
declared. -/
@[simp] def Program.UnionFree : Program → Prop
  | [] => True
  | c :: cs => c.UnionFree ∧ Program.UnionFree cs

/-! ### Ordering-freedom

The other condition, and it is about where a program may apply `min`. It compares two terms
by `Term.blt`, a structural order, where egglog compares by e-class id. It is therefore not
stable under congruence: `union (f 1) (g 1)` lets `min (f 1) (f 2)` and `min (g 1) (f 2)`
settle on incongruent terms. On literals it is stable, since `Cong.eq_of_isLit` makes a
literal's class a singleton, but this untyped model cannot tell the two uses apart, so the
condition excludes `min` outright.

It walks into a rule — both its query, which evaluates its patterns, and its head — and
into a `:merge`, since a body and its result are evaluated too. -/

mutual

/-- Whether `min` occurs anywhere in `e`. -/
def Expr.hasMin : Expr → Bool
  | .lit _ => false
  | .var _ => false
  | .app _ args => Expr.hasMinList args
  | .min _ _ => true

def Expr.hasMinList : List Expr → Bool
  | [] => false
  | e :: es => e.hasMin || Expr.hasMinList es

end

/-- No `min` in `e`. -/
def Expr.OrderingFree (e : Expr) : Prop := e.hasMin = false

/-- `Expr.OrderingFree` over an argument list. -/
def Expr.OrderingFreeList (es : List Expr) : Prop := Expr.hasMinList es = false

/-- A query pattern is evaluated, so it carries the condition too. -/
def Pattern.OrderingFree : Pattern → Prop
  | .expr e => e.OrderingFree
  | .eq e₁ e₂ => e₁.OrderingFree ∧ e₂.OrderingFree

def Action.OrderingFree : Action → Prop
  | .expr e => e.OrderingFree
  | .union e₁ e₂ => e₁.OrderingFree ∧ e₂.OrderingFree

@[simp] def Actions.OrderingFree : List Action → Prop
  | [] => True
  | a :: as => a.OrderingFree ∧ Actions.OrderingFree as

/-- Both halves: a query pattern is evaluated against the database, a head action against
the substitution. -/
@[simp] def Rule.OrderingFree (r : Rule) : Prop :=
  (∀ p ∈ r.query, p.OrderingFree) ∧ Actions.OrderingFree r.actions

/-- A `:merge` evaluates both its body and its result — and it
*compares* the two colliding value tuples, which is the second instability here.
`Spec/Step.lean`'s `MergeConflict` decides whether a collision fires by **identity** on
those tuples, and identity is no more stable under congruence than `min` is: moved
to congruent values a firing can become a skip. Only a declaration that always conflicts
survives the move — `FnDecl.unchangedWidth = none`, which is `body = []` with no
`:internal-identity-vals`. Every `:merge` *expression* is that, `:merge (min old new)` and
every lattice in this development included; `FnDecl.OrderingFree` carries the other half. -/
@[simp] def MergeSpec.OrderingFree : MergeSpec → Prop
  | .merge body res => body = [] ∧ Expr.OrderingFreeList res

@[inherit_doc MergeSpec.OrderingFree]
def FnDecl.OrderingFree (d : FnDecl) : Prop :=
  d.identityVals = none ∧ ∀ ms ∈ d.merge, ms.OrderingFree

/-- Read of a *signature*, because a `MergeStep` reads the body it runs from one, as
`Signature.UnionFree`. -/
def Signature.OrderingFree (sig : Signature) : Prop :=
  ∀ f d, sig f = some d → d.OrderingFree

@[simp] def Cmd.OrderingFree : Cmd → Prop
  | .action a => a.OrderingFree
  | .rule r => r.OrderingFree
  | .run _ => True
  | .saturate _ => True
  | .decl _ d => d.OrderingFree

/-- No signature threading, as `Program.UnionFree`. -/
@[simp] def Program.OrderingFree : Program → Prop
  | [] => True
  | c :: cs => c.OrderingFree ∧ Program.OrderingFree cs

instance (e : Expr) : Decidable e.OrderingFree := inferInstanceAs (Decidable (_ = false))
instance (es : List Expr) : Decidable (Expr.OrderingFreeList es) :=
  inferInstanceAs (Decidable (_ = false))
instance : ∀ p : Pattern, Decidable p.OrderingFree
  | .expr e => inferInstanceAs (Decidable e.OrderingFree)
  | .eq a b => inferInstanceAs (Decidable (a.OrderingFree ∧ b.OrderingFree))
instance : ∀ a : Action, Decidable a.OrderingFree
  | .expr e => inferInstanceAs (Decidable e.OrderingFree)
  | .union a b => inferInstanceAs (Decidable (a.OrderingFree ∧ b.OrderingFree))
instance instDecidableActionsOrderingFree : ∀ as : List Action, Decidable (Actions.OrderingFree as)
  | [] => inferInstanceAs (Decidable True)
  | a :: as => @instDecidableAnd _ _ inferInstance (instDecidableActionsOrderingFree as)
instance (r : Rule) : Decidable r.OrderingFree :=
  inferInstanceAs (Decidable ((∀ p ∈ r.query, p.OrderingFree) ∧ Actions.OrderingFree r.actions))
instance : ∀ ms : MergeSpec, Decidable ms.OrderingFree
  | .merge body res => decidable_of_iff (body.isEmpty = true ∧ Expr.OrderingFreeList res)
      (by simp [List.isEmpty_iff])
instance (d : FnDecl) : Decidable d.OrderingFree :=
  decidable_of_iff (d.identityVals = none ∧ ∀ ms ∈ d.merge.toList, ms.OrderingFree)
    (by unfold FnDecl.OrderingFree; rcases d.merge with _ | ms <;> simp)
instance : ∀ c : Cmd, Decidable c.OrderingFree
  | .action a => inferInstanceAs (Decidable a.OrderingFree)
  | .rule r => inferInstanceAs (Decidable r.OrderingFree)
  | .run _ => inferInstanceAs (Decidable True)
  | .saturate _ => inferInstanceAs (Decidable True)
  | .decl _ d => inferInstanceAs (Decidable d.OrderingFree)
instance instDecidableProgramOrderingFree : ∀ P : Program, Decidable (Program.OrderingFree P)
  | [] => inferInstanceAs (Decidable True)
  | c :: cs => @instDecidableAnd _ _ inferInstance (instDecidableProgramOrderingFree cs)

end Egglog
