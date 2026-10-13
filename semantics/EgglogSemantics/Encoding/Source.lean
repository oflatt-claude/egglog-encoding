import EgglogSemantics.Proofs.Step
import EgglogSemantics.Tests.Egg

/-!
# Source-program analysis for the encoding passes

Constructor discovery, source scoping, and the supported correspondence domain.
This module does not import either program transformation or a proof checker.
-/

namespace Egglog

/-! ### The constructors a program mentions

Read declarations and expression occurrences so each pass can prepare its generated
tables before compiling source commands. Arity consistency is a separate domain condition. -/
mutual

/-- The `(name, arity)` pairs an expression applies. -/
def Expr.ctors : Expr → List (FnName × Nat)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args.length) :: Expr.ctorsList args

/-- `Expr.ctors` over an argument list. -/
def Expr.ctorsList : List Expr → List (FnName × Nat)
  | [] => []
  | e :: es => e.ctors ++ Expr.ctorsList es

end

/-- `Expr.ctors` over a pattern. -/
def Pattern.ctors : Pattern → List (FnName × Nat)
  | .expr e => e.ctors
  | .eq e₁ e₂ => e₁.ctors ++ e₂.ctors

/-- Constructor occurrences in a source action. -/
def Action.ctors : Action → List (FnName × Nat)
  | .expr e => e.ctors
  | .union e₁ e₂ => e₁.ctors ++ e₂.ctors

/-- `Expr.ctors` over a command. A declaration counts even if nothing applies it. -/
def Cmd.ctors : Cmd → List (FnName × Nat)
  | .action a => a.ctors
  | .rule r => (r.query.flatMap Pattern.ctors) ++ (r.actions.flatMap Action.ctors)
  | .run _ => []
  | .saturate _ => []
  | .decl f d => [(f, d.arity)]

/-- Every function name and arity the program mentions, deduplicated. -/
def Program.ctors (P : Program) : List (FnName × Nat) := (P.flatMap Cmd.ctors).dedup

/-- The first expression substitution for a variable, matching `Env.lookup` order.
These are proof-level substitutions; the source language has no binding actions. -/
def Expr.lookupG (v : Var) : List (Var × Expr) → Option Expr
  | [] => none
  | (w, e) :: rest => if v = w then some e else Expr.lookupG v rest

/-- Every definition the substitution carries is closed. -/
def Expr.ClosedG (G : List (Var × Expr)) : Prop :=
  ∀ v e, Expr.lookupG v G = some e → e.vars = []

def Database.GlobalsInline (src : Database) (G : List (Var × Expr)) : Prop :=
  ∀ v e, Expr.lookupG v G = some e →
    e.vars = [] ∧ (∀ fk ∈ e.ctors, Prim.ofName fk.1 = none) ∧
      ∃ t, e.eval src.sig [] = some t ∧ Env.lookup v src.env = some t

/-- The clause moves to a state that still builds what it built and still binds what it
bound. -/
theorem Database.GlobalsInline.mono_src {src src' : Database} {G : List (Var × Expr)}
    (h : src.GlobalsInline G)
    (hsig : ∀ (e : Expr) (t : Term), e.eval src.sig [] = some t → e.eval src'.sig [] = some t)
    (henv : ∀ v t, Env.lookup v src.env = some t → Env.lookup v src'.env = some t) :
    src'.GlobalsInline G := by
  intro v e he
  obtain ⟨hcl, hnp, t, hev, hlk⟩ := h v e he
  exact ⟨hcl, hnp, t, hsig e t hev, henv v t hlk⟩

/-- The static half of the clause, which is what the three text conditions need. -/
theorem Database.GlobalsInline.closed {src : Database} {G : List (Var × Expr)}
    (h : src.GlobalsInline G) : Expr.ClosedG G := fun v e he => (h v e he).1

/-- The environment and the signature are both unmoved, which is the shape a run, a
saturation and a rule declaration all have. -/
theorem Database.GlobalsInline.of_eq {src src' : Database} {G : List (Var × Expr)}
    (h : src.GlobalsInline G) (hsig : src'.sig = src.sig) (henv : src'.env = src.env) :
    src'.GlobalsInline G :=
  h.mono_src (fun _ _ he => by rw [hsig]; exact he) (fun _ _ hv => by rw [henv]; exact hv)

/-! ### Queries

A source pattern becomes one view read per subterm, joined on e-class variables — the
`check` expansion of `proof_encoding.md`, "Queries". The reads bind ids, so the outer
`(= e₁ e₂)` of a source equality pattern becomes id equality, which is egglog's own
`(= e3 e6)` and is why the rebuild has to have canonicalized the entries first. -/
/-- The rulesets a source `Cmd.saturate` names. -/
def Program.saturateRulesets (P : Program) : List RulesetName :=
  (P.filterMap fun c => match c with | .saturate R => some R | _ => none).dedup

/-! ### The source programs `encode` is defined for

`Program.EncodeDomain` below specifies the constructor fragment and the naming, query,
arity, and head-legality conditions used by the correspondence theorem. -/

/-- Compatibility marker for the former separate entry-pattern constructor. Complete
atoms share the expression case, so this imposes no restriction on current patterns. -/
def Pattern.NoValues : Pattern → Prop
  | _ => True

/-- The variables an action mentions, binders included. -/
def Action.vars : Action → List Var
  | .expr e => e.vars
  | .union e₁ e₂ => e₁.vars ∪ e₂.vars

/-- `Action.vars` over a command. -/
def Cmd.vars : Cmd → List Var
  | .action a => a.vars
  | .rule r => r.query.vars ∪ (r.actions.flatMap Action.vars)
  | .run _ => []
  | .saturate _ => []
  | .decl _ _ => []

/-- Every variable the program mentions. -/
def Program.vars (P : Program) : List Var := (P.flatMap Cmd.vars).dedup

/-- The ruleset names a command mentions: the one a rule joins, and the one a run fires. -/
def Cmd.rulesets : Cmd → List RulesetName
  | .rule r => [r.ruleset]
  | .run R => [R]
  | .saturate R => [R]
  | .action _ => []
  | .decl _ _ => []

/-- Every ruleset name the program mentions. -/
def Program.rulesets (P : Program) : List RulesetName := (P.flatMap Cmd.rulesets).dedup

/-- **Every name the source text mentions**, of the three kinds the generated namespace has
to stay clear of: a function name, a variable, a ruleset. One list because one condition is
asked of all three (`EncodeDomain.noAt`). -/
def Program.names (P : Program) : List String :=
  P.ctors.map Prod.fst ++ P.vars ++ P.rulesets

/-! ### What the query flattening drops

`encodeQueryExpr` flattens an *application* and returns a leaf unchanged, so `encodePattern`
emits **no atom** for a source pattern whose expression is a bare literal or a bare variable.
Both are conditions on the source program's **text**, decidable, and both are folded into
`Program.EncodeDomain` below; `Encoding/Match.lean` is where each is consumed and where each
is refuted. -/
/-- **The pattern has a witness position.** `Matches` asks for a term the source *holds*
congruent to the instance, and a bare literal has none: the source may never have built it,
and `encodePattern` emits no atom that would say it did. -/
def Pattern.Grounded : Pattern → Prop
  | .expr e => ∀ l, e ≠ .lit l
  | .eq e₁ e₂ => (∀ l, e₁ ≠ .lit l) ∨ (∀ l, e₂ ≠ .lit l)

/-- **The witness position exists at this source state.** `Pattern.Grounded` says the pattern
is not a bare literal, which is one way to have a witness; a bare literal the source **holds**
is another, and that is the one a substituted global takes — `Expr.substGlobals` writes a
literal-valued global's definition into the query, and the source's own environment binds the
name to that term.

This is what the correspondence consumes; `Pattern.Grounded` is the text condition
`Program.EncodeDomain` states and implies it. -/
def Pattern.GroundedAt (src : Database) : Pattern → Prop
  | .expr e => ∀ l, e = .lit l → Term.lit l ∈ src.terms
  | .eq e₁ e₂ => (∀ l, e₁ = .lit l → Term.lit l ∈ src.terms) ∨
      (∀ l, e₂ = .lit l → Term.lit l ∈ src.terms)

@[inherit_doc Pattern.GroundedAt]
theorem Pattern.Grounded.groundedAt {src : Database} :
    ∀ {p : Pattern}, p.Grounded → p.GroundedAt src
  | .expr _, h => fun l he => absurd he (h l)
  | .eq _ _, h => h.imp (fun h₁ l he => absurd he (h₁ l)) (fun h₂ l he => absurd he (h₂ l))

mutual

/-- The variable occurs as an **argument of an application**: a key column of one of the view
reads `encodeQueryExpr` emits. -/
def Expr.ArgVar (v : Var) : Expr → Prop
  | .lit _ => False
  | .var _ => False
  | .app _ args => Expr.var v ∈ args ∨ Expr.ArgVarList v args

/-- `Expr.ArgVar` over an argument list. -/
def Expr.ArgVarList (v : Var) : List Expr → Prop
  | [] => False
  | e :: es => Expr.ArgVar v e ∨ Expr.ArgVarList v es

end

@[inherit_doc Expr.ArgVar]
def Pattern.ArgVar (v : Var) : Pattern → Prop
  | .expr e => Expr.ArgVar v e
  | .eq e₁ e₂ => Expr.ArgVar v e₁ ∨ Expr.ArgVar v e₂

def Query.VarsKeyed (q : Query) : Prop := ∀ v ∈ Query.vars q, ∃ p ∈ q, Pattern.ArgVar v p

/-- **The queries the flattening handles.** `Pattern.Grounded` and `Pattern.NoValues` at
every pattern of a rule's query, and `Query.VarsKeyed` at the query. Vacuous at every other
command, which is the only place a query can occur. -/
def Cmd.QueryEncodable : Cmd → Prop
  | .rule r => (∀ p ∈ r.query, p.Grounded ∧ p.NoValues) ∧ Query.VarsKeyed r.query
  | _ => True

/-! ### The heads the source cannot run

A source rule head that gets **stuck** contributes nothing and its encoding's head writes
anyway. `RuleResults` asks `evalLocalActions` for a `some`, so a stuck block silently drops
the firing — where a stuck *top-level* action drops `ProgramStep` and makes the claim
vacuous, a stuck rule head leaves the source running and the target one entry ahead. **Three**
shapes do it; the two clauses below exclude two of them, and the third is not excluded by any
clause — see `Encoding/Correspond.lean`'s `bare_build_invents_equality`, a head that builds a
bare variable the query does not bind, which `encodeBuild` emits no action for at all:

* **A `union` on a literal.** `evalAction` refuses it — egglog's type checker does, and this
  untyped model cannot see it until the operands are values — while `encodeAction` emits
  `.set @UF [ordering-max …] […]`, which `execAction` never refuses. Only a **rule head**
  needs excluding, and either by having no `union` or by the program building no literal at
  all: a bare variable operand can be bound to a literal too, and it is bound to a term the
  source holds.
  `encode_corresponds_unions_literals` is the program, and it refutes the *conclusion*
  rather than only its residue: the bogus edge is what a rebuild column rule then re-keys a
  view entry along.
* **An application of a name nobody declared.** `Expr.eval` needs `Signature.IsCtor`, so the
  source head is stuck, while `encodePrelude` declares a skolem constructor for **every**
  name `Program.ctors` reads off the uses — declared or not. `execM_soundTerms_false` is that
  program.

Both are decidable conditions on the source program's text, so a witness discharges them by
`decide` and `difftest`'s census counts exactly them. Neither costs the corpus
anything: all seventy in-domain cases are literal-free and are run with their constructors
declared up front (`Program.declared`). -/

mutual

/-- No literal occurs in the expression. -/
def Expr.litFreeB : Expr → Bool
  | .lit _ => false
  | .var _ => true
  | .app _ args => Expr.litFreeListB args

/-- `Expr.litFreeB` over an argument list. -/
def Expr.litFreeListB : List Expr → Bool
  | [] => true
  | e :: es => Expr.litFreeB e && Expr.litFreeListB es

end

/-- No literal occurs in an expression the action **evaluates**. Patterns are not read: a
literal in a query builds nothing, and a variable is only ever bound to a term the source
holds. -/
def Action.litFreeB : Action → Bool
  | .expr e => e.litFreeB
  | .union e₁ e₂ => e₁.litFreeB && e₂.litFreeB

/-- `Action.litFreeB` at every action a command runs. -/
def Cmd.litFreeB : Cmd → Bool
  | .action a => a.litFreeB
  | .rule r => r.actions.all Action.litFreeB
  | _ => true

/-- `Action.UnionFree`, computed. -/
def Action.unionFreeB : Action → Bool
  | .union _ _ => false
  | _ => true

theorem Action.unionFreeB_iff (a : Action) : a.unionFreeB = true ↔ a.UnionFree := by
  cases a <;> simp [Action.unionFreeB, Action.UnionFree]

theorem Actions.unionFreeB_iff : ∀ as : List Action,
    as.all Action.unionFreeB = true ↔ Actions.UnionFree as
  | [] => by simp
  | a :: as => by
      simp only [List.all_cons, Bool.and_eq_true, Actions.UnionFree, Action.unionFreeB_iff,
        Actions.unionFreeB_iff as]

/-- No **rule head** asserts a `union`. A top-level `union` needs no clause: on a literal it
sticks the source run outright, and `ProgramStep` then has no state for the correspondence to
be about — which is what `difftest`'s `litUnionCase` reports as `sourceStuck`. -/
def Cmd.ruleUnionFreeB : Cmd → Bool
  | .rule r => r.actions.all Action.unionFreeB
  | _ => true

@[inherit_doc Cmd.ruleUnionFreeB]
theorem Cmd.ruleUnionFreeB_iff (r : Rule) :
    (Cmd.rule r).ruleUnionFreeB = true ↔ r.UnionFree :=
  Actions.unionFreeB_iff r.actions

/-- `Spec/Scope.lean`'s `Action.Declared` at a rule's head, and nothing at any other
command: a stuck **top-level** action drops `ProgramStep` and makes the claim vacuous, so
only a head needs the condition. -/
def Cmd.HeadsDeclared : Cmd → Signature → Prop
  | .rule r, sig => Actions.Declared r.actions sig
  | _, _ => True

/-- **Every name a rule head applies is declared before the rule.** `Actions.Declared` at
the signature `Cmd.sigBind` has reached, so this is "declared *earlier in the program*" and
not merely "declared somewhere": a declaration after the run that fires the rule is not in
the signature the firing reads, and `Cmd.sigBind` is the only thing that grows it. A rule
cannot fire before its own `Cmd.rule`, so declared-before-the-rule is
declared-before-every-firing.

`Action.Declared` lets a **primitive** stand in for a declaration, since a `:merge` body is
where primitives are legal; `EncodeDomain.noPrim` closes that off for a source program, and a
rule head's names are among `Program.ctors`. -/
@[simp] def Program.HeadsDeclared : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.HeadsDeclared sig ∧ Program.HeadsDeclared cs (c.sigBind sig)

/-! Given `noPrim` this is equivalent to the `Bool` accumulator it replaced —
`Program.HeadsDeclared P (fun _ => none) ↔ headCtorsDeclaredB [] P` — for **every** program and
not only the corpus, checked out of tree and left there, since stating it in the build needs
that `Bool` back. In tree the evidence is `encodeDomainB_iff` and the census pins. -/

/-! #### Deciding the two checks the domain takes from `Spec/Scope.lean`

Both read a signature entry, and `FnDecl` carries no `DecidableEq`, so the instances go
through `Option.isSome`. With them a witness discharges either clause by `decide`, as it did
the `Bool` these replaced. -/

instance decidableNeNone {α : Type u} (o : Option α) : Decidable (o ≠ none) :=
  decidable_of_iff (o.isSome = true) (by cases o <;> simp)

instance Expr.decidableDeclared (e : Expr) (sig : Signature) : Decidable (e.Declared sig) :=
  inferInstanceAs (Decidable (∀ f ∈ e.fns, Prim.ofName f ≠ none ∨ sig f ≠ none))

instance Action.decidableDeclared : ∀ (a : Action) (sig : Signature),
    Decidable (a.Declared sig)
  | .expr e, sig => inferInstanceAs (Decidable (e.Declared sig))
  | .union e₁ e₂, sig => inferInstanceAs (Decidable (e₁.Declared sig ∧ e₂.Declared sig))

instance Actions.decidableDeclared : ∀ (as : List Action) (sig : Signature),
    Decidable (Actions.Declared as sig)
  | [], _ => .isTrue trivial
  | a :: as, sig =>
      @instDecidableAnd _ _ (Action.decidableDeclared a sig) (Actions.decidableDeclared as sig)

instance Cmd.decidableHeadsDeclared : ∀ (c : Cmd) (sig : Signature),
    Decidable (c.HeadsDeclared sig)
  | .rule r, sig => inferInstanceAs (Decidable (Actions.Declared r.actions sig))
  | .action _, _ => .isTrue trivial
  | .run _, _ => .isTrue trivial
  | .saturate _, _ => .isTrue trivial
  | .decl _ _, _ => .isTrue trivial

instance Program.decidableHeadsDeclared : ∀ (P : Program) (sig : Signature),
    Decidable (Program.HeadsDeclared P sig)
  | [], _ => .isTrue trivial
  | c :: cs, sig => @instDecidableAnd _ _ (Cmd.decidableHeadsDeclared c sig)
      (Program.decidableHeadsDeclared cs (c.sigBind sig))

instance Action.decidableSetLegal : ∀ (a : Action) (sig : Signature),
    Decidable (a.SetLegal sig)
  | .expr _, _ => .isTrue trivial
  | .union _ _, _ => .isTrue trivial

instance Actions.decidableSetLegal : ∀ (as : List Action) (sig : Signature),
    Decidable (Actions.SetLegal as sig)
  | [], _ => .isTrue trivial
  | a :: as, sig =>
      @instDecidableAnd _ _ (Action.decidableSetLegal a sig) (Actions.decidableSetLegal as sig)

instance Cmd.decidableSetLegal : ∀ (c : Cmd) (sig : Signature), Decidable (c.SetLegal sig)
  | .action a, sig => inferInstanceAs (Decidable (a.SetLegal sig))
  | .rule r, sig => inferInstanceAs (Decidable (Actions.SetLegal r.actions sig))
  | .run _, _ => .isTrue trivial
  | .saturate _, _ => .isTrue trivial
  | .decl _ _, _ => .isTrue trivial

instance Program.decidableSetLegal : ∀ (P : Program) (sig : Signature),
    Decidable (Program.SetLegal P sig)
  | [], _ => .isTrue trivial
  | c :: cs, sig => @instDecidableAnd _ _ (Cmd.decidableSetLegal c sig)
      (Program.decidableSetLegal cs (c.sigBind sig))

/-! #### The head-scope check, and deciding it

`Spec/Scope.lean`'s `Actions.Scoped` at a rule's own query variables. Every action in
the head uses the same query substitution; actions do not introduce bindings. -/

/-- **Every variable a rule head reads is one the rule's own query binds.**
`Actions.Scoped`'s own `Expr.IsApp` at a bare build is part of it.

Stated on the program's text, and *stronger* than `Rule.HeadScoped` at the source state,
which would also let a head read a global. The weaker form is what the proofs spend; this is
what a witness can decide. -/
def Cmd.HeadScoped : Cmd → Prop
  | .rule r => Actions.Scoped r.actions (Query.vars r.query)
  | _ => True

@[inherit_doc Cmd.HeadScoped]
def Program.HeadsScoped (P : Program) : Prop := ∀ c ∈ P, c.HeadScoped

instance Expr.decidableIsApp : ∀ e : Expr, Decidable e.IsApp
  | .app _ _ => .isTrue trivial
  | .lit _ => .isFalse (fun h => (h : False))
  | .var _ => .isFalse (fun h => (h : False))

instance Expr.decidableScoped (e : Expr) (Γ : Scope) : Decidable (e.Scoped Γ) :=
  inferInstanceAs (Decidable (∀ v ∈ e.vars, v ∈ Γ))

instance Action.decidableScoped : ∀ (a : Action) (Γ : Scope), Decidable (a.Scoped Γ)
  | .expr e, Γ => inferInstanceAs (Decidable (e.IsApp ∧ e.Scoped Γ))
  | .union e₁ e₂, Γ => inferInstanceAs (Decidable (e₁.Scoped Γ ∧ e₂.Scoped Γ))

instance Actions.decidableScoped : ∀ (as : List Action) (Γ : Scope),
    Decidable (Actions.Scoped as Γ)
  | [], _ => .isTrue trivial
  | a :: as, Γ => @instDecidableAnd _ _ (Action.decidableScoped a Γ)
      (Actions.decidableScoped as Γ)

instance Cmd.decidableHeadScoped : ∀ c : Cmd, Decidable c.HeadScoped
  | .rule r => inferInstanceAs (Decidable (Actions.Scoped r.actions (Query.vars r.query)))
  | .action _ => .isTrue trivial
  | .run _ => .isTrue trivial
  | .saturate _ => .isTrue trivial
  | .decl _ _ => .isTrue trivial

instance Program.decidableHeadsScoped (P : Program) : Decidable P.HeadsScoped :=
  inferInstanceAs (Decidable (∀ c ∈ P, c.HeadScoped))

/-- Constructor programs supported by the correspondence theorem: declarations, names,
queries, arities, and rule heads satisfy the conditions recorded below. -/
structure Program.EncodeDomain (P : Program) : Prop where
  /-- The source declares only constructors. Generated target tables may be functions. -/
  ctorsOnly : P.CtorDecls
  /-- Compatibility condition for the existing proof interfaces; automatic in the
  current action syntax. -/
  setLegal : Program.SetLegal P (fun _ => none)
  /-- Every source application builds a constructor rather than evaluating a primitive. -/
  noPrim : ∀ fk ∈ P.ctors, Prim.ofName fk.1 = none
  /-- Source function, variable, and ruleset names cannot collide with generated names. -/
  noAt : ∀ n ∈ P.names, ¬ "@".isPrefixOf n
  /-- Patterns supply constructor reads and key every variable. Flattening a bare literal
  pattern would otherwise erase its existence requirement. -/
  queryEncodable : ∀ c ∈ P, c.QueryEncodable
  /-- Either no action performs a union, or no literal can be built and handed to one. -/
  noLitUnion : (∀ c ∈ P, c.ruleUnionFreeB = true) ∨ ∀ c ∈ P, c.litFreeB = true
  /-- A source rule head applies only functions declared before the rule. -/
  headsDeclared : Program.HeadsDeclared P (fun _ => none)
  /-- Each source function has a unique arity. -/
  aritiesAgree : P.arityConflicts = []
  /-- Every rule-head variable is query-bound, and a build action is an application.
  This excludes a bare unbound head that the compiler would otherwise silently erase. -/
  headsScoped : P.HeadsScoped

/-- **Every application the source holds is a declared constructor's, applied.** -/
def Database.TermsBuild (src : Database) : Prop :=
  ∀ f as, Term.app f as ∈ src.terms → Prim.ofName f = none ∧ src.sig.IsCtor f

end Egglog
