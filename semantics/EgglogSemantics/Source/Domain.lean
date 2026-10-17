import EgglogSemantics.Spec.Scope
import EgglogSemantics.Spec.Eval

/-!
# The source fragment

Constructor discovery, source scoping, and `Program.Fragment`: the one definition of the
source programs the congruence pass compiles and the source proof checker accepts. Decided
by `instDecidableFragment`, so a program is checked by `decide`. The theorems about these
definitions are in `Proofs/Source/Domain.lean`.
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
  | .min a b => a.ctors ++ b.ctors
  | .ite lhs rhs yes no =>
      Expr.ctorsList lhs ++ Expr.ctorsList rhs ++ yes.ctors ++ no.ctors

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
  | .rule r => (r.query.flatMap Pattern.ctors) ++ (r.actions.flatMap Action.ctors)
  | .run _ => []
  | .saturate _ => []
  | .decl f d => [(f, d.arity)]
  | .check q => q.flatMap Pattern.ctors

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
    e.vars = [] ∧ ∃ t, e.eval src.sig [] = some t ∧ Env.lookup v src.env = some t

/-! ### Queries

A source pattern becomes one view read per subterm, joined on e-class variables — the
`check` expansion of `proof_encoding.md`, "Queries". The reads bind ids, so the outer
`(= e₁ e₂)` of a source equality pattern becomes id equality, which is egglog's own
`(= e3 e6)` and is why the rebuild has to have canonicalized the entries first. -/
/-- The rulesets a source `Cmd.saturate` names. -/
def Program.saturateRulesets (P : Program) : List RulesetName :=
  (P.filterMap fun c => match c with | .saturate R => some R | _ => none).dedup

/-! ### The source programs `encode` is defined for

`Program.Fragment` below specifies the constructor fragment and the naming, query, arity,
and head-legality conditions used by the correspondence theorem. -/

/-- The variables an action mentions, binders included. -/
def Action.vars : Action → List Var
  | .expr e => e.vars
  | .union e₁ e₂ => e₁.vars ∪ e₂.vars

/-- `Action.vars` over a command. -/
def Cmd.vars : Cmd → List Var
  | .rule r => r.query.vars ∪ (r.actions.flatMap Action.vars)
  | .run _ => []
  | .saturate _ => []
  | .decl _ _ => []
  | .check q => q.vars

/-- Every variable the program mentions. -/
def Program.vars (P : Program) : List Var := (P.flatMap Cmd.vars).dedup

/-- The ruleset names a command mentions: the one a rule joins, and the one a run fires. -/
def Cmd.rulesets : Cmd → List RulesetName
  | .rule r => [r.ruleset]
  | .run R => [R]
  | .saturate R => [R]
  | .decl _ _ => []
  | .check _ => []

/-- Every ruleset name the program mentions. -/
def Program.rulesets (P : Program) : List RulesetName := (P.flatMap Cmd.rulesets).dedup

/-- **Every name the source text mentions**, of the three kinds the generated namespace has
to stay clear of: a function name, a variable, a ruleset. One list because one condition is
asked of all three (`Fragment.noAt`). -/
def Program.names (P : Program) : List String :=
  P.ctors.map Prod.fst ++ P.vars ++ P.rulesets

/-! ### What the query flattening drops

`encodeQueryExpr` flattens an *application* and returns a leaf unchanged, so `encodePattern`
emits **no atom** for a source pattern whose expression is a bare literal or a bare variable.
Both are conditions on the source program's **text**, decidable, and both are folded into
`Program.Fragment` below; `Proofs/Congruence/Match.lean` is where each is consumed and where each
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
`Program.Fragment` states and implies it. -/
def Pattern.GroundedAt (src : Database) : Pattern → Prop
  | .expr e => ∀ l, e = .lit l → Term.lit l ∈ src.terms
  | .eq e₁ e₂ => (∀ l, e₁ = .lit l → Term.lit l ∈ src.terms) ∨
      (∀ l, e₂ = .lit l → Term.lit l ∈ src.terms)


/-- **The queries the flattening handles.** Every pattern of a rule's query is
`Pattern.Grounded` and `Pattern.Scoped` — no bare literal, and a fact is an application, as
in egglog — and the query is `Query.VarsKeyed`. Vacuous at every other command, which is
the only place a query can occur. -/
def Cmd.QueryEncodable : Cmd → Prop
  | .rule r => (∀ p ∈ r.query, p.Grounded ∧ p.Scoped) ∧ Query.VarsKeyed r.query
  | .check q => (∀ p ∈ q, p.Grounded ∧ p.Scoped) ∧ Query.VarsKeyed q
  | _ => True

/-! ### Rule-head legality

A stuck rule head contributes no writes. The fragment excludes undeclared applications
and literal unions so that source and compiled firings agree. -/

mutual

/-- No literal occurs in the expression. -/
def Expr.litFreeB : Expr → Bool
  | .lit _ => false
  | .var _ => true
  | .app _ args => Expr.litFreeListB args
  | .min a b => Expr.litFreeB a && Expr.litFreeB b
  | .ite lhs rhs yes no =>
      Expr.litFreeListB lhs && Expr.litFreeListB rhs && yes.litFreeB && no.litFreeB

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
  | .rule r => r.actions.all Action.litFreeB
  | _ => true

/-- `Action.UnionFree`, computed. -/
def Action.unionFreeB : Action → Bool
  | .union _ _ => false
  | _ => true

/-- No rule head asserts a union. -/
def Cmd.ruleUnionFreeB : Cmd → Bool
  | .rule r => r.actions.all Action.unionFreeB
  | _ => true

/-- Every function applied by a rule head is declared. -/
def Cmd.HeadsDeclared : Cmd → Signature → Prop
  | .rule r, sig => Actions.Declared r.actions sig
  | _, _ => True

/-- **Every name a rule head applies is declared before the rule.** `Actions.Declared` at
the signature `Cmd.sigBind` has reached, so this is "declared *earlier in the program*" and
not merely "declared somewhere": a declaration after the run that fires the rule is not in
the signature the firing reads, and `Cmd.sigBind` is the only thing that grows it. A rule
cannot fire before its own `Cmd.rule`, so declared-before-the-rule is
declared-before-every-firing.

A rule head's names are among `Program.ctors`. -/
@[simp] def Program.HeadsDeclared : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.HeadsDeclared sig ∧ Program.HeadsDeclared cs (c.sigBind sig)

/-! This is equivalent to the `Bool` accumulator it replaced —
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
  inferInstanceAs (Decidable (∀ f ∈ e.fns, sig f ≠ none))

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
  | .run _, _ => .isTrue trivial
  | .saturate _, _ => .isTrue trivial
  | .decl _ _, _ => .isTrue trivial
  | .check _, _ => .isTrue trivial

instance Program.decidableHeadsDeclared : ∀ (P : Program) (sig : Signature),
    Decidable (Program.HeadsDeclared P sig)
  | [], _ => .isTrue trivial
  | c :: cs, sig => @instDecidableAnd _ _ (Cmd.decidableHeadsDeclared c sig)
      (Program.decidableHeadsDeclared cs (c.sigBind sig))

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
  | .min _ _ => .isFalse (fun h => (h : False))
  | .ite _ _ _ _ => .isFalse (fun h => (h : False))

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
  | .run _ => .isTrue trivial
  | .saturate _ => .isTrue trivial
  | .decl _ _ => .isTrue trivial
  | .check _ => .isTrue trivial

instance Program.decidableHeadsScoped (P : Program) : Decidable P.HeadsScoped :=
  inferInstanceAs (Decidable (∀ c ∈ P, c.HeadScoped))

/-- Every name is applied at one arity. -/
def Program.AritiesAgree (P : Program) : Prop :=
  ∀ p ∈ P.ctors, ∀ q ∈ P.ctors, p.1 = q.1 → p.2 = q.2

instance (P : Program) : Decidable P.AritiesAgree :=
  inferInstanceAs (Decidable (∀ p ∈ P.ctors, ∀ q ∈ P.ctors, p.1 = q.1 → p.2 = q.2))

/-- **The source fragment**: the programs the congruence pass compiles, the completeness
theorem is about, and the source proof checker accepts. Declarations, names, queries,
arities, and rule heads satisfy the conditions recorded below. -/
@[blueprint "def:fragment"
  (title := /-- Supported source fragment -/)
  (statement := /-- Source declarations are constructors, expressions contain no $\min$,
  and source names avoid the generated \texttt{@} prefix. Expression patterns and build
  actions are applications. Equality patterns are not pairs of bare literals, and every
  query variable occurs as an application argument. Head variables are query-bound;
  head functions are declared before the rule, and each name has a consistent arity.
  Finally, either all heads are union-free or all head expressions are literal-free. -/)]
structure Program.Fragment (P : Program) : Prop where
  /-- Source declarations are constructors; future source functions must not be nested. -/
  ctorsOnly : P.CtorDecls
  /-- The source never computes with `min`: every expression builds. -/
  noMin : Program.OrderingFree P
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
  aritiesAgree : P.AritiesAgree
  /-- Every rule-head variable is query-bound, and a build action is an application.
  This excludes a bare unbound head that the compiler would otherwise silently erase. -/
  headsScoped : P.HeadsScoped

/-! #### Deciding the fragment -/

/-- `Cmd.CtorDecl`, computed. -/
def Cmd.ctorDeclB : Cmd → Bool
  | .decl _ d => d.merge.isNone
  | _ => true

instance (c : Cmd) : Decidable c.CtorDecl :=
  decidable_of_iff (c.ctorDeclB = true) (by
    cases c <;> simp [Cmd.ctorDeclB, Cmd.CtorDecl, Option.isNone_iff_eq_none])

/-- A bare literal, computed. -/
def Expr.isLitB : Expr → Bool
  | .lit _ => true
  | _ => false

instance Expr.decidableIsLitFree (e : Expr) : Decidable (∀ l, e ≠ .lit l) :=
  decidable_of_iff (e.isLitB = false) (by cases e <;> simp [Expr.isLitB])

instance : ∀ p : Pattern, Decidable p.Grounded
  | .expr e => inferInstanceAs (Decidable (∀ l, e ≠ .lit l))
  | .eq e₁ e₂ => inferInstanceAs (Decidable ((∀ l, e₁ ≠ .lit l) ∨ ∀ l, e₂ ≠ .lit l))

instance : ∀ p : Pattern, Decidable p.Scoped
  | .expr e => inferInstanceAs (Decidable e.IsApp)
  | .eq _ _ => .isTrue trivial

/-- `Expr.var v ∈ args`, computed: `Expr` carries no `BEq`. -/
def Expr.memVarB (v : Var) : List Expr → Bool
  | [] => false
  | .var w :: es => w == v || Expr.memVarB v es
  | _ :: es => Expr.memVarB v es

theorem Expr.memVarB_iff (v : Var) : ∀ args : List Expr,
    Expr.memVarB v args = true ↔ Expr.var v ∈ args
  | [] => by simp [Expr.memVarB]
  | .lit _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es
  | .var w :: es => by
      simp only [Expr.memVarB, Bool.or_eq_true, beq_iff_eq, List.mem_cons, Expr.var.injEq,
        Expr.memVarB_iff v es]
      exact or_congr_left eq_comm
  | .app _ _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es
  | .min _ _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es
  | .ite _ _ _ _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es

mutual

/-- `Expr.ArgVar`, computed. -/
def Expr.argVarB (v : Var) : Expr → Bool
  | .lit _ => false
  | .var _ => false
  | .app _ args => Expr.memVarB v args || Expr.argVarListB v args
  | .min a b => Expr.argVarB v a || Expr.argVarB v b
  | .ite _ _ _ _ => false

/-- `Expr.ArgVarList`, computed. -/
def Expr.argVarListB (v : Var) : List Expr → Bool
  | [] => false
  | e :: es => Expr.argVarB v e || Expr.argVarListB v es

end

mutual

theorem Expr.argVarB_iff (v : Var) : ∀ e : Expr, Expr.argVarB v e = true ↔ Expr.ArgVar v e
  | .ite _ _ _ _ => by simp [Expr.argVarB, Expr.ArgVar]
  | .lit _ => by simp [Expr.argVarB, Expr.ArgVar]
  | .var _ => by simp [Expr.argVarB, Expr.ArgVar]
  | .app _ args => by
      simp only [Expr.argVarB, Expr.ArgVar, Bool.or_eq_true, Expr.memVarB_iff,
        Expr.argVarListB_iff v args]
  | .min a b => by
      simp only [Expr.argVarB, Expr.ArgVar, Bool.or_eq_true, Expr.argVarB_iff v a,
        Expr.argVarB_iff v b]

theorem Expr.argVarListB_iff (v : Var) : ∀ es : List Expr,
    Expr.argVarListB v es = true ↔ Expr.ArgVarList v es
  | [] => by simp [Expr.argVarListB, Expr.ArgVarList]
  | e :: es => by
      simp only [Expr.argVarListB, Expr.ArgVarList, Bool.or_eq_true, Expr.argVarB_iff v e,
        Expr.argVarListB_iff v es]

end

/-- `Pattern.ArgVar`, computed. -/
def Pattern.argVarB (v : Var) : Pattern → Bool
  | .expr e => e.argVarB v
  | .eq e₁ e₂ => e₁.argVarB v || e₂.argVarB v

theorem Pattern.argVarB_iff (v : Var) (p : Pattern) :
    p.argVarB v = true ↔ Pattern.ArgVar v p := by
  cases p <;> simp [Pattern.argVarB, Pattern.ArgVar, Expr.argVarB_iff]

instance (v : Var) (p : Pattern) : Decidable (Pattern.ArgVar v p) :=
  decidable_of_iff (p.argVarB v = true) (Pattern.argVarB_iff v p)

instance (q : Query) : Decidable (Query.VarsKeyed q) :=
  inferInstanceAs (Decidable (∀ v ∈ Query.vars q, ∃ p ∈ q, Pattern.ArgVar v p))

instance : ∀ c : Cmd, Decidable c.QueryEncodable
  | .rule r => inferInstanceAs (Decidable ((∀ p ∈ r.query, p.Grounded ∧ p.Scoped) ∧
      Query.VarsKeyed r.query))
  | .run _ => .isTrue trivial
  | .saturate _ => .isTrue trivial
  | .decl _ _ => .isTrue trivial
  | .check q => inferInstanceAs (Decidable ((∀ p ∈ q, p.Grounded ∧ p.Scoped) ∧
      Query.VarsKeyed q))

instance (P : Program) : Decidable P.CtorDecls :=
  inferInstanceAs (Decidable (∀ c ∈ P, c.CtorDecl))

instance instDecidableFragment (P : Program) : Decidable P.Fragment :=
  decidable_of_iff (P.CtorDecls ∧ Program.OrderingFree P ∧ (∀ n ∈ P.names, ¬ "@".isPrefixOf n) ∧
      (∀ c ∈ P, c.QueryEncodable) ∧
      ((∀ c ∈ P, c.ruleUnionFreeB = true) ∨ ∀ c ∈ P, c.litFreeB = true) ∧
      Program.HeadsDeclared P (fun _ => none) ∧ P.AritiesAgree ∧ P.HeadsScoped)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2⟩,
      fun h => ⟨h.ctorsOnly, h.noMin, h.noAt, h.queryEncodable, h.noLitUnion, h.headsDeclared,
        h.aritiesAgree, h.headsScoped⟩⟩

/-- **Every application the source holds is a declared constructor's, applied.** -/
def Database.TermsBuild (src : Database) : Prop :=
  ∀ f as, Term.app f as ∈ src.terms → src.sig.IsCtor f

end Egglog
