import EgglogSemantics.Encoding.Subst
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

mutual

def Expr.inlineGlobals (G : List (Var × Expr)) : Expr → Expr
  | .lit l => .lit l
  | .var v => (Expr.lookupG v G).getD (.var v)
  | .app f args => .app f (Expr.inlineGlobalsList G args)

/-- `Expr.inlineGlobals` over an argument list. -/
def Expr.inlineGlobalsList (G : List (Var × Expr)) : List Expr → List Expr
  | [] => []
  | e :: es => Expr.inlineGlobals G e :: Expr.inlineGlobalsList G es

end

mutual

/-- **Inlining introduces no primitive** the definitions did not already carry. -/
theorem ctors_inlineGlobals_noPrim {G : List (Var × Expr)}
    (hG : ∀ (u : Var) (e' : Expr), Expr.lookupG u G = some e' →
      ∀ fk ∈ e'.ctors, Prim.ofName fk.1 = none) :
    ∀ (e : Expr), (∀ fk ∈ e.ctors, Prim.ofName fk.1 = none) →
      ∀ fk ∈ (e.inlineGlobals G).ctors, Prim.ofName fk.1 = none
  | .lit _, _, fk, hfk => absurd hfk (by simp [Expr.inlineGlobals, Expr.ctors])
  | .var v, _, fk, hfk => by
      rw [Expr.inlineGlobals] at hfk
      cases hE : Expr.lookupG v G with
      | none => rw [hE, Option.getD_none] at hfk; exact absurd hfk (by simp [Expr.ctors])
      | some e' => rw [hE, Option.getD_some] at hfk; exact hG v e' hE fk hfk
  | .app f args, h, fk, hfk => by
      rw [Expr.inlineGlobals, Expr.ctors, List.mem_cons] at hfk
      rcases hfk with rfl | hfk
      · exact h (f, args.length) (by rw [Expr.ctors]; exact List.mem_cons_self)
      · exact ctorsList_inlineGlobals_noPrim hG args
          (fun gk hgk => h gk (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hgk)) fk hfk

@[inherit_doc ctors_inlineGlobals_noPrim]
theorem ctorsList_inlineGlobals_noPrim {G : List (Var × Expr)}
    (hG : ∀ (u : Var) (e' : Expr), Expr.lookupG u G = some e' →
      ∀ fk ∈ e'.ctors, Prim.ofName fk.1 = none) :
    ∀ (es : List Expr), (∀ fk ∈ Expr.ctorsList es, Prim.ofName fk.1 = none) →
      ∀ fk ∈ Expr.ctorsList (Expr.inlineGlobalsList G es), Prim.ofName fk.1 = none
  | [], _, fk, hfk => absurd hfk (by simp [Expr.inlineGlobalsList, Expr.ctorsList])
  | e :: es, h, fk, hfk => by
      rw [Expr.inlineGlobalsList, Expr.ctorsList] at hfk
      rcases List.mem_append.mp hfk with hfk' | hfk'
      · exact ctors_inlineGlobals_noPrim hG e
          (fun gk hgk => h gk (by rw [Expr.ctorsList]; exact List.mem_append_left _ hgk)) fk hfk'
      · exact ctorsList_inlineGlobals_noPrim hG es
          (fun gk hgk => h gk (by rw [Expr.ctorsList]; exact List.mem_append_right _ hgk))
          fk hfk'

end

mutual

def Expr.substGlobals (G : List (Var × Expr)) : Expr → Expr
  | .lit l => .lit l
  | .var v => (Expr.lookupG v G).getD (.var v)
  | .app f args => .app f (Expr.substGlobalsList G args)

/-- `Expr.substGlobals` over an argument list. -/
def Expr.substGlobalsList (G : List (Var × Expr)) : List Expr → List Expr
  | [] => []
  | e :: es => Expr.substGlobals G e :: Expr.substGlobalsList G es

end

/-- `Expr.substGlobals` over a pattern. -/
def Pattern.substGlobals (G : List (Var × Expr)) : Pattern → Pattern
  | .expr e => .expr (e.substGlobals G)
  | .eq e₁ e₂ => .eq (e₁.substGlobals G) (e₂.substGlobals G)

/-- `Pattern.substGlobals` over a query. -/
def Query.substGlobals (G : List (Var × Expr)) (q : Query) : Query :=
  q.map (Pattern.substGlobals G)

/-- **The rule the encoder actually encodes**: the source rule with its *query* read through
the globals. The head is untouched — it reads the same environment the source head reads. -/
def Rule.substGlobals (G : List (Var × Expr)) (r : Rule) : Rule :=
  { r with query := Query.substGlobals G r.query }

@[simp] theorem Rule.substGlobals_actions (G : List (Var × Expr)) (r : Rule) :
    (r.substGlobals G).actions = r.actions := rfl

@[simp] theorem Rule.substGlobals_query (G : List (Var × Expr)) (r : Rule) :
    (r.substGlobals G).query = Query.substGlobals G r.query := rfl

@[simp] theorem Rule.substGlobals_ruleset (G : List (Var × Expr)) (r : Rule) :
    (r.substGlobals G).ruleset = r.ruleset := rfl

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

def Database.GlobalsCover (sd : Database) (G : List (Var × Expr)) : Prop :=
  ∀ v, (Env.lookup v sd.env).isSome → Expr.lookupG v G ≠ none

/-- Nothing is bound yet, so nothing has to be covered. -/
theorem Database.globalsCover_empty : Database.empty.GlobalsCover [] := by
  intro v hv; exact absurd hv (by simp [Database.empty])

/-! #### The encoder's substitution *is* the specification's resolution

`Spec/Step.lean` resolves the globals then in scope into a rule's query when the rule is
declared, writing each name's **value** back as syntax (`Term.toExpr`); the encoder writes the
name's **definition** (`Expr.substGlobals`). The two agree, and that identity is what pairs a
stored source rule with its own program text once resolution has moved to declaration time.

It needs both halves of the bookkeeping: `Database.GlobalsInline` to know a definition
evaluates to what the environment binds, and `Database.GlobalsCover` to know the environment
binds nothing the substitution missed. And it needs the definition to be **primitive-free**,
which is `Database.GlobalsInline`'s own clause and `Program.EncodeDomain.noPrim`'s consequence:
`(+ 1 2)` evaluates to `3`, and `Term.toExpr 3` is not `(+ 1 2)`. -/

mutual

/-- **A closed primitive-free expression is its own value, read back.** -/
theorem Term.toExpr_of_eval {sig : Signature} {σ : Env} :
    ∀ (e : Expr) {t : Term}, (∀ fk ∈ e.ctors, Prim.ofName fk.1 = none) →
      (∀ w, w ∉ e.vars) → e.eval sig σ = some t → t.toExpr = e
  | .lit l, t, _, _, h => by
      rw [Expr.eval, Option.some.injEq] at h; rw [← h]; rfl
  | .var v, _, _, hv, _ => absurd (show v ∈ (Expr.var v).vars by simp [Expr.vars]) (hv v)
  | .app f args, t, hc, hv, h => by
      have hp : Prim.ofName f = none :=
        hc (f, args.length) (by rw [Expr.ctors]; exact List.mem_cons_self ..)
      by_cases hctor : sig.IsCtor f
      · rw [Expr.eval_app_ctor hp hctor] at h
        obtain ⟨ts, hts, ht⟩ := Option.map_eq_some_iff.mp h
        rw [← ht, Term.toExpr_app,
          Term.toExprList_of_evalList args
            (fun fk hfk => hc fk (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hfk))
            (by rw [Expr.vars] at hv; exact hv) hts]
      · rw [Expr.eval, hp, if_neg hctor] at h; exact absurd h (by simp)

@[inherit_doc Term.toExpr_of_eval]
theorem Term.toExprList_of_evalList {sig : Signature} {σ : Env} :
    ∀ (es : List Expr) {ts : List Term},
      (∀ fk ∈ Expr.ctorsList es, Prim.ofName fk.1 = none) →
      (∀ w, w ∉ Expr.varsList es) → Expr.evalList sig es σ = some ts →
      Term.toExprList ts = es
  | [], ts, _, _, h => by rw [Expr.evalList, Option.some.injEq] at h; rw [← h]; rfl
  | e :: es, ts, hc, hv, h => by
      rw [Expr.evalList] at h
      obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, hts⟩ := Option.map_eq_some_iff.mp h
      rw [← hts, Term.toExprList_cons,
        Term.toExpr_of_eval e
          (fun fk hfk => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_left _ hfk))
          (fun w hw => hv w (by
            rw [Expr.varsList]; exact List.mem_union_iff.mpr (Or.inl hw))) ht,
        Term.toExprList_of_evalList es
          (fun fk hfk => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_right _ hfk))
          (fun w hw => hv w (by
            rw [Expr.varsList]; exact List.mem_union_iff.mpr (Or.inr hw))) hus]

end

/-- **A definition the substitution carries is the environment's value, read back.** -/
theorem Database.GlobalsInline.toExpr_eq {src : Database} {G : List (Var × Expr)}
    (h : src.GlobalsInline G) {v : Var} {e : Expr} (he : Expr.lookupG v G = some e) :
    ∃ t, Env.lookup v src.env = some t ∧ t.toExpr = e := by
  obtain ⟨hcl, hnp, t, hev, hlk⟩ := h v e he
  exact ⟨t, hlk, Term.toExpr_of_eval e hnp
    (fun w hw => absurd (hcl ▸ hw) (by simp)) hev⟩

mutual

/-- **The resolution and the substitution are the same rewriting**, variable by variable. -/
theorem Expr.resolveGlobals_eq_substGlobals {src : Database} {G : List (Var × Expr)}
    (hgi : src.GlobalsInline G) (hcov : src.GlobalsCover G) :
    ∀ e : Expr, Expr.resolveGlobals src.env e = Expr.substGlobals G e
  | .lit _ => rfl
  | .var v => by
      cases hlk : Expr.lookupG v G with
      | none =>
          have hnone : Env.lookup v src.env = none := by
            cases hE : Env.lookup v src.env with
            | none => rfl
            | some t => exact absurd hlk (hcov v (by rw [hE]; rfl))
          rw [Expr.resolveGlobals_var_none hnone, Expr.substGlobals, hlk, Option.getD_none]
      | some e =>
          obtain ⟨t, hlkt, hte⟩ := hgi.toExpr_eq hlk
          rw [Expr.resolveGlobals_var_some hlkt, Expr.substGlobals, hlk, Option.getD_some, hte]
  | .app f args => by
      rw [Expr.resolveGlobals_app, Expr.substGlobals,
        Expr.resolveGlobalsList_eq_substGlobalsList hgi hcov args]

@[inherit_doc Expr.resolveGlobals_eq_substGlobals]
theorem Expr.resolveGlobalsList_eq_substGlobalsList {src : Database} {G : List (Var × Expr)}
    (hgi : src.GlobalsInline G) (hcov : src.GlobalsCover G) :
    ∀ es : List Expr, Expr.resolveGlobalsList src.env es = Expr.substGlobalsList G es
  | [] => rfl
  | e :: es => by
      rw [Expr.resolveGlobalsList_cons, Expr.substGlobalsList,
        Expr.resolveGlobals_eq_substGlobals hgi hcov e,
        Expr.resolveGlobalsList_eq_substGlobalsList hgi hcov es]

end

@[inherit_doc Expr.resolveGlobals_eq_substGlobals]
theorem Pattern.resolveGlobals_eq_substGlobals {src : Database} {G : List (Var × Expr)}
    (hgi : src.GlobalsInline G) (hcov : src.GlobalsCover G) :
    ∀ p : Pattern, Pattern.resolveGlobals src.env p = Pattern.substGlobals G p
  | .expr e => by
      rw [Pattern.resolveGlobals, Pattern.substGlobals,
        Expr.resolveGlobals_eq_substGlobals hgi hcov e]
  | .eq e₁ e₂ => by
      rw [Pattern.resolveGlobals, Pattern.substGlobals,
        Expr.resolveGlobals_eq_substGlobals hgi hcov e₁,
        Expr.resolveGlobals_eq_substGlobals hgi hcov e₂]

@[inherit_doc Expr.resolveGlobals_eq_substGlobals]
theorem Query.resolveGlobals_eq_substGlobals {src : Database} {G : List (Var × Expr)}
    (hgi : src.GlobalsInline G) (hcov : src.GlobalsCover G) (q : Query) :
    Query.resolveGlobals src.env q = Query.substGlobals G q := by
  rw [Query.resolveGlobals, Query.substGlobals]
  exact List.map_congr_left fun p _ => Pattern.resolveGlobals_eq_substGlobals hgi hcov p

/-- **The rule the specification stores is the rule the encoder encodes.** -/
theorem Rule.resolveGlobals_eq_substGlobals {src : Database} {G : List (Var × Expr)}
    (hgi : src.GlobalsInline G) (hcov : src.GlobalsCover G) (r : Rule) :
    r.resolveGlobals src.env = r.substGlobals G := by
  rw [Rule.resolveGlobals, Rule.substGlobals, Query.resolveGlobals_eq_substGlobals hgi hcov]

/-- A substitution interpreted by an empty context cannot replace a query variable. -/
theorem Rule.substGlobals_eq_of_empty_env {src : Database} {G : List (Var × Expr)}
    (hgi : src.GlobalsInline G) (henv : src.env = []) (r : Rule) : r.substGlobals G = r := by
  have hc : src.GlobalsCover G := by
    intro v hv
    simp [henv, Env.lookup] at hv
  rw [← Rule.resolveGlobals_eq_substGlobals hgi hc, henv, Rule.resolveGlobals_nil]

/-! #### And resolving an already-resolved rule changes nothing

The other half of the pairing: the *encoded* program is run by the same `execCmdM`, so its
rules are stored `Rule.resolveGlobals`'d too. There is nothing left to resolve — the
substitution already removed every name the environment binds — so the target's stored rule is
the encoder's own output on the nose. -/

mutual

/-- A variable no environment binds is one the resolution leaves. -/
theorem Expr.resolveGlobals_eq_self {σ : Env} :
    ∀ (e : Expr), (∀ v ∈ e.vars, Env.lookup v σ = none) → Expr.resolveGlobals σ e = e
  | .lit _, _ => rfl
  | .var v, h => Expr.resolveGlobals_var_none (h v (by simp [Expr.vars]))
  | .app f args, h => by
      rw [Expr.resolveGlobals_app,
        Expr.resolveGlobalsList_eq_self args (by rw [Expr.vars] at h; exact h)]

@[inherit_doc Expr.resolveGlobals_eq_self]
theorem Expr.resolveGlobalsList_eq_self {σ : Env} :
    ∀ (es : List Expr), (∀ v ∈ Expr.varsList es, Env.lookup v σ = none) →
      Expr.resolveGlobalsList σ es = es
  | [], _ => rfl
  | e :: es, h => by
      rw [Expr.resolveGlobalsList_cons,
        Expr.resolveGlobals_eq_self e
          (fun v hv => h v (by rw [Expr.varsList]; exact List.mem_union_iff.mpr (Or.inl hv))),
        Expr.resolveGlobalsList_eq_self es
          (fun v hv => h v (by rw [Expr.varsList]; exact List.mem_union_iff.mpr (Or.inr hv)))]

end

@[inherit_doc Expr.resolveGlobals_eq_self]
theorem Pattern.resolveGlobals_eq_self {σ : Env} :
    ∀ (p : Pattern), (∀ v ∈ p.vars, Env.lookup v σ = none) →
      Pattern.resolveGlobals σ p = p
  | .expr e, h => by rw [Pattern.resolveGlobals, Expr.resolveGlobals_eq_self e h]
  | .eq e₁ e₂, h => by
      rw [Pattern.resolveGlobals,
        Expr.resolveGlobals_eq_self e₁
          (fun v hv => h v (by rw [Pattern.vars]; exact List.mem_union_iff.mpr (Or.inl hv))),
        Expr.resolveGlobals_eq_self e₂
          (fun v hv => h v (by rw [Pattern.vars]; exact List.mem_union_iff.mpr (Or.inr hv)))]

@[inherit_doc Expr.resolveGlobals_eq_self]
theorem Query.resolveGlobals_eq_self {σ : Env} (q : Query)
    (h : ∀ v ∈ Query.vars q, Env.lookup v σ = none) : Query.resolveGlobals σ q = q := by
  rw [Query.resolveGlobals]
  conv_rhs => rw [← List.map_id q]
  exact List.map_congr_left fun p hp =>
    Pattern.resolveGlobals_eq_self p fun v hv => h v (Query.mem_vars.mpr ⟨p, hp, hv⟩)

@[inherit_doc Expr.resolveGlobals_eq_self]
theorem Rule.resolveGlobals_eq_self {σ : Env} (r : Rule)
    (h : ∀ v ∈ Query.vars r.query, Env.lookup v σ = none) : r.resolveGlobals σ = r := by
  rw [Rule.resolveGlobals, Query.resolveGlobals_eq_self _ h]

/-! ### Queries

A source pattern becomes one view read per subterm, joined on e-class variables — the
`check` expansion of `proof_encoding.md`, "Queries". The reads bind ids, so the outer
`(= e₁ e₂)` of a source equality pattern becomes id equality, which is egglog's own
`(= e3 e6)` and is why the rebuild has to have canonicalized the entries first. -/
/-- The rulesets a source `Cmd.saturate` names. -/
def Program.saturateRulesets (P : Program) : List RulesetName :=
  (P.filterMap fun c => match c with | .saturate R => some R | _ => none).dedup

/-- The source rules, in the order `encodeCmds` numbers them. -/
def Program.srcRules (P : Program) : List Rule :=
  P.filterMap fun c => match c with | .rule r => some r | _ => none

/-! ### The source programs `encode` is defined for

`Program.EncodeDomain` below specifies the constructor fragment and the naming, query,
arity, and head-legality conditions used by the correspondence theorem. -/
/-- Compatibility marker for proofs over the former action syntax. Every current action
satisfies it; the source fragment is constrained by constructor declarations and evaluability. -/
def Action.NoSet : Action → Prop
  | _ => True

/-- Compatibility marker for the former separate entry-pattern constructor. Complete
atoms share the expression case, so this imposes no restriction on current patterns. -/
def Pattern.NoValues : Pattern → Prop
  | _ => True

/-- `Action.NoSet` at every action a command runs. -/
def Cmd.NoSet : Cmd → Prop
  | .action a => a.NoSet
  | .rule r => ∀ a ∈ r.actions, a.NoSet
  | _ => True

/-- The signature a constructor declaration installs declares constructors only. -/
theorem Signature.allConstructors_sigBind {sig : Signature} (hsig : sig.AllConstructors)
    {c : Cmd} (hc : c.CtorDecl) : (c.sigBind sig).AllConstructors := by
  cases c with
  | decl f d =>
      intro g
      by_cases h : g = f
      · subst h
        rw [Cmd.sigBind, Signature.mergeOf, Function.update_self]
        exact hc
      · rw [Cmd.sigBind, Signature.mergeOf, Function.update_of_ne h]
        exact hsig g
  | _ => exact hsig

/-- The two automatic structural predicates agree. -/
theorem Cmd.setLegal_iff_noSet {sig : Signature} (hsig : sig.AllConstructors) (c : Cmd) :
    c.SetLegal sig ↔ c.NoSet := by
  have hact : ∀ a : Action, a.SetLegal sig ↔ a.NoSet := by
    intro a
    cases a <;> simp [Action.SetLegal, Action.NoSet, hsig _]
  have hacts : ∀ as : List Action, Actions.SetLegal as sig ↔ ∀ a ∈ as, a.NoSet := by
    intro as
    induction as with
    | nil => simp
    | cons a as ih => simp [hact a, ih]
  cases c <;> simp [Cmd.NoSet, hact, hacts]

/-- The compatibility equivalence over a program. Both structural checks are automatic. -/
theorem Program.setLegal_iff_noSet : ∀ {P : Program} {sig : Signature}, sig.AllConstructors →
    P.CtorDecls → (Program.SetLegal P sig ↔ ∀ c ∈ P, c.NoSet)
  | [], _, _, _ => by simp
  | c :: cs, sig, hsig, hctor => by
      have hc : c.CtorDecl := hctor c (List.mem_cons_self ..)
      have htail : Program.CtorDecls cs := fun c' hc' => hctor c' (List.mem_cons_of_mem _ hc')
      rw [Program.SetLegal, Cmd.setLegal_iff_noSet hsig c,
        Program.setLegal_iff_noSet (Signature.allConstructors_sigBind hsig hc) htail]
      simp

/-- The variables a pattern mentions. -/
def Pattern.varsOf : Pattern → List Var := Pattern.vars

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

theorem Expr.substGlobalsList_eq_map (G : List (Var × Expr)) :
    ∀ es : List Expr, Expr.substGlobalsList G es = es.map (Expr.substGlobals G)
  | [] => rfl
  | e :: es => by rw [Expr.substGlobalsList, List.map_cons, Expr.substGlobalsList_eq_map G es]

/-- **A literal the substitution produced is one the source holds.** The only way
`Expr.substGlobals` makes a bare literal out of a non-literal is by writing a global's own
definition in, and `Database.GlobalsInline` says the environment binds the name to its
value — which `Database.WF` puts in `terms`. -/
theorem Expr.mem_terms_of_substGlobals_lit {src : Database} {G : List (Var × Expr)}
    (hw : src.WF) (hG : src.GlobalsInline G) {e : Expr} (h : ∀ l, e ≠ .lit l) :
    ∀ l, e.substGlobals G = .lit l → Term.lit l ∈ src.terms := by
  cases e with
  | lit l => exact absurd rfl (h l)
  | var v =>
      intro l hl
      rw [Expr.substGlobals] at hl
      cases hlk : Expr.lookupG v G with
      | none => rw [hlk] at hl; exact absurd hl (by simp)
      | some e' =>
          rw [hlk] at hl
          rw [Option.getD_some] at hl
          subst hl
          obtain ⟨-, -, t, hev, hbind⟩ := hG v _ hlk
          rw [Expr.eval_lit, Option.some.injEq] at hev
          subst hev
          exact hw.envInTerms _ (Env.mem_of_lookup hbind)
  | app f args => intro l hl; rw [Expr.substGlobals] at hl; exact absurd hl (by simp)

@[inherit_doc Expr.mem_terms_of_substGlobals_lit]
theorem Database.GlobalsInline.groundedAt_substGlobals {src : Database} {G : List (Var × Expr)}
    (hw : src.WF) (hG : src.GlobalsInline G) :
    ∀ {p : Pattern}, p.Grounded → (p.substGlobals G).GroundedAt src
  | .expr _, h => Expr.mem_terms_of_substGlobals_lit hw hG h
  | .eq _ _, h => h.imp (Expr.mem_terms_of_substGlobals_lit hw hG)
      (Expr.mem_terms_of_substGlobals_lit hw hG)

/-- The substitution moves nothing between the three pattern shapes. -/
theorem Pattern.NoValues.substGlobals {G : List (Var × Expr)} :
    ∀ {p : Pattern}, p.NoValues → (p.substGlobals G).NoValues
  | .expr _, _ => trivial
  | .eq _ _, _ => trivial

mutual

/-- **A variable the substitution leaves is one it does not replace**, and one the original
expression already mentioned. The definitions are closed, so a replaced variable's occurrences
vanish entirely rather than moving. -/
theorem Expr.mem_vars_substGlobals {G : List (Var × Expr)} (hcl : Expr.ClosedG G) :
    ∀ (e : Expr) {v : Var}, v ∈ (e.substGlobals G).vars →
      v ∈ e.vars ∧ Expr.substGlobals G (.var v) = .var v
  | .lit _, _, h => absurd h (by simp [Expr.substGlobals])
  | .var w, v, h => by
      rw [Expr.substGlobals] at h
      cases hlk : Expr.lookupG w G with
      | none =>
          rw [hlk, Option.getD_none] at h
          obtain rfl : v = w := by simpa [Expr.vars] using h
          exact ⟨by simp [Expr.vars], by rw [Expr.substGlobals, hlk, Option.getD_none]⟩
      | some e =>
          rw [hlk, Option.getD_some] at h
          exact absurd h (by rw [hcl w _ hlk]; simp)
  | .app f args, v, h => by
      rw [Expr.substGlobals, Expr.vars] at h
      obtain ⟨hv, hs⟩ := Expr.mem_varsList_substGlobals hcl args h
      exact ⟨by rw [Expr.vars]; exact hv, hs⟩

@[inherit_doc Expr.mem_vars_substGlobals]
theorem Expr.mem_varsList_substGlobals {G : List (Var × Expr)} (hcl : Expr.ClosedG G) :
    ∀ (es : List Expr) {v : Var}, v ∈ Expr.varsList (Expr.substGlobalsList G es) →
      v ∈ Expr.varsList es ∧ Expr.substGlobals G (.var v) = .var v
  | [], _, h => absurd h (by simp [Expr.substGlobalsList])
  | e :: es, v, h => by
      rw [Expr.substGlobalsList, Expr.varsList, List.mem_union_iff] at h
      rcases h with h | h
      · obtain ⟨hv, hs⟩ := Expr.mem_vars_substGlobals hcl e h
        exact ⟨by rw [Expr.varsList]; exact List.mem_union_iff.mpr (Or.inl hv), hs⟩
      · obtain ⟨hv, hs⟩ := Expr.mem_varsList_substGlobals hcl es h
        exact ⟨by rw [Expr.varsList]; exact List.mem_union_iff.mpr (Or.inr hv), hs⟩

end

mutual

/-- **A variable the substitution does not replace survives it.** -/
theorem Expr.mem_vars_substGlobals_of_keep {G : List (Var × Expr)} (hcl : Expr.ClosedG G)
    {v : Var} (hkeep : Expr.substGlobals G (.var v) = .var v) :
    ∀ (e : Expr), v ∈ e.vars → v ∈ (e.substGlobals G).vars
  | .lit _, h => absurd h (by simp [Expr.vars])
  | .var w, h => by
      obtain rfl : v = w := by simpa [Expr.vars] using h
      rw [hkeep]
      simp [Expr.vars]
  | .app f args, h => by
      rw [Expr.vars] at h
      rw [Expr.substGlobals, Expr.vars]
      exact Expr.mem_varsList_substGlobals_of_keep hcl hkeep args h

@[inherit_doc Expr.mem_vars_substGlobals_of_keep]
theorem Expr.mem_varsList_substGlobals_of_keep {G : List (Var × Expr)} (hcl : Expr.ClosedG G)
    {v : Var} (hkeep : Expr.substGlobals G (.var v) = .var v) :
    ∀ (es : List Expr), v ∈ Expr.varsList es →
      v ∈ Expr.varsList (Expr.substGlobalsList G es)
  | [], h => absurd h (by simp [Expr.varsList])
  | e :: es, h => by
      rw [Expr.varsList, List.mem_union_iff] at h
      rw [Expr.substGlobalsList, Expr.varsList, List.mem_union_iff]
      exact h.imp (Expr.mem_vars_substGlobals_of_keep hcl hkeep e)
        (Expr.mem_varsList_substGlobals_of_keep hcl hkeep es)

end

mutual

/-- **A key position survives the substitution**, for a variable the substitution leaves. -/
theorem Expr.ArgVar.substGlobals {G : List (Var × Expr)} {v : Var}
    (hv : Expr.substGlobals G (.var v) = .var v) :
    ∀ {e : Expr}, Expr.ArgVar v e → Expr.ArgVar v (e.substGlobals G)
  | .app f args, h => by
      rw [Expr.substGlobals, Expr.ArgVar]
      rcases h with h | h
      · refine Or.inl ?_
        rw [Expr.substGlobalsList_eq_map]
        exact hv ▸ List.mem_map_of_mem h
      · exact Or.inr (Expr.ArgVarList.substGlobals hv h)

@[inherit_doc Expr.ArgVar.substGlobals]
theorem Expr.ArgVarList.substGlobals {G : List (Var × Expr)} {v : Var}
    (hv : Expr.substGlobals G (.var v) = .var v) :
    ∀ {es : List Expr}, Expr.ArgVarList v es → Expr.ArgVarList v (Expr.substGlobalsList G es)
  | e :: es, h => by
      rw [Expr.substGlobalsList, Expr.ArgVarList]
      exact h.imp (Expr.ArgVar.substGlobals hv) (Expr.ArgVarList.substGlobals hv)

end

@[inherit_doc Expr.ArgVar.substGlobals]
theorem Pattern.ArgVar.substGlobals {G : List (Var × Expr)} {v : Var}
    (hv : Expr.substGlobals G (.var v) = .var v) :
    ∀ {p : Pattern}, Pattern.ArgVar v p → Pattern.ArgVar v (p.substGlobals G)
  | .expr _, h => Expr.ArgVar.substGlobals hv h
  | .eq _ _, h => h.imp (Expr.ArgVar.substGlobals hv) (Expr.ArgVar.substGlobals hv)

/-- `Pattern.NoValues.substGlobals` over a query. -/
theorem Query.noValues_substGlobals {G : List (Var × Expr)} {q : Query}
    (h : ∀ p ∈ q, p.NoValues) : ∀ p ∈ Query.substGlobals G q, p.NoValues := by
  intro p hp
  rw [Query.substGlobals, List.mem_map] at hp
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  exact (h p₀ hp₀).substGlobals

/-- `Database.GlobalsInline.groundedAt_substGlobals` over a query. -/
theorem Query.groundedAt_substGlobals {src : Database} {G : List (Var × Expr)}
    (hw : src.WF) (hG : src.GlobalsInline G) {q : Query}
    (h : ∀ p ∈ q, p.Grounded) : ∀ p ∈ Query.substGlobals G q, p.GroundedAt src := by
  intro p hp
  rw [Query.substGlobals, List.mem_map] at hp
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  exact hG.groundedAt_substGlobals hw (h p₀ hp₀)

/-- **A query variable the substitution removed is one it carries a definition for.** The
counterpart of `Query.VarsKeyed.substGlobals`, and what says a rule head reading such a
variable reads a global. -/
theorem Query.lookupG_ne_none_of_not_mem_vars_substGlobals {G : List (Var × Expr)}
    (hcl : Expr.ClosedG G) {q : Query} {v : Var} (hv : v ∈ Query.vars q)
    (hnv : v ∉ Query.vars (Query.substGlobals G q)) : Expr.lookupG v G ≠ none := by
  intro hnone
  refine hnv (Query.mem_vars.mpr ?_)
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp hv
  refine ⟨p.substGlobals G, List.mem_map_of_mem hp, ?_⟩
  have hkeep : Expr.substGlobals G (Expr.var v) = .var v := by
    rw [Expr.substGlobals, hnone, Option.getD_none]
  clear hv hnv hp
  cases p with
  | expr e => exact Expr.mem_vars_substGlobals_of_keep hcl hkeep e hvp
  | eq e₁ e₂ =>
      rcases List.mem_union_iff.mp hvp with h | h
      · exact List.mem_union_iff.mpr (Or.inl (Expr.mem_vars_substGlobals_of_keep hcl hkeep e₁ h))
      · exact List.mem_union_iff.mpr (Or.inr (Expr.mem_vars_substGlobals_of_keep hcl hkeep e₂ h))

/-- **Every variable of the substituted query still sits at a key column.** -/
theorem Query.VarsKeyed.substGlobals {G : List (Var × Expr)} (hcl : Expr.ClosedG G) {q : Query}
    (h : Query.VarsKeyed q) : Query.VarsKeyed (Query.substGlobals G q) := by
  intro v hv
  obtain ⟨p', hp', hvp⟩ := Query.mem_vars.mp hv
  rw [Query.substGlobals, List.mem_map] at hp'
  obtain ⟨p, hp, rfl⟩ := hp'
  have hkeep : v ∈ p.vars ∧ Expr.substGlobals G (Expr.var v) = .var v := by
    cases p with
    | expr e => exact Expr.mem_vars_substGlobals hcl e hvp
    | eq e₁ e₂ =>
        rcases List.mem_union_iff.mp hvp with h' | h'
        · obtain ⟨hv', hs⟩ := Expr.mem_vars_substGlobals hcl e₁ h'
          exact ⟨List.mem_union_iff.mpr (Or.inl hv'), hs⟩
        · obtain ⟨hv', hs⟩ := Expr.mem_vars_substGlobals hcl e₂ h'
          exact ⟨List.mem_union_iff.mpr (Or.inr hv'), hs⟩
  obtain ⟨p₀, hp₀, ha⟩ := h v (Query.mem_vars.mpr ⟨p, hp, hkeep.1⟩)
  exact ⟨p₀.substGlobals G, List.mem_map_of_mem hp₀, Pattern.ArgVar.substGlobals hkeep.2 ha⟩

/-! #### The target's stored rule is the encoder's output

`FDatabase.execCmdM` resolves the globals then in scope into a rule it registers, exactly as
`Spec/Step.lean`'s `cmdEffect` does. At an **encoded** rule there is nothing left to resolve:
every variable it mentions is either generated — `@`-prefixed, and `FDatabase.NoAtEnv` keeps
those out of the environment — or one `Expr.substGlobals` declined to replace, and
`Database.GlobalsCover` says the environment does not bind one of those either. -/

/-- A closed expression has nothing to substitute. -/
theorem Expr.substGlobals_eq_self_of_closed {G : List (Var × Expr)} :
    ∀ {e : Expr}, (∀ v, v ∉ e.vars) → e.substGlobals G = e
  | .lit _, _ => rfl
  | .var v, h => absurd (show v ∈ (Expr.var v).vars by simp [Expr.vars]) (h v)
  | .app f args, h => by
      rw [Expr.substGlobals, Expr.substGlobalsList_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id args]
      refine List.map_congr_left fun e he => Expr.substGlobals_eq_self_of_closed
        fun v hv => h v ?_
      rw [Expr.vars]
      clear h
      induction args with
      | nil => exact absurd he (by simp)
      | cons a as ih =>
          rw [Expr.varsList, List.mem_union_iff]
          rcases List.mem_cons.mp he with rfl | he'
          · exact Or.inl hv
          · exact Or.inr (ih he')

/-- **A variable the substitution leaves is one it carries no definition for.** -/
theorem Expr.lookupG_eq_none_of_mem_vars_substGlobals {G : List (Var × Expr)}
    (hcl : Expr.ClosedG G) {v : Var} {e : Expr} (h : v ∈ (e.substGlobals G).vars) :
    Expr.lookupG v G = none := by
  have hk := (Expr.mem_vars_substGlobals hcl e h).2
  rw [Expr.substGlobals] at hk
  cases hE : Expr.lookupG v G with
  | none => rfl
  | some e' =>
      rw [hE, Option.getD_some] at hk
      subst hk
      exact absurd (hcl v _ hE) (by simp [Expr.vars])

@[inherit_doc Expr.lookupG_eq_none_of_mem_vars_substGlobals]
theorem Query.lookupG_eq_none_of_mem_vars_substGlobals {G : List (Var × Expr)}
    (hcl : Expr.ClosedG G) {q : Query} {v : Var}
    (h : v ∈ Query.vars (Query.substGlobals G q)) : Expr.lookupG v G = none := by
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp h
  rw [Query.substGlobals, List.mem_map] at hp
  obtain ⟨p₀, -, rfl⟩ := hp
  cases p₀ with
  | expr e => exact Expr.lookupG_eq_none_of_mem_vars_substGlobals hcl hvp
  | eq e₁ e₂ =>
      rcases List.mem_union_iff.mp hvp with h' | h'
      · exact Expr.lookupG_eq_none_of_mem_vars_substGlobals hcl h'
      · exact Expr.lookupG_eq_none_of_mem_vars_substGlobals hcl h'

/-- **Substituting twice is substituting once**: the definitions are closed, so nothing a
first pass wrote can be rewritten by a second. -/
theorem Query.substGlobals_idem {G : List (Var × Expr)} (hcl : Expr.ClosedG G) (q : Query) :
    Query.substGlobals G (Query.substGlobals G q) = Query.substGlobals G q := by
  have hE : ∀ e : Expr, (e.substGlobals G).substGlobals G = e.substGlobals G := by
    intro e
    induction e using Expr.rec
      (motive_2 := fun es => Expr.substGlobalsList G (Expr.substGlobalsList G es)
        = Expr.substGlobalsList G es) with
    | lit l => rfl
    | var v =>
        cases hE : Expr.lookupG v G with
        | none =>
            rw [Expr.substGlobals, hE, Option.getD_none, Expr.substGlobals, hE,
              Option.getD_none]
        | some e' =>
            rw [Expr.substGlobals, hE, Option.getD_some]
            exact Expr.substGlobals_eq_self_of_closed
              fun w hw => absurd (hcl v _ hE ▸ hw) (by simp)
    | app f args ih => rw [Expr.substGlobals, Expr.substGlobals, ih]
    | nil => rfl
    | cons e es ihe ihes =>
        rw [Expr.substGlobalsList, Expr.substGlobalsList, ihe, ihes]
  have hL : ∀ es : List Expr, Expr.substGlobalsList G (Expr.substGlobalsList G es)
      = Expr.substGlobalsList G es := by
    intro es; induction es with
    | nil => rfl
    | cons e es ih => rw [Expr.substGlobalsList, Expr.substGlobalsList, hE, ih]
  simp only [Query.substGlobals, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  cases p with
  | expr e => rw [Function.comp_apply, Pattern.substGlobals, Pattern.substGlobals, hE]
  | eq e₁ e₂ => rw [Function.comp_apply, Pattern.substGlobals, Pattern.substGlobals, hE, hE]

@[inherit_doc Query.substGlobals_idem]
theorem Rule.substGlobals_idem {G : List (Var × Expr)} (hcl : Expr.ClosedG G) (r : Rule) :
    (r.substGlobals G).substGlobals G = r.substGlobals G := by
  simp only [Rule.substGlobals, Query.substGlobals_idem hcl]

mutual

/-- **A term read back as syntax applies only the term's own heads**, none of which is a
primitive at a state whose terms build (`Database.TermsBuild`). -/
theorem Term.ctors_toExpr_noPrim {db : Database} (hwf : db.WF)
    (htb : ∀ f as, Term.app f as ∈ db.terms → Prim.ofName f = none) :
    ∀ (t : Term), t ∈ db.terms → ∀ fk ∈ t.toExpr.ctors, Prim.ofName fk.1 = none
  | .lit _, _, _, hfk => absurd hfk (by simp [Term.toExpr, Expr.ctors])
  | .app f ts, hm, fk, hfk => by
      rw [Term.toExpr_app, Expr.ctors, List.mem_cons] at hfk
      rcases hfk with rfl | hfk
      · exact htb f ts hm
      · exact Term.ctorsList_toExprList_noPrim hwf htb ts
          (fun u hu => hwf.subtermClosed _ hm (Term.arg_subterms hu (u.self_mem_subterms)))
          fk hfk

@[inherit_doc Term.ctors_toExpr_noPrim]
theorem Term.ctorsList_toExprList_noPrim {db : Database} (hwf : db.WF)
    (htb : ∀ f as, Term.app f as ∈ db.terms → Prim.ofName f = none) :
    ∀ (ts : List Term), (∀ u ∈ ts, u ∈ db.terms) →
      ∀ fk ∈ Expr.ctorsList (Term.toExprList ts), Prim.ofName fk.1 = none
  | [], _, _, hfk => absurd hfk (by simp [Term.toExprList, Expr.ctorsList])
  | t :: ts, hm, fk, hfk => by
      rw [Term.toExprList_cons, Expr.ctorsList] at hfk
      rcases List.mem_append.mp hfk with hfk' | hfk'
      · exact Term.ctors_toExpr_noPrim hwf htb t (hm t List.mem_cons_self) fk hfk'
      · exact Term.ctorsList_toExprList_noPrim hwf htb ts
          (fun u hu => hm u (List.mem_cons_of_mem _ hu)) fk hfk'

end

mutual

theorem Expr.substGlobals_eq_inlineGlobals (G : List (Var × Expr)) :
    ∀ e : Expr, Expr.substGlobals G e = Expr.inlineGlobals G e
  | .lit _ => rfl
  | .var _ => rfl
  | .app f args => by
      rw [Expr.substGlobals, Expr.inlineGlobals,
        Expr.substGlobalsList_eq_inlineGlobalsList G args]

@[inherit_doc Expr.substGlobals_eq_inlineGlobals]
theorem Expr.substGlobalsList_eq_inlineGlobalsList (G : List (Var × Expr)) :
    ∀ es : List Expr, Expr.substGlobalsList G es = Expr.inlineGlobalsList G es
  | [] => rfl
  | e :: es => by
      rw [Expr.substGlobalsList, Expr.inlineGlobalsList,
        Expr.substGlobals_eq_inlineGlobals G e,
        Expr.substGlobalsList_eq_inlineGlobalsList G es]

end

/-- `ctors_inlineGlobals_noPrim` at a pattern's substitution. -/
theorem Pattern.ctors_substGlobals_noPrim {G : List (Var × Expr)}
    (hG : ∀ (u : Var) (e' : Expr), Expr.lookupG u G = some e' →
      ∀ fk ∈ e'.ctors, Prim.ofName fk.1 = none) :
    ∀ (p : Pattern), (∀ fk ∈ p.ctors, Prim.ofName fk.1 = none) →
      ∀ fk ∈ (p.substGlobals G).ctors, Prim.ofName fk.1 = none := by
  have hL : ∀ (es : List Expr), (∀ fk ∈ Expr.ctorsList es, Prim.ofName fk.1 = none) →
      ∀ fk ∈ Expr.ctorsList (Expr.substGlobalsList G es), Prim.ofName fk.1 = none := by
    intro es h
    rw [Expr.substGlobalsList_eq_inlineGlobalsList]
    exact ctorsList_inlineGlobals_noPrim hG es h
  intro p h fk hfk
  cases p with
  | expr e =>
      rw [Pattern.substGlobals, Pattern.ctors, Expr.substGlobals_eq_inlineGlobals] at hfk
      exact ctors_inlineGlobals_noPrim hG e (by rw [Pattern.ctors] at h; exact h) fk hfk
  | eq e₁ e₂ =>
      rw [Pattern.substGlobals, Pattern.ctors] at hfk
      rw [Pattern.ctors] at h
      rcases List.mem_append.mp hfk with hfk' | hfk'
      · rw [Expr.substGlobals_eq_inlineGlobals] at hfk'
        exact ctors_inlineGlobals_noPrim hG e₁
          (fun gk hgk => h gk (List.mem_append_left _ hgk)) fk hfk'
      · rw [Expr.substGlobals_eq_inlineGlobals] at hfk'
        exact ctors_inlineGlobals_noPrim hG e₂
          (fun gk hgk => h gk (List.mem_append_right _ hgk)) fk hfk'

/-! #### The resolution is the substitution at the environment's own definitions

`Spec/Step.lean`'s `Rule.resolveGlobals` writes each global's **value** back as syntax; that is
`Expr.substGlobals` at the substitution the environment induces, so everything proved of the
substitution above transfers to it. -/

mutual

/-- A term read back as syntax mentions no variable. -/
theorem Term.vars_toExpr : ∀ t : Term, t.toExpr.vars = []
  | .lit _ => rfl
  | .app f ts => by rw [Term.toExpr_app, Expr.vars, Term.varsList_toExprList ts]

@[inherit_doc Term.vars_toExpr]
theorem Term.varsList_toExprList : ∀ ts : List Term, Expr.varsList (Term.toExprList ts) = []
  | [] => rfl
  | t :: ts => by
      rw [Term.toExprList_cons, Expr.varsList, Term.vars_toExpr, Term.varsList_toExprList ts]
      rfl

end

/-- **The substitution an environment induces**: each name bound to the expression that
rebuilds its value. -/
def Env.toG (σ : Env) : List (Var × Expr) := σ.map fun b => (b.1, b.2.toExpr)

@[inherit_doc Env.toG]
theorem Expr.lookupG_toG : ∀ (σ : Env) (v : Var),
    Expr.lookupG v (Env.toG σ) = (Env.lookup v σ).map Term.toExpr
  | [], _ => rfl
  | b :: σ, v => by
      rw [Env.toG, List.map_cons, Expr.lookupG, Env.lookup]
      by_cases h : v = b.1
      · rw [if_pos h, if_pos h, Option.map_some]
      · rw [if_neg h, if_neg h]
        exact Expr.lookupG_toG σ v

@[inherit_doc Env.toG]
theorem Expr.closedG_toG (σ : Env) : Expr.ClosedG (Env.toG σ) := by
  intro v e he
  rw [Expr.lookupG_toG] at he
  obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp he
  exact Term.vars_toExpr t

mutual

@[inherit_doc Env.toG]
theorem Expr.resolveGlobals_eq_substGlobals_toG (σ : Env) :
    ∀ e : Expr, Expr.resolveGlobals σ e = Expr.substGlobals (Env.toG σ) e
  | .lit _ => rfl
  | .var v => by
      rw [Expr.resolveGlobals_var, Expr.substGlobals, Expr.lookupG_toG]
      cases Env.lookup v σ with
      | none => rfl
      | some t => rfl
  | .app f args => by
      rw [Expr.resolveGlobals_app, Expr.substGlobals,
        Expr.resolveGlobalsList_eq_substGlobalsList_toG σ args]

@[inherit_doc Env.toG]
theorem Expr.resolveGlobalsList_eq_substGlobalsList_toG (σ : Env) :
    ∀ es : List Expr, Expr.resolveGlobalsList σ es = Expr.substGlobalsList (Env.toG σ) es
  | [] => rfl
  | e :: es => by
      rw [Expr.resolveGlobalsList_cons, Expr.substGlobalsList,
        Expr.resolveGlobals_eq_substGlobals_toG σ e,
        Expr.resolveGlobalsList_eq_substGlobalsList_toG σ es]

end

@[inherit_doc Env.toG]
theorem Pattern.resolveGlobals_eq_substGlobals_toG (σ : Env) :
    ∀ p : Pattern, Pattern.resolveGlobals σ p = Pattern.substGlobals (Env.toG σ) p
  | .expr e => by
      rw [Pattern.resolveGlobals, Pattern.substGlobals,
        Expr.resolveGlobals_eq_substGlobals_toG]
  | .eq e₁ e₂ => by
      rw [Pattern.resolveGlobals, Pattern.substGlobals,
        Expr.resolveGlobals_eq_substGlobals_toG, Expr.resolveGlobals_eq_substGlobals_toG]

@[inherit_doc Env.toG]
theorem Query.resolveGlobals_eq_substGlobals_toG (σ : Env) (q : Query) :
    Query.resolveGlobals σ q = Query.substGlobals (Env.toG σ) q := by
  rw [Query.resolveGlobals, Query.substGlobals]
  exact List.map_congr_left fun p _ => Pattern.resolveGlobals_eq_substGlobals_toG σ p

/-- `Pattern.NoValues.substGlobals` at the resolution. -/
theorem Query.noValues_resolveGlobals {σ : Env} {q : Query}
    (h : ∀ p ∈ q, p.NoValues) : ∀ p ∈ Query.resolveGlobals σ q, p.NoValues := by
  rw [Query.resolveGlobals_eq_substGlobals_toG]
  exact Query.noValues_substGlobals h

/-- `Query.VarsKeyed.substGlobals` at the resolution. -/
theorem Query.VarsKeyed.resolveGlobals {σ : Env} {q : Query}
    (h : Query.VarsKeyed q) : Query.VarsKeyed (Query.resolveGlobals σ q) := by
  rw [Query.resolveGlobals_eq_substGlobals_toG]
  exact Query.VarsKeyed.substGlobals (Expr.closedG_toG σ) h

/-- **The resolution introduces no primitive**: it writes back terms the state holds, whose
heads build (`Database.TermsBuild`). -/
theorem Query.ctors_resolveGlobals_noPrim {db : Database} (hwf : db.WF)
    (htb : ∀ f as, Term.app f as ∈ db.terms → Prim.ofName f = none) {q : Query}
    (h : ∀ p ∈ q, ∀ fk ∈ p.ctors, Prim.ofName fk.1 = none) :
    ∀ p ∈ Query.resolveGlobals db.env q, ∀ fk ∈ p.ctors, Prim.ofName fk.1 = none := by
  intro p hp
  rw [Query.resolveGlobals_eq_substGlobals_toG, Query.substGlobals, List.mem_map] at hp
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  refine Pattern.ctors_substGlobals_noPrim (fun u e' he' => ?_) p₀ (h p₀ hp₀)
  rw [Expr.lookupG_toG] at he'
  obtain ⟨t, hlk, rfl⟩ := Option.map_eq_some_iff.mp he'
  exact Term.ctors_toExpr_noPrim hwf htb t (hwf.envInTerms (u, t) (Env.mem_of_lookup hlk))

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

/-! #### The `union` legality the clause implies

`Spec/Scope.lean`'s `Action.UnionLegal` at a rule head, from either disjunct of
`noLitUnion`: with no `union` in a head there is nothing to check, and with no literal in the
program an operand is not one. -/

/-- An action that asserts no equation asserts none on a literal. -/
theorem Action.UnionLegal.of_unionFree {a : Action} (h : a.UnionFree) : a.UnionLegal := by
  cases a <;> first | trivial | exact absurd h id

/-- An action that evaluates no literal hands none to a `union`. -/
theorem Action.UnionLegal.of_litFreeB {a : Action} (h : a.litFreeB = true) : a.UnionLegal := by
  cases a with
  | union e₁ e₂ =>
      simp only [Action.litFreeB, Bool.and_eq_true] at h
      refine ⟨fun l hl => ?_, fun l hl => ?_⟩
      · rw [hl] at h; simp [Expr.litFreeB] at h
      · rw [hl] at h; simp [Expr.litFreeB] at h
  | expr _ => trivial

@[inherit_doc Action.UnionLegal.of_unionFree]
theorem Actions.UnionLegal.of_mem : ∀ {as : List Action}, (∀ a ∈ as, a.UnionLegal) →
    Actions.UnionLegal as
  | [], _ => trivial
  | _ :: as, hall =>
      ⟨hall _ (List.mem_cons_self ..),
        Actions.UnionLegal.of_mem fun b hb => hall b (List.mem_cons_of_mem _ hb)⟩

/-- **The domain's `noLitUnion` implies `union` legality at every rule head.** Not the
converse: `Action.UnionLegal` reads the operand expressions, and a *variable* operand bound to
a literal is what the clause's second disjunct is for. -/
theorem Program.EncodeDomain.unionLegal_of_mem {P : Program} (h : P.EncodeDomain) {r : Rule}
    (hr : Cmd.rule r ∈ P) : Actions.UnionLegal r.actions := by
  rcases h.noLitUnion with hfree | hlit
  · refine Actions.UnionLegal.of_mem fun a ha => Action.UnionLegal.of_unionFree ?_
    have hb := hfree _ hr
    simp only [Cmd.ruleUnionFreeB, List.all_eq_true] at hb
    exact (Action.unionFreeB_iff a).mp (hb a ha)
  · refine Actions.UnionLegal.of_mem fun a ha => Action.UnionLegal.of_litFreeB ?_
    have hb := hlit _ hr
    simp only [Cmd.litFreeB, List.all_eq_true] at hb
    exact hb a ha

/-- **Every application the source holds is a declared constructor's, applied.** -/
def Database.TermsBuild (src : Database) : Prop :=
  ∀ f as, Term.app f as ∈ src.terms → Prim.ofName f = none ∧ src.sig.IsCtor f

end Egglog
