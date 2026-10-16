import EgglogSemantics.Proofs.Source.Execution

/-! Constructor names and arities across constructor-source executions. -/

namespace Egglog

/-- Every application inside `t` is one `P` applies at that arity. -/
def Term.CtorsIn (P : Program) (t : Term) : Prop :=
  ∀ g bs, Term.app g bs ∈ t.subterms → (g, bs.length) ∈ P.ctors

@[simp] theorem Term.ctorsIn_lit {P : Program} {l : Lit} : Term.CtorsIn P (.lit l) := by
  intro g bs hs
  exact absurd (Term.subterms_lit ▸ hs) (by simp)

theorem Term.ctorsIn_app {P : Program} {f : FnName} {args : List Term} :
    Term.CtorsIn P (.app f args) ↔
      (f, args.length) ∈ P.ctors ∧ ∀ a ∈ args, Term.CtorsIn P a := by
  simp only [Term.CtorsIn, Term.subterms_app, Set.mem_insert_iff, Set.mem_iUnion,
    exists_prop]
  constructor
  · intro h
    refine ⟨h f args (Or.inl rfl), fun a ha g bs hs => h g bs (Or.inr ⟨a, ha, hs⟩)⟩
  · rintro ⟨hf, h⟩ g bs hs
    rcases hs with hs' | ⟨a, ha, hs'⟩
    · obtain ⟨rfl, rfl⟩ : g = f ∧ bs = args := by
        constructor <;> [exact (Term.app.inj hs').1; exact (Term.app.inj hs').2]
      exact hf
    · exact h a ha g bs hs'

/-- Every application the state holds is one `P` applies at that arity. -/
def Database.CtorsIn (db : Database) (P : Program) : Prop :=
  ∀ f as, Term.app f as ∈ db.terms → (f, as.length) ∈ P.ctors

theorem Database.CtorsIn.term {db : Database} {P : Program} (hw : db.WF) (h : db.CtorsIn P)
    {t : Term} (ht : t ∈ db.terms) : Term.CtorsIn P t :=
  fun g bs hs => h g bs (hw.subtermClosed t ht hs)

theorem Database.empty_ctorsIn {P : Program} : Database.empty.CtorsIn P := by
  intro f as ht; exact absurd ht (by simp)

mutual

/-- **An expression whose applications `P` makes evaluates to a term whose applications `P`
makes**, in an environment whose bindings do. Building applies a head `Expr.ctors` recorded,
and `min` returns one of its operands, exactly as for `Expr.eval_litFree`. -/
theorem Expr.eval_ctorsIn {P : Program} {sig : Signature} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.CtorsIn P t) :
    ∀ (e : Expr) {t : Term}, (∀ fk ∈ e.ctors, fk ∈ P.ctors) →
      e.eval sig σ = some t → Term.CtorsIn P t
  | .lit _, _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      exact Term.ctorsIn_lit
  | .var v, t, _, he => hσ v t (Option.filter_eq_some_iff.mp he).1
  | .app f args, t, hc, he => by
      by_cases hcc : sig.IsCtor f
      · rw [Expr.eval_app_ctor hcc] at he
        obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
        refine Term.ctorsIn_app.mpr ⟨?_, ?_⟩
        · rw [Expr.evalList_length hts]
          exact hc _ (by rw [Expr.ctors]; exact List.mem_cons_self)
        · exact Expr.evalList_ctorsIn hσ args
            (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk)) hts
      · rw [Expr.eval_app_not_ctor hcc] at he
        exact absurd he (by simp)
  | .min a b, t, hc, he => by
      rw [Expr.eval_min, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, hmap⟩ := he
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rcases Term.least_eq_or x y with h | h <;> rw [h]
      · exact Expr.eval_ctorsIn hσ a
          (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_append_left _ hk)) hx
      · exact Expr.eval_ctorsIn hσ b
          (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_append_right _ hk)) hy

@[inherit_doc Expr.eval_ctorsIn]
theorem Expr.evalList_ctorsIn {P : Program} {sig : Signature} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.CtorsIn P t) :
    ∀ (es : List Expr) {ts : List Term}, (∀ fk ∈ Expr.ctorsList es, fk ∈ P.ctors) →
      Expr.evalList sig es σ = some ts → ∀ t ∈ ts, Term.CtorsIn P t
  | [], _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp
  | e :: es, ts, hc, he => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hrest⟩ := he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Expr.eval_ctorsIn hσ e
          (fun fk hk => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_left _ hk)) hu
      · exact Expr.evalList_ctorsIn hσ es
          (fun fk hk => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_right _ hk))
          hus t ht'

end

theorem Database.CtorsIn.lookup {db : Database} {P : Program} (hw : db.WF)
    (h : db.CtorsIn P) : ∀ v t, Env.lookup v db.env = some t → Term.CtorsIn P t :=
  fun v t hv => h.term hw (hw.envInTerms (v, t) (Env.mem_of_lookup hv))

/-- An action applies only constructor names and arities found in the source program. -/
def Action.CtorsIn (a : Action) (P : Program) : Prop := ∀ fk ∈ a.ctors, fk ∈ P.ctors

/-- `Action.CtorsIn` at every action a command runs. -/
def Cmd.CtorsIn : Cmd → Program → Prop
  | .rule r, P => ∀ a ∈ r.actions, a.CtorsIn P
  | _, _ => True

/-- **Every command of the source program is one**, since its own `Cmd.ctors` are among the
program's. -/
theorem Cmd.CtorsIn.of_domain {P : Program} (_hdom : P.Fragment) {c : Cmd} (hc : c ∈ P) :
    c.CtorsIn P := by
  cases c with
  | rule r =>
      intro a ha fk hk
      exact mem_program_ctors hc (by
        rw [Cmd.ctors]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩))
  | run R => trivial
  | saturate R => trivial
  | decl f dc => trivial
  | check _ => trivial

/-- Evaluating a source atom preserves its constructor names and arities. -/
theorem Expr.evalAtom_ctorsIn {P : Program} {sig : Signature} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.CtorsIn P t)
    (e : Expr) {t : Term} (hc : ∀ fk ∈ e.ctors, fk ∈ P.ctors)
    (he : e.evalAtom sig σ = some t) : Term.CtorsIn P t := by
  cases e with
  | lit _ => cases Option.some.inj he; exact Term.ctorsIn_lit
  | var v => exact hσ v t (Option.filter_eq_some_iff.mp he).1
  | min a b => exact Expr.eval_ctorsIn hσ (.min a b) hc he
  | app f args =>
    obtain ⟨ts, hts, rfl⟩ := Expr.evalAtom_app_inv he
    refine Term.ctorsIn_app.mpr ⟨?_, ?_⟩
    · rw [Expr.evalList_length hts]
      exact hc _ (by rw [Expr.ctors]; exact List.mem_cons_self)
    · exact Expr.evalList_ctorsIn hσ args
        (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk)) hts

theorem evalAction_ctorsIn {db db' : Database} {P : Program} (hw : db.WF) (h : db.CtorsIn P)
    {a : Action} (ha : a.CtorsIn P) (hv : evalAction db a = some db') : db'.CtorsIn P := by
  have hlk := h.lookup hw
  have hc := ha
  have hcin : ∀ {t : Term}, Term.CtorsIn P t →
      ∀ f as, Term.app f as ∈ t.subterms → (f, as.length) ∈ P.ctors := fun ht f as hs =>
    ht f as hs
  rcases evalAction_eq_some hv with ⟨e, t, rfl, he, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, he₁, he₂, -, rfl⟩
  · have ht : Term.CtorsIn P t := Expr.evalAtom_ctorsIn hlk e hc he
    intro g bs hs
    rw [Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact h g bs hs'
    · exact hcin ht g bs hs'
  · have hc₁ : ∀ fk ∈ e₁.ctors, fk ∈ P.ctors :=
      fun fk hk => hc fk (by rw [Action.ctors]; exact List.mem_append_left _ hk)
    have hc₂ : ∀ fk ∈ e₂.ctors, fk ∈ P.ctors :=
      fun fk hk => hc fk (by rw [Action.ctors]; exact List.mem_append_right _ hk)
    have ht₁ : Term.CtorsIn P t₁ := Expr.eval_ctorsIn hlk e₁ hc₁ he₁
    have ht₂ : Term.CtorsIn P t₂ := Expr.eval_ctorsIn hlk e₂ hc₂ he₂
    intro g bs hs
    rw [Database.addEq_terms] at hs
    rcases hs with hs' | hs'
    · rcases hs' with hs'' | hs''
      · exact h g bs hs''
      · exact hcin ht₁ g bs hs''
    · exact hcin ht₂ g bs hs'

theorem evalActions_ctorsIn {db db' : Database} {P : Program} (hw : db.WF) (h : db.CtorsIn P)
    {as : List Action} (hl : ∀ a ∈ as, a.CtorsIn P)
    (hv : evalActions db as = some db') : db'.CtorsIn P := by
  induction as generalizing db with
  | nil =>
      rw [evalActions_nil, Option.some_inj] at hv
      exact hv ▸ h
  | cons a as ih =>
      rw [evalActions_cons, Option.bind_eq_some_iff] at hv
      obtain ⟨d, hd, hrest⟩ := hv
      exact ih (evalAction_wf hw hd) (evalAction_ctorsIn hw h (hl a List.mem_cons_self) hd)
        (fun b hb => hl b (List.mem_cons_of_mem _ hb)) hrest

theorem evalLocalActions_ctorsIn {db db' : Database} {P : Program} (hw : db.WF)
    (h : db.CtorsIn P) {as : List Action} (hl : ∀ a ∈ as, a.CtorsIn P) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (hv : evalLocalActions db as σ = some db') :
    db'.CtorsIn P := by
  obtain ⟨d, hd, rfl⟩ := evalLocalActions_eq_some hv
  have hlf : ({ db with env := σ ++ db.env } : Database).CtorsIn P := by
    intro f as' ht; exact h f as' (Database.terms_setEnv ▸ ht)
  intro f as' ht
  rw [Database.terms_setEnvRules] at ht
  exact evalActions_ctorsIn (hw.appendEnv hσ) hlf hl hd f as' ht

/-- **The source-side invariant the view-declaration reading spends**: every application the
state holds is one `P` makes, and every rule the state holds has a head that applies only
those. The second clause is what the rule-firing case needs, for `Database.NoLits`' reason. -/
structure Database.CtorsInState (db : Database) (P : Program) : Prop where
  /-- Every application the state holds is one `P` makes. -/
  terms : db.CtorsIn P
  /-- Every rule the state holds applies only what `P` applies. -/
  heads : ∀ r ∈ db.rules, ∀ a ∈ r.actions, a.CtorsIn P

theorem Database.empty_ctorsInState {P : Program} : Database.empty.CtorsInState P where
  terms := Database.empty_ctorsIn
  heads := by intro r hr; exact absurd hr (by simp [Database.empty])

/-- **A round keeps it.** -/
theorem Database.CtorsInState.runRules {R : RulesetName} {db : Database} {P : Program}
    (hw : db.WF) (h : db.CtorsInState P) : (RunRules R db).CtorsInState P := by
  refine ⟨?_, ?_⟩
  · intro f as ht
    rw [RunRules, Database.sUnion_terms] at ht
    rcases ht with ht' | ht'
    · exact h.terms f as ht'
    · obtain ⟨d, hd, ht''⟩ := Set.mem_iUnion₂.mp ht'
      obtain ⟨r, hr, -, σ, hq, hfire⟩ := hd
      exact evalLocalActions_ctorsIn hw h.terms (h.heads r hr) hq.mem_terms hfire f as ht''
  · rw [RunRules, Database.sUnion_rules]; exact h.heads

/-- Source commands preserve the constructor census in both terms and rule heads. -/
theorem cmdStep_ctorsIn {db db' : Database} {P : Program} (hc : db.CtorState)
    (h : db.CtorsInState P) {c : Cmd} (hn : c.CtorsIn P) (hdecl : c.CtorDecl)
    (hstep : CmdStep db c db') : db'.CtorsInState P := by
  obtain ⟨d, hreach, hcl⟩ := hstep.reach
  cases c with
  | rule r =>
      obtain rfl : d = { db with rules := insert r db.rules } := hreach
      obtain rfl : db' = { db with rules := insert r db.rules } :=
        hcl.eq_of_allConstructors hc.sig
      refine ⟨fun f as ht => h.terms f as (Database.terms_setRules ▸ ht), ?_⟩
      intro r' hr'
      rcases Set.mem_insert_iff.mp hr' with rfl | hr''
      · exact hn
      · exact h.heads r' hr''
  | run R =>
      obtain rfl : d = RunRules R db := hreach
      obtain rfl : db' = RunRules R db :=
        hcl.eq_of_allConstructors (by rw [RunRules.sig]; exact hc.sig)
      exact h.runRules hc.wf
  | saturate R =>
      have hsat : SaturateReach R db db' := cmdStep_saturate_iff.mp hstep
      refine (RunReach.induction (P := fun x => x.CtorState ∧ x.CtorsInState P) ?_ hsat.reach
        ⟨hc, h⟩).2
      intro x y hx hxy
      obtain rfl : y = RunRules R x := hxy.eq_of_allConstructors hx.1.sig
      exact ⟨⟨RunRules.wf hx.1.wf, by rw [RunRules.sig]; exact hx.1.sig⟩,
        hx.2.runRules hx.1.wf⟩
  | decl f dc =>
      obtain rfl : d = { db with sig := Function.update db.sig f (some dc) } := hreach
      obtain rfl : db' = { db with sig := Function.update db.sig f (some dc) } :=
        hcl.eq_of_allConstructors (hc.sig.sigBind hdecl)
      exact ⟨fun f' as ht => h.terms f' as (Database.terms_setSig ▸ ht), h.heads⟩
  | check q =>
      obtain ⟨_, rfl⟩ := hreach
      rw [hcl.eq_of_allConstructors hc.sig]
      exact h

@[inherit_doc cmdStep_ctorsIn]
theorem programStep_ctorsIn {db db' : Database} {P : Program} (hc : db.CtorState)
    (h : db.CtorsInState P) {p : Program} (hn : ∀ c ∈ p, c.CtorsIn P) (hdecl : p.CtorDecls)
    (hstep : ProgramStep db p db') : db'.CtorsInState P := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hstep _ ih =>
      exact ih (hstep.ctorState hc (hdecl c List.mem_cons_self))
        (cmdStep_ctorsIn hc h (hn c List.mem_cons_self) (hdecl c List.mem_cons_self) hstep)
        (fun c' hc' => hn c' (List.mem_cons_of_mem c hc'))
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

/-- Every constructor in a reached source prefix occurs in the whole program at that arity. -/
theorem ctorsIn_of_prefixStep {P : Program} (hdom : P.Fragment) {p : Program}
    (hsub : ∀ c ∈ p, c ∈ P) {sd : Database} (hstep : ProgramStep Database.empty p sd) :
    sd.CtorsIn P :=
  (programStep_ctorsIn Database.CtorState.empty Database.empty_ctorsInState
    (fun c hc => Cmd.CtorsIn.of_domain hdom (hsub c hc))
    (fun c hc => hdom.ctorsOnly c (hsub c hc)) hstep).terms

end Egglog
