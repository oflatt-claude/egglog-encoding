import EgglogSemantics.Encoding.Correspond

namespace Egglog

/-! ### Literal-free terms and states -/

/-- No literal occurs in `t`. -/
def Term.LitFree (t : Term) : Prop := ∀ s ∈ t.subterms, ¬ s.isLit

theorem Term.not_litFree_lit {l : Lit} : ¬ Term.LitFree (.lit l) := by
  intro h
  exact h _ (Term.self_mem_subterms _) rfl

theorem Term.litFree_app {f : FnName} {args : List Term} :
    Term.LitFree (.app f args) ↔ ∀ a ∈ args, Term.LitFree a := by
  simp only [Term.LitFree, Term.subterms_app, Set.mem_insert_iff, Set.mem_iUnion,
    exists_prop, forall_eq_or_imp]
  constructor
  · rintro ⟨-, h⟩ a ha s hs
    exact h s ⟨a, ha, hs⟩
  · rintro h
    refine ⟨by simp [Term.isLit], ?_⟩
    rintro s ⟨a, ha, hs⟩
    exact h a ha s hs

/-- No term the state holds is a literal. -/
def Database.LitFree (db : Database) : Prop := ∀ t ∈ db.terms, ¬ t.isLit

theorem Database.LitFree.term {db : Database} (hw : db.WF) (h : db.LitFree) {t : Term}
    (ht : t ∈ db.terms) : Term.LitFree t :=
  fun s hs => h s (hw.subtermClosed t ht hs)

theorem Database.empty_litFree : Database.empty.LitFree := by
  intro t ht; exact absurd ht (by simp)

/-! ### Evaluation of a literal-free expression builds a literal-free term -/

mutual

/-- **A literal-free expression evaluates to a literal-free term**, in an environment whose
bindings are literal-free. `Prim.ofName f = none` is what keeps the primitive branch out:
`ordering-gt` returns a fresh `bool` literal from operands that hold none, so the clause is
about the applied names and not only about the syntax. -/
theorem Expr.eval_litFree {sig : Signature} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t) :
    ∀ (e : Expr) {t : Term}, e.litFreeB = true → (∀ f ∈ e.fns, Prim.ofName f = none) →
      e.eval sig σ = some t → Term.LitFree t
  | .lit _, _, hl, _, _ => by simp [Expr.litFreeB] at hl
  | .var v, t, _, _, he => hσ v t he
  | .app f args, t, hl, hf, he => by
      rw [Expr.eval_app_ctor (hf f (by simp [Expr.fns])) ?_] at he
      · obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
        refine Term.litFree_app.mpr ?_
        exact Expr.evalList_litFree hσ args (by simpa [Action.litFreeB, Expr.litFreeB] using hl)
          (fun g hg => hf g (by simp [Expr.fns, hg])) hts
      · by_contra hc
        rw [Expr.eval_app_not_ctor (hf f (by simp [Expr.fns])) hc] at he
        exact absurd he (by simp)

@[inherit_doc Expr.eval_litFree]
theorem Expr.evalList_litFree {sig : Signature} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t) :
    ∀ (es : List Expr) {ts : List Term}, Expr.litFreeListB es = true →
      (∀ f ∈ Expr.fnsList es, Prim.ofName f = none) →
      Expr.evalList sig es σ = some ts → ∀ t ∈ ts, Term.LitFree t
  | [], _, _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp
  | e :: es, ts, hl, hf, he => by
      rw [Expr.litFreeListB, Bool.and_eq_true] at hl
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hrest⟩ := he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Expr.eval_litFree hσ e hl.1 (fun g hg => hf g (by simp [hg])) hu
      · exact Expr.evalList_litFree hσ es hl.2 (fun g hg => hf g (by simp [hg])) hus t ht'

end

end Egglog

namespace Egglog

/-! ### The primitive condition, at the applied names -/

/-- `Program.EncodeDomain.noPrim` reads `Program.ctors` and evaluation reads `Expr.fns`. -/
theorem noPrim_fns {e : Expr} (hp : ∀ fk ∈ e.ctors, Prim.ofName fk.1 = none) :
    ∀ f ∈ e.fns, Prim.ofName f = none := fun f hf =>
  let ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hf
  hp (f, k) hk

@[inherit_doc noPrim_fns]
theorem noPrim_fnsList {es : List Expr}
    (hp : ∀ fk ∈ Expr.ctorsList es, Prim.ofName fk.1 = none) :
    ∀ f ∈ Expr.fnsList es, Prim.ofName f = none := fun f hf =>
  let ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hf
  hp (f, k) hk

/-! ### One action keeps the state literal-free -/

theorem Database.LitFree.lookup {db : Database} (hw : db.WF) (h : db.LitFree) :
    ∀ v t, Env.lookup v db.env = some t → Term.LitFree t := fun v t hv =>
  h.term hw (hw.envInTerms (v, t) (Env.mem_of_lookup hv))

/-- **A literal-free action keeps the state literal-free.** Every writer is an `addTerm` or
an `addEq` of a value `Expr.eval_litFree` covers. -/
theorem evalAction_litFree {db db' : Database} (hw : db.WF) (h : db.LitFree)
    {a : Action} (hl : a.litFreeB = true) (hp : ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none)
    (hv : evalAction db a = some db') : db'.LitFree := by
  have hlk := h.lookup hw
  rcases evalAction_eq_some hv with ⟨e, t, rfl, he, rfl⟩ | ⟨v, e, t, rfl, he, rfl⟩ |
      ⟨e₁, e₂, t₁, t₂, rfl, he₁, he₂, -, rfl⟩ | ⟨f, args, out, as, vs, rfl, ha, hb, rfl⟩
  · have ht : Term.LitFree t :=
      Expr.eval_litFree hlk e hl (noPrim_fns hp) he
    intro s hs
    rw [Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact h s hs'
    · exact ht s hs'
  · have ht : Term.LitFree t :=
      Expr.eval_litFree hlk e hl (noPrim_fns hp) he
    intro s hs
    rw [Database.terms_setEnv, Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact h s hs'
    · exact ht s hs'
  · rw [Action.litFreeB, Bool.and_eq_true] at hl
    have hp₁ : ∀ fk ∈ e₁.ctors, Prim.ofName fk.1 = none :=
      fun fk hk => hp fk (by rw [Action.ctors]; exact List.mem_append_left _ hk)
    have hp₂ : ∀ fk ∈ e₂.ctors, Prim.ofName fk.1 = none :=
      fun fk hk => hp fk (by rw [Action.ctors]; exact List.mem_append_right _ hk)
    have ht₁ : Term.LitFree t₁ := Expr.eval_litFree hlk e₁ hl.1 (noPrim_fns hp₁) he₁
    have ht₂ : Term.LitFree t₂ := Expr.eval_litFree hlk e₂ hl.2 (noPrim_fns hp₂) he₂
    intro s hs
    rw [Database.addEq_terms] at hs
    rcases hs with hs' | hs'
    · rcases hs' with hs'' | hs''
      · exact h s hs''
      · exact ht₁ s hs''
    · exact ht₂ s hs'
  · rw [Action.litFreeB, Bool.and_eq_true] at hl
    have hp₁ : ∀ fk ∈ Expr.ctorsList args, Prim.ofName fk.1 = none :=
      fun fk hk => hp fk (List.mem_cons_of_mem _ (List.mem_append_left _ hk))
    have hp₂ : ∀ fk ∈ Expr.ctorsList out, Prim.ofName fk.1 = none :=
      fun fk hk => hp fk (List.mem_cons_of_mem _ (List.mem_append_right _ hk))
    have hall : ∀ u ∈ as ++ vs, Term.LitFree u := by
      intro u hu
      rcases List.mem_append.mp hu with hu' | hu'
      · exact Expr.evalList_litFree hlk args hl.1 (noPrim_fnsList hp₁) ha u hu'
      · exact Expr.evalList_litFree hlk out hl.2 (noPrim_fnsList hp₂) hb u hu'
    intro s hs
    rw [Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact h s hs'
    · exact Term.litFree_app.mpr hall s hs'

end Egglog

namespace Egglog

/-- What one action must be for `evalAction` to keep the state literal-free: no literal in
the expressions it evaluates, and no applied name a primitive — `ordering-gt` returns a
`bool` literal from operands that hold none. -/
def Action.NoLits (a : Action) : Prop :=
  a.litFreeB = true ∧ ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none

/-- `Action.NoLits` at every action a command runs. Vacuous at a run, a saturation and a
declaration, which evaluate nothing. -/
def Cmd.NoLits : Cmd → Prop
  | .action a => a.NoLits
  | .rule r => ∀ a ∈ r.actions, a.NoLits
  | _ => True

theorem evalActions_litFree {db db' : Database} (hw : db.WF) (h : db.LitFree)
    {as : List Action} (hl : ∀ a ∈ as, a.NoLits)
    (hv : evalActions db as = some db') : db'.LitFree := by
  induction as generalizing db with
  | nil =>
      rw [evalActions_nil, Option.some_inj] at hv
      exact hv ▸ h
  | cons a as ih =>
      rw [evalActions_cons, Option.bind_eq_some_iff] at hv
      obtain ⟨d, hd, hrest⟩ := hv
      have ha := hl a List.mem_cons_self
      refine ih (evalAction_wf hw hd) (evalAction_litFree hw h ha.1 ha.2 hd) ?_ hrest
      exact fun b hb => hl b (List.mem_cons_of_mem _ hb)

theorem evalLocalActions_litFree {db db' : Database} (hw : db.WF) (h : db.LitFree)
    {as : List Action} (hl : ∀ a ∈ as, a.NoLits) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (hv : evalLocalActions db as σ = some db') :
    db'.LitFree := by
  obtain ⟨d, hd, rfl⟩ := evalLocalActions_eq_some hv
  have hlf : ({ db with env := db.env ++ σ } : Database).LitFree := by
    intro t ht; exact h t (Database.terms_setEnv ▸ ht)
  intro t ht
  rw [Database.terms_setEnvRules] at ht
  exact evalActions_litFree (hw.appendEnv hσ) hlf hl hd t ht

/-- **The source-side invariant `noLitUnion`'s second arm is carried as**: no term the state
holds is a literal, and every rule it holds has a literal-free head. The second clause is what
the rule-firing case needs — a firing evaluates a head the *state* carries, not one the
command names. -/
structure Database.NoLits (db : Database) : Prop where
  /-- No term the state holds is a literal, so no variable is bound to one. -/
  terms : db.LitFree
  /-- Every rule the state holds has a literal-free head. -/
  heads : ∀ r ∈ db.rules, ∀ a ∈ r.actions, a.NoLits

theorem Database.empty_noLits : Database.empty.NoLits where
  terms := Database.empty_litFree
  heads := by intro r hr; exact absurd hr (by simp [Database.empty])

/-- **A round keeps it.** `RunRules` is a `Database.sUnion` over the firings, each of which is
an `evalLocalActions` of a head the state carries. -/
theorem Database.NoLits.runRules {R : RulesetName} {db : Database} (hw : db.WF)
    (h : db.NoLits) : (RunRules R db).NoLits := by
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [RunRules, Database.sUnion_terms] at ht
    rcases ht with ht' | ht'
    · exact h.terms t ht'
    · obtain ⟨d, hd, ht''⟩ := Set.mem_iUnion₂.mp ht'
      obtain ⟨r, hr, -, σ, hq, hfire⟩ := hd
      exact evalLocalActions_litFree hw h.terms (h.heads r hr) hq.mem_terms hfire t ht''
  · rw [RunRules, Database.sUnion_rules]; exact h.heads

end Egglog

namespace Egglog

/-! ### One command and one run keep it -/

theorem cmdStep_noLits {db db' : Database} (hc : db.CtorState) (h : db.NoLits)
    {c : Cmd} (hn : c.NoLits) (hdecl : c.CtorDecl) (hstep : CmdStep db c db') :
    db'.NoLits := by
  obtain ⟨d, hreach, hcl⟩ := hstep
  cases c with
  | action a =>
      have hv : evalAction db a = some d := hreach
      obtain rfl : db' = d :=
        hcl.eq_of_allConstructors (by rw [evalAction_sig hv]; exact hc.sig)
      exact ⟨evalAction_litFree hc.wf h.terms hn.1 hn.2 hv,
        by rw [evalAction_rules hv]; exact h.heads⟩
  | rule r =>
      have hv : some { db with rules := insert r db.rules } = some d := hreach
      obtain rfl : d = { db with rules := insert r db.rules } := (Option.some.inj hv).symm
      obtain rfl : db' = { db with rules := insert r db.rules } :=
        hcl.eq_of_allConstructors hc.sig
      refine ⟨fun t ht => h.terms t (Database.terms_setRules ▸ ht), ?_⟩
      intro r' hr'
      rcases Set.mem_insert_iff.mp hr' with rfl | hr''
      · exact hn
      · exact h.heads r' hr''
  | run R =>
      have hv : some (RunRules R db) = some d := hreach
      obtain rfl : d = RunRules R db := (Option.some.inj hv).symm
      obtain rfl : db' = RunRules R db :=
        hcl.eq_of_allConstructors (by rw [RunRules.sig]; exact hc.sig)
      exact h.runRules hc.wf
  | saturate R =>
      have hsat : SaturateReach R db db' := cmdStep_saturate_iff.mp ⟨d, hreach, hcl⟩
      refine (RunReach.induction (P := fun x => x.CtorState ∧ x.NoLits) ?_ hsat.1 ⟨hc, h⟩).2
      intro x y hx hxy
      obtain rfl : y = RunRules R x := hxy.eq_of_allConstructors hx.1.sig
      exact ⟨⟨RunRules.wf hx.1.wf, by rw [RunRules.sig]; exact hx.1.sig⟩,
        hx.2.runRules hx.1.wf⟩
  | decl f dc =>
      have hv : some { db with sig := Function.update db.sig f (some dc) } = some d := hreach
      obtain rfl : d = { db with sig := Function.update db.sig f (some dc) } :=
        (Option.some.inj hv).symm
      obtain rfl : db' = { db with sig := Function.update db.sig f (some dc) } :=
        hcl.eq_of_allConstructors (hc.sig.sigBind hdecl)
      exact ⟨fun t ht => h.terms t (Database.terms_setSig ▸ ht), h.heads⟩

/-- **`Database.NoLits` at every state a run reaches.** Applied to a *prefix* of the source
program it is the invariant at the state a firing command starts from, which is where the
head's own `union` check is spent. -/
theorem programStep_noLits {db db' : Database} (hc : db.CtorState) (h : db.NoLits)
    {p : Program} (hn : ∀ c ∈ p, c.NoLits) (hdecl : p.CtorDecls)
    (hstep : ProgramStep db p db') : db'.NoLits := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hstep _ ih =>
      exact ih (hstep.ctorState hc (hdecl c List.mem_cons_self))
        (cmdStep_noLits hc h (hn c List.mem_cons_self) (hdecl c List.mem_cons_self) hstep)
        (fun c' hc' => hn c' (List.mem_cons_of_mem c hc'))
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

end Egglog

namespace Egglog

/-! ### The block evaluates

`Spec/Scope.lean`'s `Action.Evaluable` asks a `union` operand to be an **application**, which
is the strongest condition readable off the expression alone and which a lit-free program's
*variable* operand fails: a query binds a variable to a term the source holds, and that term
is not a literal for a reason about the **state**. So the block lemma is restated with that
clause replaced by the two arms of `Program.EncodeDomain.noLitUnion`, which is exactly what
`evalAction`'s own check spends. -/

/-- `Action.Evaluable` with the `union` operands' `Expr.IsApp` dropped: every expression the
action evaluates builds, and nothing is asked about literals. -/
def Action.Builds : Action → Signature → Prop
  | .expr e, sig => e.Evaluable sig
  | .letBind _ e, sig => e.Evaluable sig
  | .union e₁ e₂, sig => e₁.Evaluable sig ∧ e₂.Evaluable sig
  | .set _ args out, sig => (∀ e ∈ args, e.Evaluable sig) ∧ ∀ e ∈ out, e.Evaluable sig

@[simp] def Actions.Builds : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Builds sig ∧ Actions.Builds as sig

/-- **The `union` check, as the block needs it**: either the block asserts no equation, or
the state holds no literal and the block evaluates none. The two arms of
`Program.EncodeDomain.noLitUnion`, and both survive one action — which is what lets the fold
carry the disjunction rather than one arm at a time. -/
def Actions.UnionRunnable (as : List Action) (db : Database) : Prop :=
  Actions.UnionFree as ∨ (db.LitFree ∧ ∀ a ∈ as, a.NoLits)

/-- **One action does not get stuck.** `evalAction_isSome_of_scoped` with the `union` clause
weakened to `Actions.UnionRunnable`. -/
theorem evalAction_isSome_of_builds {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    (hw : db.WF) {a : Action} {as : List Action} (hsc : a.Scoped Γ) (hb : a.Builds db.sig)
    (hr : Actions.UnionRunnable (a :: as) db) :
    ∃ db', evalAction db a = some db' ∧ (a.bind Γ).Models db'.env := by
  cases a with
  | expr e =>
      obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm hsc.2 hb
      exact ⟨db.addTerm t, by simp [evalAction, ht], hm⟩
  | letBind v e =>
      obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm hsc hb
      refine ⟨{ db.addTerm t with env := (v, t) :: db.env }, by simp [evalAction, ht], ?_⟩
      intro w
      simp only [Action.bind, List.mem_cons, Env.dom_cons]
      exact or_congr_right (hm w)
  | union e₁ e₂ =>
      obtain ⟨t₁, ht₁⟩ := Expr.eval_isSome_of_scoped hm hsc.1 hb.1
      obtain ⟨t₂, ht₂⟩ := Expr.eval_isSome_of_scoped hm hsc.2 hb.2
      rcases hr with huf | ⟨hlf, hnl⟩
      · exact absurd huf.1 id
      · obtain ⟨hl, hp⟩ := hnl _ List.mem_cons_self
        rw [Action.litFreeB, Bool.and_eq_true] at hl
        have hp₁ : ∀ fk ∈ e₁.ctors, Prim.ofName fk.1 = none :=
          fun fk hk => hp fk (List.mem_append_left _ hk)
        have hp₂ : ∀ fk ∈ e₂.ctors, Prim.ofName fk.1 = none :=
          fun fk hk => hp fk (List.mem_append_right _ hk)
        have hlk := hlf.lookup hw
        have hn₁ : ¬ t₁.isLit :=
          Expr.eval_litFree hlk e₁ hl.1 (noPrim_fns hp₁) ht₁ t₁ (Term.self_mem_subterms t₁)
        have hn₂ : ¬ t₂.isLit :=
          Expr.eval_litFree hlk e₂ hl.2 (noPrim_fns hp₂) ht₂ t₂ (Term.self_mem_subterms t₂)
        exact ⟨db.addEq t₁ t₂, by simp [evalAction, ht₁, ht₂, hn₁, hn₂], hm⟩
  | set f args out =>
      obtain ⟨cs, hcs⟩ := Expr.evalList_isSome args
        (fun v hv => by
          obtain ⟨e, hmem, hve⟩ := Expr.mem_varsList hv
          exact (hm v).mp (hsc.1 e hmem v hve))
        (fun g hg => by
          obtain ⟨e, hmem, hge⟩ := Expr.mem_fnsList hg
          exact hb.1 e hmem g hge)
      obtain ⟨vs, hvs⟩ := Expr.evalList_isSome out
        (fun v hv => by
          obtain ⟨e, hmem, hve⟩ := Expr.mem_varsList hv
          exact (hm v).mp (hsc.2 e hmem v hve))
        (fun g hg => by
          obtain ⟨e, hmem, hge⟩ := Expr.mem_fnsList hg
          exact hb.2 e hmem g hge)
      refine ⟨db.addTerm (.app f (cs ++ vs)), by simp [evalAction, hcs, hvs], ?_⟩
      simpa [Action.bind] using hm

/-- **The block does not get stuck.** The fold, with `Actions.UnionRunnable` as the
invariant: the union-free arm shrinks with the list, and the literal-free arm is carried by
`evalAction_litFree`. -/
theorem evalActions_isSome_of_builds {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    (hw : db.WF) {as : List Action} (hsc : Actions.Scoped as Γ)
    (hb : Actions.Builds as db.sig) (hr : Actions.UnionRunnable as db) :
    ∃ db', evalActions db as = some db' ∧ (Actions.bind as Γ).Models db'.env := by
  induction as generalizing db Γ with
  | nil => exact ⟨db, rfl, hm⟩
  | cons a as ih =>
      obtain ⟨db₁, h₁, hm₁⟩ := evalAction_isSome_of_builds hm hw hsc.1 hb.1 hr
      have hsig : db₁.sig = db.sig := evalAction_sig h₁
      have hr₁ : Actions.UnionRunnable as db₁ := by
        rcases hr with huf | ⟨hlf, hnl⟩
        · exact Or.inl huf.2
        · obtain ⟨hl, hp⟩ := hnl a List.mem_cons_self
          exact Or.inr ⟨evalAction_litFree hw hlf hl hp h₁,
            fun b hb' => hnl b (List.mem_cons_of_mem _ hb')⟩
      obtain ⟨db₂, h₂, hm₂⟩ :=
        ih hm₁ (evalAction_wf hw h₁) hsc.2 (by rw [hsig]; exact hb.2) hr₁
      exact ⟨db₂, by simp [h₁, h₂], hm₂⟩

/-- **A rule head does not get stuck**, at the substitution its query delivered.
`Spec/Scope.lean`'s `evalLocalActions_isSome_of_scoped` with the `union` clause weakened. -/
theorem evalLocalActions_isSome_of_builds {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    (hw : db.WF) {r : Rule} (hsc : Actions.Scoped r.actions (Query.bind r.query Γ))
    (hb : Actions.Builds r.actions db.sig)
    (hr : Actions.UnionRunnable r.actions db) {σ : Env}
    (hq : ValidQuerySubst db r.query σ) :
    ∃ d, evalActions { db with env := db.env ++ σ } r.actions = some d ∧
      evalLocalActions db r.actions σ = some { d with env := db.env, rules := db.rules } := by
  obtain ⟨d, hd, -⟩ := evalActions_isSome_of_builds
    (db := { db with env := db.env ++ σ }) (Query.bind_models hm hq)
    (hw.appendEnv hq.mem_terms) hsc hb
    (by rcases hr with huf | ⟨hlf, hnl⟩
        · exact Or.inl huf
        · exact Or.inr ⟨fun t ht => hlf t (Database.terms_setEnv ▸ ht), hnl⟩)
  exact ⟨d, hd, by simp [evalLocalActions, hd]⟩

end Egglog

namespace Egglog

/-! ### Where in the block an action ran

`hfired` is stated at the block's *initial* environment `src.env ++ τ`, and an action after a
`letBind` in the same block runs at an extended one. So the block lemma has to say which
environment each action saw, and it is the initial one extended by a prefix whose domain is
the `let`s the block performed before it. -/

/-- The variable a `let` binds; nothing for any other action. -/
def Action.letVars : Action → List Var
  | .letBind v _ => [v]
  | _ => []

/-- The variables a block's `let`s bind, which is what an action's environment can carry
beyond the block's own. -/
def Actions.letVars (as : List Action) : List Var := as.flatMap Action.letVars

/-- **Only a `let` extends the environment**, and it extends it by its own binder. -/
theorem evalAction_env_append {db db' : Database} {a : Action}
    (h : evalAction db a = some db') :
    ∃ δ, db'.env = δ ++ db.env ∧ ∀ v ∈ Env.dom δ, v ∈ a.letVars := by
  rcases evalAction_eq_some h with ⟨e, t, rfl, -, rfl⟩ | ⟨v, e, t, rfl, -, rfl⟩ |
      ⟨e₁, e₂, t₁, t₂, rfl, -, -, -, rfl⟩ | ⟨f, args, out, cs, vs, rfl, -, -, rfl⟩
  · exact ⟨[], rfl, by simp⟩
  · exact ⟨[(v, t)], rfl, by simp [Action.letVars]⟩
  · exact ⟨[], rfl, by simp⟩
  · exact ⟨[], rfl, by simp⟩

/-- **Each action of a block ran at the block's own state, extended by the `let`s before
it**, and what it wrote is in the block's result. The environment clause is the one `hfired`
does not state; `Database.Contained` is what carries the write to the end of the block. -/
theorem exists_step_of_mem_evalActions : ∀ {as : List Action} {db d : Database},
    evalActions db as = some d → ∀ a ∈ as,
      ∃ δ e e', (∀ v ∈ Env.dom δ, v ∈ Actions.letVars as) ∧ e.sig = db.sig ∧
        e.env = δ ++ db.env ∧ evalAction e a = some e' ∧ Database.Contained e' d
  | [], _, _, _, a, ha => absurd ha (by simp)
  | b :: bs, db, d, hv, a, ha => by
      rw [evalActions_cons, Option.bind_eq_some_iff] at hv
      obtain ⟨db₁, h₁, hrest⟩ := hv
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨[], db, db₁, by simp, rfl, by simp, h₁, evalActions_contained hrest⟩
      · obtain ⟨δ, e, e', hdom, hsig, henv, hs, hcont⟩ :=
          exists_step_of_mem_evalActions hrest a ha'
        obtain ⟨δ₁, henv₁, hdom₁⟩ := evalAction_env_append h₁
        refine ⟨δ ++ δ₁, e, e', ?_, by rw [hsig, evalAction_sig h₁], ?_, hs, hcont⟩
        · intro v hvm
          rw [Env.dom_append, List.mem_append] at hvm
          rw [Actions.letVars, List.flatMap_cons, List.mem_append]
          rcases hvm with hv' | hv'
          · exact Or.inr (hdom v hv')
          · exact Or.inl (hdom₁ v hv')
        · rw [henv, henv₁, List.append_assoc]

end Egglog

namespace Egglog

/-! ### `hfired`, discharged

The three parts of `hfired` composed: the block evaluates (`evalLocalActions_isSome_of_builds`,
out of the two domain clauses), each action ran at an environment the block's `let`s extended
(`exists_step_of_mem_evalActions`), and the write reaches the round's post-state
(`mem_terms_of_ruleFired`, `mem_eqs_of_ruleFired`). -/

/-- **The head's variables are bound where it runs**: the query's, the state's globals, or
the block's own `let`s. `Spec/Scope.lean`'s `Actions.Scoped` at the scope the state's
environment already is, so nothing has to model anything.

Not a domain clause, and it is not one because it costs nothing to ask here: a head variable
neither the query nor a global binds sticks the **encoded** head too — `encodeBuild` keeps a
source variable as itself and the encoded query binds no name the source query does not — so
such a firing writes on neither side. -/
def Rule.HeadScoped (r : Rule) (db : Database) : Prop :=
  Actions.Scoped r.actions (Query.bind r.query (Env.dom db.env))

theorem Scope.Models.dom (σ : Env) : Scope.Models (Env.dom σ) σ := fun _ => Iff.rfl

/-- **A source rule of the round writes, and where.** The firing exists — which is what
`RuleResults` asks and what a stuck head denies — and each action of its head ran at the
environment `src.env ++ τ` extended by the `let`s before it, with its own writes reaching the
round's post-state. -/
theorem exists_headStep_of_ruleFired {R : RulesetName} {c : Cmd} {sd sd' : Database}
    {r : Rule} (hfire : c = Cmd.run R ∨ c = Cmd.saturate R)
    (hstep : CmdStep sd c sd') (hw : sd.WF)
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hsc : r.HeadScoped sd)
    (hb : Actions.Builds r.actions sd.sig) (hun : Actions.UnionRunnable r.actions sd)
    {τ : Env} (hq : ValidQuerySubst sd r.query τ) :
    ∀ a ∈ r.actions, ∃ δ e e', (∀ v ∈ Env.dom δ, v ∈ Actions.letVars r.actions) ∧
      e.sig = sd.sig ∧ e.env = δ ++ (sd.env ++ τ) ∧ evalAction e a = some e' ∧
      (∀ t ∈ e'.terms, t ∈ sd'.terms) ∧ (∀ p ∈ e'.eqs, p ∈ sd'.eqs) := by
  obtain ⟨d, hd, hlocal⟩ :=
    evalLocalActions_isSome_of_builds (Scope.Models.dom sd.env) hw hsc hb hun hq
  intro a ha
  obtain ⟨δ, e, e', hdom, hsig, henv, hs, hcont⟩ := exists_step_of_mem_evalActions hd a ha
  refine ⟨δ, e, e', hdom, hsig, henv, hs, ?_, ?_⟩
  · intro t ht
    exact mem_terms_of_ruleFired hfire hstep hr hrs hq hlocal
      (Database.terms_setEnvRules ▸ hcont.terms ht)
  · intro p hp
    exact mem_eqs_of_ruleFired hfire hstep hr hrs hq hlocal (hcont.eqs hp)

/-- **`hfired` for `entrySound_headBuild`.** The head's own build, at the substitution the
correspondence returns: the term the source's head evaluation gives is a term the round's
post-state holds.

`hlet` is what the two states' shapes cost. `hfired` reads the head at the block's *initial*
environment, and an action after a `letBind` runs at an extended one; where the head mentions
none of the block's own binders the two environments agree on what the head reads
(`Expr.eval_agreeOn`) and the extension drops out. All seventy in-domain cases satisfy it
outright — no rule head there binds anything. -/
theorem mem_terms_of_headBuild {R : RulesetName} {c : Cmd} {sd sd' : Database}
    {r : Rule} (hfire : c = Cmd.run R ∨ c = Cmd.saturate R)
    (hstep : CmdStep sd c sd') (hw : sd.WF)
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hsc : r.HeadScoped sd)
    (hb : Actions.Builds r.actions sd.sig) (hun : Actions.UnionRunnable r.actions sd)
    {τ : Env} (hq : ValidQuerySubst sd r.query τ)
    {f : FnName} {args : List Expr} (ha : Action.expr (.app f args) ∈ r.actions)
    (hlet : ∀ v ∈ (Expr.app f args).vars, v ∉ Actions.letVars r.actions)
    {is : List Term}
    (hval : (Expr.app f args).eval sd.sig (sd.env ++ τ) = some (.app f is)) :
    Term.app f is ∈ sd'.terms := by
  obtain ⟨δ, e, e', hdom, hsig, henv, hs, hterms, -⟩ :=
    exists_headStep_of_ruleFired hfire hstep hw hr hrs hsc hb hun hq _ ha
  have hagree : ∀ v ∈ (Expr.app f args).vars,
      Env.lookup v e.env = Env.lookup v (sd.env ++ τ) := by
    intro v hv
    rw [henv]
    exact Env.lookup_append_of_not_mem fun hc => hlet v hv (hdom v hc)
  have heval : (Expr.app f args).eval e.sig e.env = some (.app f is) := by
    rw [hsig, Expr.eval_agreeOn (sig := sd.sig) _ hagree]; exact hval
  rcases evalAction_eq_some hs with ⟨g, t, hg, hev, rfl⟩ | ⟨v, g, t, hg, -, -⟩ |
      ⟨g₁, g₂, t₁, t₂, hg, -, -, -, -⟩ | ⟨g, cs, out, as, vs, hg, -, -, -⟩
  · obtain rfl : g = Expr.app f args := by injection hg with h; exact h.symm
    obtain rfl : t = Term.app f is := Option.some.inj (hev.symm.trans heval)
    exact hterms _ (Database.mem_addTerm _ _)
  · exact absurd hg (by simp)
  · exact absurd hg (by simp)
  · exact absurd hg (by simp)

/-- **`hfired` for `cong_headUnion`.** The head's own `union`, at the same substitution: the
pair the source's head asserted is a pair the round's post-state asserts. `hlet` is what it
is in `mem_terms_of_headBuild`. -/
theorem mem_eqs_of_headUnion {R : RulesetName} {c : Cmd} {sd sd' : Database}
    {r : Rule} (hfire : c = Cmd.run R ∨ c = Cmd.saturate R)
    (hstep : CmdStep sd c sd') (hw : sd.WF)
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hsc : r.HeadScoped sd)
    (hb : Actions.Builds r.actions sd.sig) (hun : Actions.UnionRunnable r.actions sd)
    {τ : Env} (hq : ValidQuerySubst sd r.query τ)
    {e₁ e₂ : Expr} (ha : Action.union e₁ e₂ ∈ r.actions)
    (hlet : ∀ v ∈ e₁.vars ∪ e₂.vars, v ∉ Actions.letVars r.actions)
    {t₁ t₂ : Term} (hv₁ : e₁.eval sd.sig (sd.env ++ τ) = some t₁)
    (hv₂ : e₂.eval sd.sig (sd.env ++ τ) = some t₂) : (t₁, t₂) ∈ sd'.eqs := by
  obtain ⟨δ, e, e', hdom, hsig, henv, hs, -, heqs⟩ :=
    exists_headStep_of_ruleFired hfire hstep hw hr hrs hsc hb hun hq _ ha
  have hagree : ∀ v ∈ e₁.vars ∪ e₂.vars,
      Env.lookup v e.env = Env.lookup v (sd.env ++ τ) := by
    intro v hv
    rw [henv]
    exact Env.lookup_append_of_not_mem fun hc => hlet v hv (hdom v hc)
  have he₁ : e₁.eval e.sig e.env = some t₁ := by
    rw [hsig, Expr.eval_agreeOn (sig := sd.sig) _
      (fun v hv => hagree v (List.mem_union_iff.mpr (Or.inl hv)))]
    exact hv₁
  have he₂ : e₂.eval e.sig e.env = some t₂ := by
    rw [hsig, Expr.eval_agreeOn (sig := sd.sig) _
      (fun v hv => hagree v (List.mem_union_iff.mpr (Or.inr hv)))]
    exact hv₂
  rcases evalAction_eq_some hs with ⟨g, t, hg, -, -⟩ | ⟨v, g, t, hg, -, -⟩ |
      ⟨g₁, g₂, u₁, u₂, hg, hu₁, hu₂, -, rfl⟩ | ⟨g, cs, out, as, vs, hg, -, -, -⟩
  · exact absurd hg (by simp)
  · exact absurd hg (by simp)
  · obtain ⟨rfl, rfl⟩ : g₁ = e₁ ∧ g₂ = e₂ := by
      injection hg with h₁ h₂
      exact ⟨h₁.symm, h₂.symm⟩
    obtain rfl : u₁ = t₁ := Option.some.inj (hu₁.symm.trans he₁)
    obtain rfl : u₂ = t₂ := Option.some.inj (hu₂.symm.trans he₂)
    exact heqs _ (by rw [Database.addEq_eqs]; exact Set.mem_insert _ _)
  · exact absurd hg (by simp)

end Egglog

namespace Egglog

/-! ### The two domain clauses, as the block's hypotheses

`EncodeDomain.headsDeclared` is `Actions.Declared` at the signature the source program's
prefix has installed, and the state a firing reads is later than that — `Cmd.sigBind` only
ever writes a `some`, so a name declared before the rule is declared at the firing.
`EncodeDomain.noPrim` and `ctorsOnly` then turn declaredness into `Signature.IsCtor`, which is
what `Expr.eval` needs. -/

/-- One signature declares everything another does. `Cmd.sigBind` writes only a `some`, so
this is what a command leaves. -/
def Signature.Extends (sig' sig : Signature) : Prop := ∀ f, sig f ≠ none → sig' f ≠ none

theorem Signature.Extends.refl (sig : Signature) : sig.Extends sig := fun _ h => h

theorem Signature.Extends.trans {s₁ s₂ s₃ : Signature} (h₁ : s₂.Extends s₁)
    (h₂ : s₃.Extends s₂) : s₃.Extends s₁ := fun f h => h₂ f (h₁ f h)

theorem Signature.extends_sigBind (sig : Signature) (c : Cmd) :
    (c.sigBind sig).Extends sig := by
  cases c with
  | decl f d =>
      intro g hg
      rw [Cmd.sigBind]
      by_cases h : g = f
      · subst h; rw [Function.update_self]; simp
      · rw [Function.update_of_ne h]; exact hg
  | _ => exact fun _ h => h

/-- Declaredness is monotone in the signature, which is what carries a clause asked before
the rule to the state the rule fires at. -/
theorem Expr.Declared.mono {e : Expr} {sig sig' : Signature} (hs : sig'.Extends sig)
    (h : e.Declared sig) : e.Declared sig' :=
  fun f hf => (h f hf).imp id (hs f)

theorem Action.Declared.mono {a : Action} {sig sig' : Signature} (hs : sig'.Extends sig)
    (h : a.Declared sig) : a.Declared sig' := by
  cases a with
  | expr e => exact Expr.Declared.mono hs h
  | letBind v e => exact Expr.Declared.mono hs h
  | union e₁ e₂ => exact ⟨Expr.Declared.mono hs h.1, Expr.Declared.mono hs h.2⟩
  | set f args out =>
      exact ⟨hs f h.1, fun e he => Expr.Declared.mono hs (h.2.1 e he),
        fun e he => Expr.Declared.mono hs (h.2.2 e he)⟩

theorem Actions.Declared.mono : ∀ {as : List Action} {sig sig' : Signature},
    sig'.Extends sig → Actions.Declared as sig → Actions.Declared as sig'
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, hs, h => ⟨h.1.mono hs, Actions.Declared.mono hs h.2⟩

/-- An expression's own `Expr.ctors` are among the list's. -/
theorem Expr.mem_ctorsList {es : List Expr} {e : Expr} (he : e ∈ es) {p : FnName × Nat}
    (hp : p ∈ e.ctors) : p ∈ Expr.ctorsList es := by
  induction es with
  | nil => simp at he
  | cons x xs ih =>
      rw [Expr.ctorsList]
      rcases List.mem_cons.mp he with rfl | he'
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (ih he')

/-- **A declared name that is no primitive is a constructor**, on a constructor-only
signature. This is the whole of what `headsDeclared` buys `Expr.eval`. -/
theorem Expr.Evaluable.of_declared {sig : Signature} (hac : sig.AllConstructors) {e : Expr}
    (hp : ∀ f ∈ e.fns, Prim.ofName f = none) (h : e.Declared sig) : e.Evaluable sig := by
  intro f hf
  refine ⟨hp f hf, ?_⟩
  obtain hd := (h f hf).resolve_left (by rw [hp f hf]; simp)
  obtain ⟨d, hdd⟩ := Option.ne_none_iff_exists'.mp hd
  refine Signature.isCtor_of_decl hdd ?_
  have hm := hac f
  rw [Signature.mergeOf, hdd, Option.bind_some] at hm
  exact hm

@[inherit_doc Expr.Evaluable.of_declared]
theorem Action.Builds.of_declared {sig : Signature} (hac : sig.AllConstructors) {a : Action}
    (hp : ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none) (h : a.Declared sig) :
    a.Builds sig := by
  cases a with
  | expr e => exact Expr.Evaluable.of_declared hac (noPrim_fns hp) h
  | letBind v e => exact Expr.Evaluable.of_declared hac (noPrim_fns hp) h
  | union e₁ e₂ =>
      exact ⟨Expr.Evaluable.of_declared hac
          (noPrim_fns fun fk hk => hp fk (List.mem_append_left _ hk)) h.1,
        Expr.Evaluable.of_declared hac
          (noPrim_fns fun fk hk => hp fk (List.mem_append_right _ hk)) h.2⟩
  | set f args out =>
      refine ⟨fun e he => Expr.Evaluable.of_declared hac (fun g hg => ?_) (h.2.1 e he),
        fun e he => Expr.Evaluable.of_declared hac (fun g hg => ?_) (h.2.2 e he)⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg
        exact hp (g, k) (List.mem_cons_of_mem _
          (List.mem_append_left _ (Expr.mem_ctorsList he hk)))
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg
        exact hp (g, k) (List.mem_cons_of_mem _
          (List.mem_append_right _ (Expr.mem_ctorsList he hk)))

@[inherit_doc Expr.Evaluable.of_declared]
theorem Actions.Builds.of_declared {sig : Signature} (hac : sig.AllConstructors) :
    ∀ {as : List Action}, (∀ a ∈ as, ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none) →
      Actions.Declared as sig → Actions.Builds as sig
  | [], _, _ => trivial
  | a :: _, hp, h =>
      ⟨Action.Builds.of_declared hac (hp a List.mem_cons_self) h.1,
        Actions.Builds.of_declared hac (fun b hb => hp b (List.mem_cons_of_mem _ hb)) h.2⟩

end Egglog

namespace Egglog

/-! ### The two domain clauses, as state invariants

`headsDeclared` is threaded along `Cmd.sigBind` and a rule fires from `db.rules`, so what a
firing needs is not a fact about the program's text but the same fact carried on the state:
every rule the state holds has a head that builds at the state's own signature. -/

/-- What one source command must be for a rule it registers to have a runnable head:
`Spec/Scope.lean`'s `Actions.Declared` at the signature standing when the rule is read, and no
applied name a primitive. `EncodeDomain.headsDeclared` and `.noPrim` are exactly the two. -/
def Cmd.HeadRuns (c : Cmd) (sig : Signature) : Prop :=
  c.HeadsDeclared sig ∧ ∀ fk ∈ c.ctors, Prim.ofName fk.1 = none

/-- `Cmd.HeadRuns` along the program, as `Program.HeadsDeclared` is. -/
@[simp] def Program.HeadRuns : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.HeadRuns sig ∧ Program.HeadRuns cs (c.sigBind sig)

/-- **Every rule the state holds has a head that builds.** The invariant a firing spends:
`Actions.Builds` is what `evalLocalActions_isSome_of_builds` asks and it is asked at the
state's own signature, not at the program's. -/
def Database.HeadsBuild (db : Database) : Prop :=
  ∀ r ∈ db.rules, Actions.Builds r.actions db.sig

theorem Database.empty_headsBuild : Database.empty.HeadsBuild := by
  intro r hr; exact absurd hr (by simp [Database.empty])

/-- Evaluability survives a constructor declaration: `Signature.IsCtor.update` is the clause
`Cmd.CtorDecl` buys. -/
theorem Expr.Evaluable.update {sig : Signature} {f : FnName} {d : FnDecl}
    (hd : d.merge = none) {e : Expr} (h : e.Evaluable sig) :
    e.Evaluable (Function.update sig f (some d)) :=
  fun g hg => ⟨(h g hg).1, Signature.IsCtor.update hd (h g hg).2⟩

theorem Action.Builds.update {sig : Signature} {f : FnName} {d : FnDecl}
    (hd : d.merge = none) {a : Action} (h : a.Builds sig) :
    a.Builds (Function.update sig f (some d)) := by
  cases a with
  | expr e => exact Expr.Evaluable.update hd h
  | letBind v e => exact Expr.Evaluable.update hd h
  | union e₁ e₂ => exact ⟨Expr.Evaluable.update hd h.1, Expr.Evaluable.update hd h.2⟩
  | set g args out =>
      exact ⟨fun e he => Expr.Evaluable.update hd (h.1 e he),
        fun e he => Expr.Evaluable.update hd (h.2 e he)⟩

theorem Actions.Builds.update {sig : Signature} {f : FnName} {d : FnDecl} (hd : d.merge = none) :
    ∀ {as : List Action}, Actions.Builds as sig →
      Actions.Builds as (Function.update sig f (some d))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1.update hd, Actions.Builds.update hd h.2⟩

theorem cmdStep_headsBuild {db db' : Database} (hc : db.CtorState) (h : db.HeadsBuild)
    {c : Cmd} (hrun : c.HeadRuns db.sig) (hdecl : c.CtorDecl) (hstep : CmdStep db c db') :
    db'.HeadsBuild := by
  obtain ⟨d, hreach, hcl⟩ := hstep
  cases c with
  | action a =>
      have hv : evalAction db a = some d := hreach
      obtain rfl : db' = d :=
        hcl.eq_of_allConstructors (by rw [evalAction_sig hv]; exact hc.sig)
      intro r hr
      rw [evalAction_sig hv]
      exact h r (by rw [← evalAction_rules hv]; exact hr)
  | rule r =>
      have hv : some { db with rules := insert r db.rules } = some d := hreach
      obtain rfl : d = { db with rules := insert r db.rules } := (Option.some.inj hv).symm
      obtain rfl : db' = { db with rules := insert r db.rules } :=
        hcl.eq_of_allConstructors hc.sig
      intro r' hr'
      rcases Set.mem_insert_iff.mp hr' with rfl | hr''
      · exact Actions.Builds.of_declared hc.sig
          (fun a ha fk hk => hrun.2 fk (by
            rw [Cmd.ctors]
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩)))
          hrun.1
      · exact h r' hr''
  | run R =>
      have hv : some (RunRules R db) = some d := hreach
      obtain rfl : d = RunRules R db := (Option.some.inj hv).symm
      obtain rfl : db' = RunRules R db :=
        hcl.eq_of_allConstructors (by rw [RunRules.sig]; exact hc.sig)
      intro r hr
      rw [RunRules.sig]
      exact h r (by rw [RunRules, Database.sUnion_rules] at hr; exact hr)
  | saturate R =>
      have hsat : SaturateReach R db db' := cmdStep_saturate_iff.mp ⟨d, hreach, hcl⟩
      refine (RunReach.induction (P := fun x => x.CtorState ∧ x.HeadsBuild) ?_ hsat.1
        ⟨hc, h⟩).2
      intro x y hx hxy
      obtain rfl : y = RunRules R x := hxy.eq_of_allConstructors hx.1.sig
      refine ⟨⟨RunRules.wf hx.1.wf, by rw [RunRules.sig]; exact hx.1.sig⟩, fun r hr => ?_⟩
      rw [RunRules.sig]
      exact hx.2 r (by rw [RunRules, Database.sUnion_rules] at hr; exact hr)
  | decl f dc =>
      have hv : some { db with sig := Function.update db.sig f (some dc) } = some d := hreach
      obtain rfl : d = { db with sig := Function.update db.sig f (some dc) } :=
        (Option.some.inj hv).symm
      obtain rfl : db' = { db with sig := Function.update db.sig f (some dc) } :=
        hcl.eq_of_allConstructors (hc.sig.sigBind hdecl)
      exact fun r hr => Actions.Builds.update hdecl (h r hr)

/-- **`Database.HeadsBuild` at every state a run reaches.** -/
theorem programStep_headsBuild {db db' : Database} (hc : db.CtorState) (h : db.HeadsBuild)
    {p : Program} (hrun : Program.HeadRuns p db.sig) (hdecl : p.CtorDecls)
    (hstep : ProgramStep db p db') : db'.HeadsBuild := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hstep _ ih =>
      refine ih (hstep.ctorState hc (hdecl c List.mem_cons_self))
        (cmdStep_headsBuild hc h hrun.1 (hdecl c List.mem_cons_self) hstep) ?_
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))
      rw [hstep.sig]; exact hrun.2

end Egglog

namespace Egglog

/-! ### The invariants, from the domain -/

/-- **`Cmd.NoLits` from `noLitUnion`'s second arm and `noPrim`.** -/
theorem Cmd.NoLits.of_domain {P : Program} (hdom : P.EncodeDomain)
    (hlit : ∀ c ∈ P, c.litFreeB = true) {c : Cmd} (hc : c ∈ P) : c.NoLits := by
  cases c with
  | action a => exact ⟨hlit _ hc, fun fk hk => hdom.noPrim fk (mem_program_ctors hc hk)⟩
  | rule r =>
      intro a ha
      have hb := hlit _ hc
      rw [Cmd.litFreeB, List.all_eq_true] at hb
      refine ⟨hb a ha, fun fk hk => hdom.noPrim fk (mem_program_ctors hc ?_)⟩
      rw [Cmd.ctors]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩)
  | run R => trivial
  | saturate R => trivial
  | decl f d => trivial

/-- **`Database.NoLits` at every state the source run reaches**, under `noLitUnion`'s second
arm. Applied to a *prefix* of the program it is the invariant at the state a firing command
starts from. -/
theorem noLits_of_programStep {P : Program} (hdom : P.EncodeDomain)
    (hlit : ∀ c ∈ P, c.litFreeB = true) {p : Program} (hp : ∀ c ∈ p, c ∈ P)
    {sd : Database} (hstep : ProgramStep Database.empty p sd) : sd.NoLits :=
  programStep_noLits Database.CtorState.empty Database.empty_noLits
    (fun c hc => Cmd.NoLits.of_domain hdom hlit (hp c hc))
    (fun c hc => hdom.ctorsOnly c (hp c hc)) hstep

/-- **`Program.HeadRuns` from `headsDeclared` and `noPrim`.** -/
theorem Program.HeadRuns.of_headsDeclared : ∀ {p : Program} {sig : Signature},
    Program.HeadsDeclared p sig → (∀ c ∈ p, ∀ fk ∈ c.ctors, Prim.ofName fk.1 = none) →
      Program.HeadRuns p sig
  | [], _, _, _ => trivial
  | _ :: _, _, h, hp =>
      ⟨⟨h.1, hp _ List.mem_cons_self⟩,
        Program.HeadRuns.of_headsDeclared h.2 fun c' hc' => hp c' (List.mem_cons_of_mem _ hc')⟩

/-- A prefix of a program whose heads run has heads that run. -/
theorem Program.HeadRuns.of_append : ∀ {p q : Program} {sig : Signature},
    Program.HeadRuns (p ++ q) sig → Program.HeadRuns p sig
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1, Program.HeadRuns.of_append h.2⟩

/-- **`Database.HeadsBuild` at every state the source run reaches**, out of `headsDeclared`,
`noPrim` and `ctorsOnly`. -/
theorem headsBuild_of_programStep {P : Program} (hdom : P.EncodeDomain) {p q : Program}
    (hP : P = p ++ q) {sd : Database} (hstep : ProgramStep Database.empty p sd) :
    sd.HeadsBuild := by
  refine programStep_headsBuild Database.CtorState.empty Database.empty_headsBuild
    (Program.HeadRuns.of_append (q := q) ?_)
    (fun c hc => hdom.ctorsOnly c (by rw [hP]; exact List.mem_append_left _ hc)) hstep
  rw [← hP]
  exact Program.HeadRuns.of_headsDeclared hdom.headsDeclared
    fun c hc fk hk => hdom.noPrim fk (mem_program_ctors hc hk)

/-! ### `hfired`, from the domain

Both shapes, with every hypothesis either the domain's or a fact about the firing. What is
**not** among them is the refuted one — that the key's application is a source term because
the target keyed on it. -/

/-- **`hfired` for `entrySound_headBuild`, from the domain.** -/
theorem mem_terms_of_headBuild_of_domain {P : Program} (hdom : P.EncodeDomain)
    {p q : Program} (hP : P = p ++ q) {sd : Database}
    (hpre : ProgramStep Database.empty p sd)
    {R : RulesetName} {c : Cmd} {sd' : Database} {r : Rule}
    (hfire : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd')
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hmem : Cmd.rule r ∈ P)
    (hsc : r.HeadScoped sd) {τ : Env} (hq : ValidQuerySubst sd r.query τ)
    {f : FnName} {args : List Expr} (ha : Action.expr (.app f args) ∈ r.actions)
    (hlet : ∀ v ∈ (Expr.app f args).vars, v ∉ Actions.letVars r.actions)
    {is : List Term}
    (hval : (Expr.app f args).eval sd.sig (sd.env ++ τ) = some (.app f is)) :
    Term.app f is ∈ sd'.terms := by
  have hstate : sd.CtorState :=
    hpre.ctorState Database.CtorState.empty
      fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc')
  refine mem_terms_of_headBuild hfire hstep hstate.wf hr hrs hsc
    (headsBuild_of_programStep hdom hP hpre r hr) ?_ hq ha hlet hval
  rcases hdom.noLitUnion with huf | hlit
  · exact Or.inl ((Cmd.ruleUnionFreeB_iff r).mp (huf _ hmem))
  · exact Or.inr ⟨(noLits_of_programStep hdom hlit
      (fun c' hc' => by rw [hP]; exact List.mem_append_left _ hc') hpre).terms,
      Cmd.NoLits.of_domain hdom hlit hmem⟩

/-- **`hfired` for `cong_headUnion`, from the domain.** -/
theorem mem_eqs_of_headUnion_of_domain {P : Program} (hdom : P.EncodeDomain)
    {p q : Program} (hP : P = p ++ q) {sd : Database}
    (hpre : ProgramStep Database.empty p sd)
    {R : RulesetName} {c : Cmd} {sd' : Database} {r : Rule}
    (hfire : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd')
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hmem : Cmd.rule r ∈ P)
    (hsc : r.HeadScoped sd) {τ : Env} (hq : ValidQuerySubst sd r.query τ)
    {e₁ e₂ : Expr} (ha : Action.union e₁ e₂ ∈ r.actions)
    (hlet : ∀ v ∈ e₁.vars ∪ e₂.vars, v ∉ Actions.letVars r.actions)
    {t₁ t₂ : Term} (hv₁ : e₁.eval sd.sig (sd.env ++ τ) = some t₁)
    (hv₂ : e₂.eval sd.sig (sd.env ++ τ) = some t₂) : (t₁, t₂) ∈ sd'.eqs := by
  have hstate : sd.CtorState :=
    hpre.ctorState Database.CtorState.empty
      fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc')
  refine mem_eqs_of_headUnion hfire hstep hstate.wf hr hrs hsc
    (headsBuild_of_programStep hdom hP hpre r hr) ?_ hq ha hlet hv₁ hv₂
  rcases hdom.noLitUnion with huf | hlit
  · exact Or.inl ((Cmd.ruleUnionFreeB_iff r).mp (huf _ hmem))
  · exact Or.inr ⟨(noLits_of_programStep hdom hlit
      (fun c' hc' => by rw [hP]; exact List.mem_append_left _ hc') hpre).terms,
      Cmd.NoLits.of_domain hdom hlit hmem⟩

end Egglog
