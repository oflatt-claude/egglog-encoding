import EgglogSemantics.Encoding.Source
import EgglogSemantics.Proofs.Scope

/-! Execution properties of the constructor source fragment. Scoped rule heads use
declared constructors; the domain's union condition prevents literal unions. These
facts are independent of either compiler or proof annotations. -/

namespace Egglog

mutual
/-- **A head an expression applies is one of its `Expr.ctors`.** `Expr.fns` deduplicates and
`Expr.ctors` carries arities; the two name the same heads, which is what carries
`Program.EncodeDomain.noPrim` to a build's `hprim`. -/
theorem Expr.exists_ctor_of_mem_fns : ∀ {e : Expr} {g : FnName}, g ∈ e.fns →
    ∃ k, (g, k) ∈ e.ctors
  | .lit _, _, hg => absurd hg (by simp [Expr.fns])
  | .var _, _, hg => absurd hg (by simp [Expr.fns])
  | .app f args, g, hg => by
      rw [Expr.fns, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨args.length, by rw [Expr.ctors]; exact List.mem_cons_self⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hg
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk⟩

@[inherit_doc Expr.exists_ctor_of_mem_fns]
theorem Expr.exists_ctorList_of_mem_fnsList : ∀ {es : List Expr} {g : FnName},
    g ∈ Expr.fnsList es → ∃ k, (g, k) ∈ Expr.ctorsList es
  | [], _, hg => absurd hg (by simp [Expr.fnsList])
  | e :: es, g, hg => by
      rw [Expr.fnsList] at hg
      rcases List.mem_union_iff.mp hg with hg' | hg'
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg'
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_left _ hk⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hg'
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_right _ hk⟩
end

/-- A `(name, arity)` pair one command applies is one the whole program applies. -/
theorem mem_program_ctors {Q : Program} {c : Cmd} (hc : c ∈ Q) {p : FnName × Nat}
    (hp : p ∈ c.ctors) : p ∈ Q.ctors := by
  rw [Program.ctors, List.mem_dedup, List.mem_flatMap]
  exact ⟨c, hc, hp⟩


/-- Every expression builds constructor values. Union operands may be variables;
the surrounding state supplies their nonliteral property. -/
def Action.Builds : Action → Signature → Prop
  | .expr e, sig => e.Evaluable sig
  | .union e₁ e₂, sig => e₁.Evaluable sig ∧ e₂.Evaluable sig

@[simp] def Actions.Builds : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Builds sig ∧ Actions.Builds as sig

/-- **Evaluability follows the signature up.** `Expr.Evaluable` reads `Signature.IsCtor` and
nothing else, so a target signature declaring every constructor the source's does carries the
source head's own condition across — which is what `Egglog.UnionsFire`'s signature clause is
spent on. -/
theorem Expr.Evaluable.mono_sig {sig sig' : Signature}
    (hsub : ∀ f, sig.IsCtor f → sig'.IsCtor f) {e : Expr} (h : e.Evaluable sig) :
    e.Evaluable sig' := fun f hf => ⟨(h f hf).1, hsub f (h f hf).2⟩

@[inherit_doc Expr.Evaluable.mono_sig]
theorem Action.Builds.mono_sig {sig sig' : Signature}
    (hsub : ∀ f, sig.IsCtor f → sig'.IsCtor f) {a : Action} (h : a.Builds sig) :
    a.Builds sig' := by
  cases a with
  | expr e => exact Expr.Evaluable.mono_sig hsub h
  | union e₁ e₂ =>
      exact ⟨Expr.Evaluable.mono_sig hsub h.1, Expr.Evaluable.mono_sig hsub h.2⟩

@[inherit_doc Expr.Evaluable.mono_sig]
theorem Actions.Builds.mono_sig {sig sig' : Signature}
    (hsub : ∀ f, sig.IsCtor f → sig'.IsCtor f) :
    ∀ {as : List Action}, Actions.Builds as sig → Actions.Builds as sig'
  | [], _ => trivial
  | _ :: _, h => ⟨Action.Builds.mono_sig hsub h.1, Actions.Builds.mono_sig hsub h.2⟩


/-! ##### Literal-free terms and states -/

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

/-! ##### Evaluation of a literal-free expression builds a literal-free term -/

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

/-! ##### The primitive condition, at the applied names -/

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

/-! ##### One action keeps the state literal-free -/

theorem Database.LitFree.lookup {db : Database} (hw : db.WF) (h : db.LitFree) :
    ∀ v t, Env.lookup v db.env = some t → Term.LitFree t := fun v t hv =>
  h.term hw (hw.envInTerms (v, t) (Env.mem_of_lookup hv))

/-- **A literal-free action keeps the state literal-free.** Every writer is an `addTerm` or
an `addEq` of a value `Expr.eval_litFree` covers. -/
theorem Expr.evalAtom_litFree {sig : Signature} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t)
    (e : Expr) {t : Term} (hl : e.litFreeB = true)
    (hf : ∀ f ∈ e.fns, Prim.ofName f = none) (he : e.evalAtom sig σ = some t) :
    Term.LitFree t := by
  cases e with
  | lit _ => simp [Expr.litFreeB] at hl
  | var v => exact hσ v t he
  | app f args =>
    obtain ⟨ts, hts, rfl⟩ := Expr.evalAtom_app_inv (hf f (by simp [Expr.fns])) he
    exact Term.litFree_app.mpr (Expr.evalList_litFree hσ args hl
      (fun g hg => hf g (by simp [Expr.fns, hg])) hts)

theorem evalAction_litFree {db db' : Database} (hw : db.WF) (h : db.LitFree)
    {a : Action} (hl : a.litFreeB = true) (hp : ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none)
    (hv : evalAction db a = some db') : db'.LitFree := by
  have hlk := h.lookup hw
  rcases evalAction_eq_some hv with ⟨e, t, rfl, he, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, he₁, he₂, -, rfl⟩
  · have ht : Term.LitFree t :=
      Expr.evalAtom_litFree hlk e hl (noPrim_fns hp) he
    intro s hs
    rw [Database.addTerm_terms] at hs
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
  have hlf : ({ db with env := σ ++ db.env } : Database).LitFree := by
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

/-! ##### One command and one run keep it -/

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
      have hv : some { db with rules := insert r db.rules } = some d :=
        hreach
      obtain rfl : d = { db with rules := insert r db.rules } :=
        (Option.some.inj hv).symm
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
    ∃ db', evalAction db a = some db' ∧ Γ.Models db'.env := by
  cases a with
  | expr e =>
      obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm hsc.2 hb
      exact ⟨db.addTerm t, by simp [evalAction, Expr.evalAtom_of_eval ht], hm⟩
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

/-- **The block does not get stuck.** The fold, with `Actions.UnionRunnable` as the
invariant: the union-free arm shrinks with the list, and the literal-free arm is carried by
`evalAction_litFree`. -/
theorem evalActions_isSome_of_builds {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    (hw : db.WF) {as : List Action} (hsc : Actions.Scoped as Γ)
    (hb : Actions.Builds as db.sig) (hr : Actions.UnionRunnable as db) :
    ∃ db', evalActions db as = some db' ∧ Γ.Models db'.env := by
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
    ∃ d, evalActions { db with env := σ ++ db.env } r.actions = some d ∧
      evalLocalActions db r.actions σ = some { d with env := db.env, rules := db.rules } := by
  obtain ⟨d, hd, -⟩ := evalActions_isSome_of_builds
    (db := { db with env := σ ++ db.env }) (Query.bind_models hm hq)
    (hw.appendEnv hq.mem_terms) hsc hb
    (by rcases hr with huf | ⟨hlf, hnl⟩
        · exact Or.inl huf
        · exact Or.inr ⟨fun t ht => hlf t (Database.terms_setEnv ▸ ht), hnl⟩)
  exact ⟨d, hd, by simp [evalLocalActions, hd]⟩


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
  | union e₁ e₂ =>
      exact ⟨Expr.Evaluable.of_declared hac
          (noPrim_fns fun fk hk => hp fk (List.mem_append_left _ hk)) h.1,
        Expr.Evaluable.of_declared hac
          (noPrim_fns fun fk hk => hp fk (List.mem_append_right _ hk)) h.2⟩

@[inherit_doc Expr.Evaluable.of_declared]
theorem Actions.Builds.of_declared {sig : Signature} (hac : sig.AllConstructors) :
    ∀ {as : List Action}, (∀ a ∈ as, ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none) →
      Actions.Declared as sig → Actions.Builds as sig
  | [], _, _ => trivial
  | a :: _, hp, h =>
      ⟨Action.Builds.of_declared hac (hp a List.mem_cons_self) h.1,
        Actions.Builds.of_declared hac (fun b hb => hp b (List.mem_cons_of_mem _ hb)) h.2⟩

/-! ##### The two domain clauses, as state invariants

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
  | union e₁ e₂ => exact ⟨Expr.Evaluable.update hd h.1, Expr.Evaluable.update hd h.2⟩

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
      have hv : some { db with rules := insert r db.rules } = some d :=
        hreach
      obtain rfl : d = { db with rules := insert r db.rules } :=
        (Option.some.inj hv).symm
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

/-! ##### The invariants, from the domain -/

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


/-- `Expr.Scoped` in the scope. -/
theorem Expr.Scoped.mono {e : Expr} {Γ Γ' : Scope} (hsub : ∀ v ∈ Γ, v ∈ Γ')
    (h : e.Scoped Γ) : e.Scoped Γ' := fun v hv => hsub v (h v hv)

@[inherit_doc Expr.Scoped.mono]
theorem Action.Scoped.mono {a : Action} {Γ Γ' : Scope} (hsub : ∀ v ∈ Γ, v ∈ Γ')
    (h : a.Scoped Γ) : a.Scoped Γ' := by
  cases a with
  | expr e => exact ⟨h.1, Expr.Scoped.mono hsub h.2⟩
  | union e₁ e₂ => exact ⟨Expr.Scoped.mono hsub h.1, Expr.Scoped.mono hsub h.2⟩

@[inherit_doc Expr.Scoped.mono]
theorem Actions.Scoped.mono : ∀ (as : List Action) {Γ Γ' : Scope}, (∀ v ∈ Γ, v ∈ Γ') →
    Actions.Scoped as Γ → Actions.Scoped as Γ' := by
  intro as
  induction as with
  | nil => intro _ _ _ _; trivial
  | cons a as ih =>
    intro Γ Γ' hsub h
    exact ⟨Action.Scoped.mono hsub h.1, ih hsub h.2⟩


/-- An environment models its own domain. -/
theorem Scope.Models.dom (σ : Env) : Scope.Models (Env.dom σ) σ := fun _ => Iff.rfl

end Egglog
