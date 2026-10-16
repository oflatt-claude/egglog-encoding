import EgglogSemantics.Proofs.Step

/-! Well-formedness and declared widths through mathematical execution. -/

namespace Egglog

/-- `env` and `rules` are invisible to `WF`, as they are to `Cong`. -/
theorem Database.WF.setEnvRules {db : Database} (hw : db.WF) {σ : Env} {R : Set Rule}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) :
    ({ db with env := σ, rules := R } : Database).WF := by
  refine ⟨fun b hb => ?_, hw.litsIsolated⟩
  rw [Database.terms_setEnvRules]; exact hσ b hb

def Action.SetWidthOk : Action → Signature → Prop
  | _, _ => True

@[simp] def Actions.SetWidthOk : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.SetWidthOk sig ∧ Actions.SetWidthOk as sig

/-- The automatic structural write predicate used by the refinement interfaces. -/
def Action.WriteLegal (a : Action) (sig : Signature) : Prop :=
  a.SetWidthOk sig

@[simp] def Actions.WriteLegal (as : List Action) (sig : Signature) : Prop :=
  Actions.SetWidthOk as sig

@[simp] def Cmd.WriteLegal : Cmd → Signature → Prop
  | .action a, sig => a.WriteLegal sig
  | .rule r, sig => Actions.WriteLegal r.actions sig
  | .check _, _ => True
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl _ _, _ => True

theorem Actions.WriteLegal.head {a : Action} {as : List Action} {sig : Signature}
    (h : Actions.WriteLegal (a :: as) sig) : a.WriteLegal sig := h.1

theorem Actions.WriteLegal.tail {a : Action} {as : List Action} {sig : Signature}
    (h : Actions.WriteLegal (a :: as) sig) : Actions.WriteLegal as sig := h.2

/-- Merge results have the declared tuple width. -/
def Signature.MergesLegal (sig : Signature) : Prop :=
  ∀ g dc oldVars newVars body res, sig g = some dc → dc.merge = some (MergeSpec.merge
    oldVars newVars body res) →
    Actions.WriteLegal body sig ∧ res.length = dc.outArity

theorem Term.IsValue.not_mentions_of_fresh {sig : Signature} {f : FnName}
    (hf : sig f = none) {t : Term} (ht : t.IsValue sig) : ¬ t.Mentions f := by
  induction t using Term.recTerm with
  | lit l => exact Term.not_mentions_lit
  | app g args ih =>
    obtain ⟨hg, ha⟩ := Term.isValue_app_iff.mp ht
    intro hm
    rcases Term.mentions_app hm with rfl | ⟨a, ham, hma⟩
    · obtain ⟨d, hd, _⟩ := hg
      simp [hf] at hd
    · exact ih a ham (ha a ham) hma

theorem Database.StoreOk.avoids {db : Database} (hs : db.StoreOk) {f : FnName}
    (hf : db.sig f = none) : db.Avoids f := by
  refine ⟨?_, fun b hb => (hs.envValues b hb).not_mentions_of_fresh hf⟩
  intro t ht
  rcases hs.term ht with hv | ⟨row, hr, rfl⟩
  · exact hv.not_mentions_of_fresh hf
  · intro hm
    rcases Term.mentions_app hm with he | ⟨a, ha, hm⟩
    · obtain ⟨d, hd, _⟩ := hr
      simp [he, hf] at hd
    · exact (hr.column_values a ha).not_mentions_of_fresh hf hm

theorem Database.StoreOk.decl {db : Database} (hs : db.StoreOk) {f : FnName}
    {dc : FnDecl} (hf : db.sig f = none) :
    ({ db with sig := Function.update db.sig f (some dc) } : Database).StoreOk := by
  let sig' := Function.update db.sig f (some dc)
  have hag : ∀ g, g ≠ f → db.sig g = sig' g :=
    fun g hg => (Function.update_of_ne hg _ _).symm
  have hav := hs.avoids hf
  have hv : ∀ t : Term, t.IsValue db.sig → t.IsValue sig' := by
    intro t ht
    change t.isValue sig' = true
    rw [← Term.isValue_update hag (ht.not_mentions_of_fresh hf)]
    exact ht
  have hrows := Database.entries_update_of_avoids hag hav
  refine ⟨?_, ?_, ?_, fun b hb => hv b.2 (hs.envValues b hb)⟩
  · intro row hr
    obtain ⟨decl, hd, hm, _⟩ := hr.1
    exact ⟨decl, hd, hm⟩
  · intro row hr t ht
    simpa only [Database.terms_setSig] using hs.columns row (hrows ▸ hr) t ht
  · intro p hp
    rcases hs.typed p hp with hp' | ⟨row, hr, rfl⟩
    · exact Or.inl ⟨hv _ hp'.1, hv _ hp'.2⟩
    · exact Or.inr ⟨row, (Entry.valid_update_iff hag
        (hav.terms row.atom (Cong.assert hp))).mp hr, rfl⟩

theorem evalLocalActions_storeOk {db d : Database} (hs : db.StoreOk)
    {as : List Action} {σ : Env} (hv : ∀ b ∈ σ, b.2.IsValue db.sig)
    (h : evalLocalActions db as σ = some d) : d.StoreOk := by
  obtain ⟨post, hp, rfl⟩ := evalLocalActions_eq_some h
  have hstart := hs.setEnv (σ := σ ++ db.env) (fun b hb =>
    (List.mem_append.mp hb).elim (hv b) (hs.envValues b))
  exact (evalActions_storeOk hstart hp).congr rfl rfl (by
    simpa only [evalActions_sig hp] using hs.envValues)

theorem RuleResults.storeOk {db d : Database} (hs : db.StoreOk) {r : Rule}
    (h : d ∈ RuleResults db r) : d.StoreOk := by
  obtain ⟨σ, hσ, he⟩ := h
  exact evalLocalActions_storeOk hs (fun b hb => (hσ.mem_values b hb).2) he

theorem RunRules.storeOk {R : RulesetName} {db : Database} (hs : db.StoreOk) :
    (RunRules R db).StoreOk := by
  have sigs : ∀ d ∈ {d | ∃ r ∈ db.rules, r.ruleset = R ∧ d ∈ RuleResults db r},
      d.sig = db.sig := by
    rintro d ⟨r, _, _, hd⟩
    exact RuleResults.sig hd
  refine ⟨?_, ?_, ?_, hs.envValues⟩
  · intro row hr
    obtain ⟨decl, hd, hm, _⟩ := hr.1
    exact ⟨decl, hd, hm⟩
  · intro row hr t ht
    rw [RunRules, Database.sUnion_entries sigs] at hr
    rcases hr with hr | hr
    · exact (Database.Contained.sUnion db _).terms (hs.columns row hr t ht)
    · obtain ⟨d, hd, hr⟩ := Set.mem_iUnion₂.mp hr
      obtain ⟨r, hrmem, hR, hdr⟩ := hd
      have hcol := (RuleResults.storeOk hs hdr).columns row hr t ht
      rw [RunRules, Database.sUnion_terms]
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨d, ⟨r, hrmem, hR, hdr⟩, hcol⟩)
  · intro p hp
    rcases hp with hp | hp
    · exact hs.typed p hp
    · obtain ⟨d, hd, hp⟩ := Set.mem_iUnion₂.mp hp
      obtain ⟨r, hrmem, hR, hdr⟩ := hd
      have ht := (RuleResults.storeOk hs hdr).typed p hp
      simpa only [RuleResults.sig hdr, RunRules.sig] using ht

theorem MergeValues.wf {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) (hw : db.WF)
    (ho : ∀ t ∈ old, t ∈ db.terms) (hn : ∀ t ∈ new, t ∈ db.terms) : d.WF := by
  cases h with
  | unchanged => exact hw
  | @changed post vs ovs nvs body res _ _ hb _ =>
    have hstart := hw.setEnv (σ := mergeEnv ovs nvs old new)
      (fun b hb => (mem_mergeEnv hb).elim (ho b.2) (hn b.2))
    exact (evalActions_wf hstart hb).setEnvRules (fun b hmem =>
      (evalActions_contained hb).terms (by
        simpa only [Database.terms_setEnv] using hw.envInTerms b hmem))

theorem MergeStep.wf {d₁ d₂ : Database} (hw : d₁.WF) (hs : d₁.StoreOk)
    (h : MergeStep d₁ d₂) : d₂.WF := by
  cases h with
  | @collide d old new decl vs hold hnew _ _ _ _ hv =>
    have hs0 := (hs.eraseEntry old hold.1).eraseEntry new hnew.1
    have hw0 := (hw.eraseEntry hs old hold.1).eraseEntry
      (hs.eraseEntry old hold.1) new hnew.1
    have keep : ∀ t, t.IsValue d₁.sig → t ∈ d₁.terms →
        t ∈ ((d₁.eraseEntry old).eraseEntry new).terms := fun t ht hm =>
      Database.mem_terms_eraseEntry_of_value hnew.1 ht
        (Database.mem_terms_eraseEntry_of_value hold.1 ht hm)
    apply Database.WF.putEntry
    exact hv.wf hw0
      (fun t ht => keep t (hold.1.output_values t ht)
        (hs.columns old hold t (List.mem_append_right _ ht)))
      (fun t ht => keep t (hnew.1.output_values t ht)
        (hs.columns new hnew t (List.mem_append_right _ ht)))

theorem MergeClosure.wf {d₁ d₂ : Database} (hw : d₁.WF) (hs : d₁.StoreOk)
    (hmw : d₁.sig.MergesWidthOk) (h : MergeClosure d₁ d₂) : d₂.WF := by
  induction h with
  | refl => exact hw
  | tail hc hstep ih => exact MergeStep.wf ih (MergeClosure.storeOk hc hs hmw) hstep

theorem RunStep.storeOk {R : RulesetName} {db db' : Database} (hs : db.StoreOk)
    (hmw : db.sig.MergesWidthOk) (h : RunStep R db db') : db'.StoreOk :=
  h.1.storeOk (RunRules.storeOk hs) hmw

theorem RunStep.wf {R : RulesetName} {db db' : Database} (hw : db.WF)
    (hs : db.StoreOk) (hmw : db.sig.MergesWidthOk) (h : RunStep R db db') : db'.WF :=
  MergeClosure.wf (RunRules.wf hw) (RunRules.storeOk hs) hmw h.1

theorem RunReach.envRules {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : d.env = db.env ∧ d.rules = db.rules := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hs ih =>
    have hm := MergeClosure.envRules hs.1
    exact ⟨hm.1.trans ih.1, hm.2.trans ih.2⟩

theorem RunReach.storeOk {R : RulesetName} {db d : Database} (hs : db.StoreOk)
    (hmw : db.sig.MergesWidthOk) (h : Relation.ReflTransGen (RunStep R) db d) : d.StoreOk := by
  induction h with
  | refl => exact hs
  | tail hc hr ih => exact hr.storeOk ih (by rw [RunReach.sig hc]; exact hmw)

theorem RunReach.wf {R : RulesetName} {db d : Database} (hw : db.WF)
    (hs : db.StoreOk) (hmw : db.sig.MergesWidthOk)
    (h : Relation.ReflTransGen (RunStep R) db d) : d.WF := by
  induction h with
  | refl => exact hw
  | tail hc hr ih =>
    exact hr.wf ih (RunReach.storeOk hs hmw hc)
      (by rw [RunReach.sig hc]; exact hmw)

theorem cmdReach_storeOk {db d : Database} (hs : db.StoreOk) {c : Cmd}
    (hf : c.DeclFresh db.sig) (hmw : (c.sigBind db.sig).MergesWidthOk)
    (h : cmdReach db c d) : d.StoreOk := by
  cases c with
  | action a => exact evalAction_storeOk hs h
  | rule r => subst d; exact hs.congr rfl rfl hs.envValues
  | run R => subst d; exact RunRules.storeOk hs
  | saturate R => exact RunReach.storeOk hs hmw (show SaturateReach R db d from h).reach
  | decl f dc => subst d; exact hs.decl hf
  | check q => rw [h.2]; exact hs

theorem cmdReach_wf' {db d : Database} (hw : db.WF) (hs : db.StoreOk) {c : Cmd}
    (hmw : (c.sigBind db.sig).MergesWidthOk) (h : cmdReach db c d) : d.WF := by
  cases c with
  | saturate R => exact RunReach.wf hw hs hmw (show SaturateReach R db d from h).reach
  | _ => exact cmdReach_wf hw (by trivial) h

theorem CmdStep.storeOk {db db' : Database} (hs : db.StoreOk) {c : Cmd}
    (hf : c.DeclFresh db.sig) (hmw : (c.sigBind db.sig).MergesWidthOk)
    (h : CmdStep db c db') : db'.StoreOk := by
  obtain ⟨d, hr, hc⟩ := h.reach
  exact hc.storeOk (cmdReach_storeOk hs hf hmw hr) (by rw [cmdReach_sig hr]; exact hmw)

theorem CmdStep.wf {db db' : Database} (hw : db.WF) (hs : db.StoreOk) {c : Cmd}
    (hf : c.DeclFresh db.sig) (hmw : (c.sigBind db.sig).MergesWidthOk)
    (h : CmdStep db c db') : db'.WF := by
  obtain ⟨d, hr, hc⟩ := h.reach
  exact hc.wf (cmdReach_wf' hw hs hmw hr) (cmdReach_storeOk hs hf hmw hr)
    (by rw [cmdReach_sig hr]; exact hmw)

mutual

theorem Expr.WidthOk.agree {sig sig' : Signature} (e : Expr)
    (h : ∀ f ∈ e.fns, sig f = sig' f) (hw : e.WidthOk sig) : e.WidthOk sig' := by
  match e with
  | .lit _ | .var _ => trivial
  | .app f args =>
    refine ⟨?_, Expr.WidthOkList.agree args (fun g hg => h g (by simp [Expr.fns, hg])) hw.2⟩
    intro d hd
    exact hw.1 d ((h f (by simp [Expr.fns])).trans hd)
  | .min a b => exact ⟨Expr.WidthOk.agree a (fun f hf => h f (by simp [hf])) hw.1,
      Expr.WidthOk.agree b (fun f hf => h f (by simp [hf])) hw.2⟩

theorem Expr.WidthOkList.agree {sig sig' : Signature} (es : List Expr)
    (h : ∀ f ∈ Expr.fnsList es, sig f = sig' f) (hw : Expr.WidthOkList es sig) :
    Expr.WidthOkList es sig' := by
  match es with
  | [] => trivial
  | e :: es => exact ⟨Expr.WidthOk.agree e (fun f hf => h f (by simp [Expr.fnsList, hf])) hw.1,
      Expr.WidthOkList.agree es (fun f hf => h f (by simp [Expr.fnsList, hf])) hw.2⟩

end

theorem Expr.AtomWidthOk.agree {sig sig' : Signature} (e : Expr)
    (h : ∀ f ∈ e.fns, sig f = sig' f) (hw : e.AtomWidthOk sig) : e.AtomWidthOk sig' := by
  cases e with
  | lit _ | var _ => trivial
  | min a b => exact Expr.WidthOk.agree (.min a b) h hw
  | app f args =>
    refine ⟨?_, Expr.WidthOkList.agree args (fun g hg => h g (by simp [Expr.fns, hg])) hw.2⟩
    intro d hd
    exact hw.1 d ((h f (by simp [Expr.fns])).trans hd)

theorem Expr.Declared.agrees_update {sig : Signature} {f : FnName} {dc : FnDecl}
    (hf : sig f = none) {e : Expr} (hd : e.Declared sig) :
    ∀ g ∈ e.fns, sig g = Function.update sig f (some dc) g := by
  intro g hg
  have hgf : g ≠ f := by
    intro he
    exact hd g hg (by rw [he]; exact hf)
  exact (Function.update_of_ne hgf _ _).symm

theorem Action.WidthOk.update_of_fresh {sig : Signature} {f : FnName} {dc : FnDecl}
    (hf : sig f = none) {a : Action} (hd : a.Declared sig) (hw : a.WidthOk sig) :
    a.WidthOk (Function.update sig f (some dc)) := by
  cases a with
  | expr e => exact Expr.AtomWidthOk.agree e (hd.agrees_update hf) hw
  | union a b => exact ⟨Expr.WidthOk.agree a (hd.1.agrees_update hf) hw.1,
      Expr.WidthOk.agree b (hd.2.agrees_update hf) hw.2⟩

theorem Actions.WidthOk.update_of_fresh {sig : Signature} {f : FnName} {dc : FnDecl}
    (hf : sig f = none) {as : List Action} (hd : Actions.Declared as sig)
    (hw : Actions.WidthOk as sig) : Actions.WidthOk as (Function.update sig f (some dc)) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨hw.1.update_of_fresh hf hd.1, ih hd.2 hw.2⟩

theorem MergeSpec.WidthOk.update_of_fresh {sig : Signature} {f : FnName} {dc : FnDecl}
    (hf : sig f = none) {ms : MergeSpec} {n : Nat} (hd : ms.Declared sig)
    (hw : ms.WidthOk n sig) : ms.WidthOk n (Function.update sig f (some dc)) := by
  cases ms with
  | merge ovs nvs body res =>
    refine ⟨hw.1, hw.2.1.update_of_fresh hf hd.1, ?_⟩
    apply Expr.WidthOkList.agree res ?_ hw.2.2
    intro g hg
    have hdecl : sig g ≠ none := by
      obtain ⟨e, he, hg⟩ := Expr.mem_fnsList hg
      exact hd.2 e he g hg
    have hgf : g ≠ f := by
      intro he
      exact hdecl (by rw [he]; exact hf)
    exact (Function.update_of_ne hgf _ _).symm

theorem Signature.MergesWidthOk.sigBind {sig : Signature} {c : Cmd}
    (hmw : sig.MergesWidthOk) (hmd : SigMergeDeclared sig)
    (hw : c.WidthOk sig) (hf : c.DeclFresh sig) : (c.sigBind sig).MergesWidthOk := by
  cases c with
  | decl f dc =>
    intro g d ms hg hm
    by_cases he : g = f
    · subst g
      rw [Cmd.sigBind, Function.update_self] at hg
      obtain rfl := Option.some.inj hg
      exact hw ms hm
    · rw [Cmd.sigBind, Function.update_of_ne he] at hg
      exact (hmw g d ms hg hm).update_of_fresh hf (hmd g d ms hg hm)
  | _ => exact hmw

/-- Static width and fresh-declaration checks preserve the runtime invariants. -/
theorem ProgramStep.wf_storeOk {db d : Database} {p : Program} (h : ProgramStep db p d)
    (hw : db.WF) (hs : db.StoreOk) (hmw : db.sig.MergesWidthOk)
    (hmd : SigMergeDeclared db.sig) (hpw : p.WidthOk db.sig)
    (hpf : p.DeclsFresh db.sig) (hpd : p.MergeDeclared db.sig) : d.WF ∧ d.StoreOk := by
  induction h with
  | nil => exact ⟨hw, hs⟩
  | @cons db mid d c cs hc hrest ih =>
    have hmw' := hmw.sigBind hmd hpw.1 hpf.1
    exact ih (CmdStep.wf hw hs hpf.1 hmw' hc) (CmdStep.storeOk hs hpf.1 hmw' hc)
      (by rw [hc.sig]; exact hmw') (cmdStep_sigMergeDeclared hmd hpd.1 hc)
      (by rw [hc.sig]; exact hpw.2) (by rw [hc.sig]; exact hpf.2)
      (by rw [hc.sig]; exact hpd.2)

theorem ProgramStep.wf {db d : Database} {p : Program} (h : ProgramStep db p d)
    (hw : db.WF) (hs : db.StoreOk) (hmw : db.sig.MergesWidthOk)
    (hmd : SigMergeDeclared db.sig) (hpw : p.WidthOk db.sig)
    (hpf : p.DeclsFresh db.sig) (hpd : p.MergeDeclared db.sig) : d.WF :=
  (h.wf_storeOk hw hs hmw hmd hpw hpf hpd).1

theorem ProgramStep.storeOk {db d : Database} {p : Program} (h : ProgramStep db p d)
    (hw : db.WF) (hs : db.StoreOk) (hmw : db.sig.MergesWidthOk)
    (hmd : SigMergeDeclared db.sig) (hpw : p.WidthOk db.sig)
    (hpf : p.DeclsFresh db.sig) (hpd : p.MergeDeclared db.sig) : d.StoreOk :=
  (h.wf_storeOk hw hs hmw hmd hpw hpf hpd).2

theorem reachable_wf_storeOk {p : Program} {d : Database}
    (hw : p.WidthOk Database.empty.sig) (hf : p.DeclsFresh Database.empty.sig)
    (hd : p.MergeDeclared Database.empty.sig) (h : ProgramStep Database.empty p d) :
    d.WF ∧ d.StoreOk := by
  exact h.wf_storeOk Database.WF.empty Database.StoreOk.empty
    (by simp [Signature.MergesWidthOk, Database.empty])
    (by simp [SigMergeDeclared, Database.empty]) hw hf hd

/-! ### `DeclaredTerms` over the step relations

Every application a reachable state holds is a declared function's entry, `entryWidth`
children wide. `Proofs/Eval.lean` carries the action half; what is left is the merge phase,
the rule phase, and a declaration.

Two front-end checks pay for it: `Program.WidthOk` for the terms a command builds and
`Program.DeclsFresh` for the signature a `.decl` writes. Two conditions no signature-level
check can deliver are carried by `Database.RunLegal`. -/

theorem MergeValues.declaredTerms {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) (hw : db.WF) (hdt : db.DeclaredTerms)
    (ho : ∀ t ∈ old, t ∈ db.terms) (hn : ∀ t ∈ new, t ∈ db.terms)
    (hspec : ∀ ms, decl.merge = some ms → ms.WidthOk decl.outArity db.sig) :
    d.DeclaredTerms ∧ ∀ t ∈ vs, Term.DeclaredTerm d.sig t := by
  cases h with
  | unchanged => exact ⟨hdt, fun t ht => Database.declaredTerm_of_mem hw hdt (ho t ht)⟩
  | @changed post vs ovs nvs body res hm _ hb hr =>
    have hw0 := hw.setEnv (σ := mergeEnv ovs nvs old new)
      (fun b hb => (mem_mergeEnv hb).elim (ho b.2) (hn b.2))
    have hdt0 : ({ db with env := mergeEnv ovs nvs old new } : Database).DeclaredTerms := by
      simpa only [Database.DeclaredTerms, Database.terms_setEnv] using hdt
    have hspec := hspec _ hm
    have hpost := evalActions_declaredTerms hw0 hdt0 hspec.2.1 hb
    refine ⟨by simpa only [Database.DeclaredTerms, Database.terms_setEnvRules] using hpost, ?_⟩
    exact Expr.evalList_declaredTerm
      (Database.env_declaredTerm (evalActions_wf hw0 hb) hpost)
      (by rw [evalActions_sig hb]; exact hspec.2.2) hr

theorem mergeStep_declaredTerms {db db' : Database} (hwf : db.WF) (hs : db.StoreOk)
    (hdt : db.DeclaredTerms) (_hml : db.sig.MergesLegal)
    (hmw : db.sig.MergesWidthOk) (h : MergeStep db db') : db'.DeclaredTerms := by
  cases h with
  | @collide d old new decl vs hold hnew _ _ hd _ hv =>
    have hc0 : ((db.eraseEntry old).eraseEntry new).terms ⊆ db.terms :=
      (Database.terms_eraseEntry_subset (row := new) (fun t ht =>
        Database.mem_terms_eraseEntry_of_value hold.1 (hnew.1.column_values t ht)
          (hs.columns new hnew t ht))).trans
        (Database.terms_eraseEntry_subset (hs.columns old hold))
    have hw0 := (hwf.eraseEntry hs old hold.1).eraseEntry
      (hs.eraseEntry old hold.1) new hnew.1
    have hdt0 : ((db.eraseEntry old).eraseEntry new).DeclaredTerms :=
      fun f args ht => hdt f args (hc0 ht)
    have keep : ∀ t, t.IsValue db.sig → t ∈ db.terms →
        t ∈ ((db.eraseEntry old).eraseEntry new).terms := fun t ht hm =>
      Database.mem_terms_eraseEntry_of_value hnew.1 ht
        (Database.mem_terms_eraseEntry_of_value hold.1 ht hm)
    obtain ⟨hddt, hvals⟩ := hv.declaredTerms hw0 hdt0
      (fun t ht => keep t (hold.1.output_values t ht)
        (hs.columns old hold t (List.mem_append_right _ ht)))
      (fun t ht => keep t (hnew.1.output_values t ht)
        (hs.columns new hnew t (List.mem_append_right _ ht)))
      (hmw old.name decl · hd)
    have hlen : vs.length = old.value.length := by
      obtain ⟨dc, hdc, _, _, hlen, _⟩ := hold.1
      have he : dc = decl := Option.some.inj (hdc.symm.trans hd)
      subst dc
      cases hv with
      | unchanged => rfl
      | changed hm _ _ hr =>
        exact (Expr.evalList_length hr).trans ((hmw _ _ _ hd hm).1.trans hlen.symm)
    have hrow : (Entry.mk old.name old.key vs).Valid d.sig := by
      rw [hv.sig]
      exact hold.1.with_value hlen (by
        simpa only [hv.sig, Database.eraseEntry_sig] using hv.output_values hold.1.output_values)
    apply Database.declaredTerms_putEntry hddt hrow
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · rw [hv.sig]
      exact Database.declaredTerm_of_mem hwf hdt (hs.columns old hold t (List.mem_append_left _ ht))
    · exact hvals t ht

theorem mergeClosure_declaredTerms {db db' : Database} (hwf : db.WF) (hs : db.StoreOk)
    (hdt : db.DeclaredTerms) (hml : db.sig.MergesLegal) (hmw : db.sig.MergesWidthOk)
    (h : MergeClosure db db') : db'.DeclaredTerms := by
  induction h with
  | refl => exact hdt
  | @tail x y hcl hstep ih =>
    have hsx : x.sig = db.sig := MergeClosure.sig hcl
    exact mergeStep_declaredTerms (MergeClosure.wf hwf hs hmw hcl)
      (MergeClosure.storeOk hcl hs hmw) ih (by rw [hsx]; exact hml) (by rw [hsx]; exact hmw) hstep

/-- The rules the state holds obey the check `evalLocalActions_declaredTerms` asks of an
action block. `RunRules` fires the rules in `db.rules`, which no signature-level check
reaches. -/
def Database.RulesOk (db : Database) : Prop :=
  ∀ r ∈ db.rules, Actions.WidthOk r.actions db.sig

theorem runRules_declaredTerms {R : RulesetName} {db : Database} (hwf : db.WF)
    (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) : (RunRules R db).DeclaredTerms := by
  intro g cs hmem
  rw [RunRules, Database.sUnion_terms] at hmem
  rcases hmem with hmem | hmem
  · exact hdt g cs hmem
  · obtain ⟨e, he, hmem⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨r, hrmem, -, σ, hq, hstep⟩ := he
    have hes : e.sig = db.sig := evalLocalActions_sig hstep
    change ∃ x, db.sig g = some x ∧ cs.length = x.entryWidth
    rw [← hes]
    exact evalLocalActions_declaredTerms hwf hdt hq.mem_terms (hr r hrmem) hstep g cs hmem

/-- **A declaration preserves `DeclaredTerms` exactly when it is fresh**, and needs nothing
else. A `DeclaredTerms` state holds no application of an undeclared name, so writing the
signature at a fresh name cannot invalidate a term it already holds. -/
theorem decl_declaredTerms {db : Database} (hdt : db.DeclaredTerms) {f : FnName}
    {dc : FnDecl} (hf : db.sig f = none) :
    ({ db with sig := Function.update db.sig f (some dc) } : Database).DeclaredTerms := by
  intro g cs hmem
  rw [Database.terms_setSig] at hmem
  obtain ⟨d, hd, hlen⟩ := hdt g cs hmem
  have hgf : g ≠ f := by rintro rfl; rw [hf] at hd; exact absurd hd (by simp)
  refine ⟨d, ?_, hlen⟩
  change Function.update db.sig f (some dc) g = some d
  rw [Function.update_of_ne hgf]; exact hd

/-- **A saturating run preserves `DeclaredTerms`.** Each round is `runRules_declaredTerms`
then `mergeClosure_declaredTerms`; what makes the induction go through is that a round moves
neither `sig` nor `rules`, so `Database.RulesOk` and the two signature-level checks hold
verbatim at every intermediate state. -/
theorem runReach_declaredTerms {R : RulesetName} {db d : Database} (hwf : db.WF)
    (hs : db.StoreOk) (hdt : db.DeclaredTerms) (hr : db.RulesOk) (hml : db.sig.MergesLegal)
    (hmw : db.sig.MergesWidthOk) (h : Relation.ReflTransGen (RunStep R) db d) :
    d.DeclaredTerms := by
  induction h with
  | refl => exact hdt
  | @tail x y hcl hstep ih =>
    have hxs := RunReach.sig hcl
    have hxr := (RunReach.envRules hcl).2
    have hxw := RunReach.wf hwf hs hmw hcl
    have hxs0 := RunReach.storeOk hs hmw hcl
    have hro : x.RulesOk := fun r hr' => hxs ▸ hr r (hxr ▸ hr')
    exact mergeClosure_declaredTerms (RunRules.wf hxw) (RunRules.storeOk hxs0)
      (runRules_declaredTerms hxw ih hro)
      (by simpa only [RunRules.sig, hxs] using hml)
      (by simpa only [RunRules.sig, hxs] using hmw) hstep.1

theorem cmdReach_declaredTerms {db d : Database} (hwf : db.WF) (hs : db.StoreOk)
    (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) {c : Cmd} (hw : c.WidthOk db.sig)
    (hfresh : c.DeclFresh db.sig) (hml : (c.sigBind db.sig).MergesLegal)
    (hmw : (c.sigBind db.sig).MergesWidthOk) (h : cmdReach db c d) : d.DeclaredTerms := by
  cases c with
  | action a => exact evalAction_declaredTerms hwf hdt hw h
  | rule r =>
    subst h
    intro g cs hmem
    rw [Database.terms_setRules] at hmem
    exact hdt g cs hmem
  | run R => subst h; exact runRules_declaredTerms hwf hdt hr
  | saturate R =>
    exact runReach_declaredTerms hwf hs hdt hr hml hmw (show SaturateReach R db d from h).reach
  | decl f dc => subst h; exact decl_declaredTerms hdt hfresh
  | check q => rw [h.2]; exact hdt

/-- The two signature-level invariants are read at the signature the command *installs*, as
`Cmd.WidthOk` and `Cmd.MergeDeclared` are: that is the signature the merge phase runs
against. -/
theorem cmdStep_declaredTerms {db d : Database} (hwf : db.WF) (hs : db.StoreOk)
    (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) {c : Cmd} (hw : c.WidthOk db.sig)
    (hfresh : c.DeclFresh db.sig) (hml : (c.sigBind db.sig).MergesLegal)
    (hmw : (c.sigBind db.sig).MergesWidthOk) (h : CmdStep db c d) : d.DeclaredTerms := by
  obtain ⟨x, hx, hcl⟩ := h.reach
  have hxs : x.sig = c.sigBind db.sig := cmdReach_sig hx
  exact mergeClosure_declaredTerms (cmdReach_wf' hwf hs hmw hx)
    (cmdReach_storeOk hs hfresh hmw hx)
    (cmdReach_declaredTerms hwf hs hdt hr hw hfresh hml hmw hx)
    (by rw [hxs]; exact hml) (by rw [hxs]; exact hmw) hcl

/-- What `Program.WidthOk` and `Program.DeclsFresh` cannot say, checked at the state each
command actually runs in — the weakest place to check it, as `FDatabase.ProgramLegal` does.
Two things: the rules the state holds pass the action-block check, and the signature the
command leaves has width-checked `:merge` bodies.
Neither is a condition on the program text — a rule outlives the signature it was added
under, and `Cmd.WidthOk` reaches a `:merge` only at the declaration that installs it. -/
def Database.RunLegal : Database → Program → Prop
  | _, [] => True
  | db, c :: cs =>
      db.RulesOk ∧ Signature.MergesLegal (c.sigBind db.sig) ∧
        Signature.MergesWidthOk (c.sigBind db.sig) ∧
        ∀ d, CmdStep db c d → Database.RunLegal d cs

/-- **A run preserves `DeclaredTerms`.** The two front-end checks thread through the
induction on their own: each is read at the signature the earlier commands leave, which is
the signature the run has reached by `CmdStep.sig`. -/
theorem programStep_declaredTerms {db db' : Database} {p : Program}
    (h : ProgramStep db p db') :
    db.WF → db.StoreOk → db.DeclaredTerms → Program.WidthOk p db.sig →
      Program.DeclsFresh p db.sig → db.RunLegal p → db'.DeclaredTerms := by
  induction h with
  | nil => exact fun _ _ hdt _ _ _ => hdt
  | @cons db x d' c cs hstep _ ih =>
    intro hwf hs hdt hw hfresh hl
    have hxs : x.sig = c.sigBind db.sig := CmdStep.sig hstep
    exact ih (CmdStep.wf hwf hs hfresh.1 hl.2.2.1 hstep)
      (CmdStep.storeOk hs hfresh.1 hl.2.2.1 hstep)
      (cmdStep_declaredTerms hwf hs hdt hl.1 hw.1 hfresh.1 hl.2.1 hl.2.2.1 hstep)
      (by rw [hxs]; exact hw.2) (by rw [hxs]; exact hfresh.2)
      (hl.2.2.2 x hstep)

/-- **Every state a legal run reaches from `Database.empty` is `DeclaredTerms`.** -/
theorem reachable_declaredTerms {p : Program} {db : Database}
    (hw : Program.WidthOk p Database.empty.sig)
    (hfresh : Program.DeclsFresh p Database.empty.sig)
    (hl : Database.empty.RunLegal p) (h : ProgramStep Database.empty p db) :
    db.DeclaredTerms :=
  programStep_declaredTerms h Database.WF.empty Database.StoreOk.empty
    Database.empty_declaredTerms hw hfresh hl

end Egglog
