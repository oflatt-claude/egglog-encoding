import EgglogSemantics.Proofs.Congruence.AbstractMaintenanceDescent

/-! Soundness through actual mathematical rounds and finite rebuilding executions. -/

namespace Egglog.Congruence.Abstract

/-- Structural invariants needed to interpret arbitrary target rule and merge steps. -/
structure Runtime (d : Database) : Prop where
  wf : d.WF
  noUnions : d.NoUnions
  declared : d.DeclaredTerms
  rulesOk : d.RulesOk
  shape : MergeShape d.sig
  uf : d.sig ufName = some (tableDecl 1)

theorem Runtime.merge {d e : Database} (h : Runtime d) (hm : MergeClosure d e) :
    Runtime e where
  wf := MergeClosure.wf h.wf hm
  noUnions := ⟨MergeClosure.diag h.noUnions.sig h.noUnions.diag hm,
    by rw [hm.sig]; exact h.noUnions.sig,
    by rw [hm.envRules.2]; exact h.noUnions.rules⟩
  declared := mergeClosure_declaredTerms h.wf h.declared (mergeShape_mergesLegal h.shape)
    (mergeShape_mergesWidthOk h.shape h.uf) hm
  rulesOk := by
    intro r hr
    rw [hm.sig]
    exact h.rulesOk r (hm.envRules.2 ▸ hr)
  shape := by rw [hm.sig]; exact h.shape
  uf := by rw [hm.sig]; exact h.uf

theorem Runtime.runRules {d : Database} (h : Runtime d) (R : RulesetName) :
    Runtime (RunRules R d) where
  wf := RunRules.wf h.wf
  noUnions := ⟨RunRules.diag h.noUnions, h.noUnions.sig, h.noUnions.rules⟩
  declared := runRules_declaredTerms h.wf h.declared h.rulesOk
  rulesOk := h.rulesOk
  shape := h.shape
  uf := h.uf

theorem Runtime.runStep {d e : Database} {R : RulesetName} (h : Runtime d)
    (hr : RunStep R d e) : Runtime e := (h.runRules R).merge hr

theorem Runtime.runReach {d e : Database} {R : RulesetName} (h : Runtime d)
    (hr : Relation.ReflTransGen (RunStep R) d e) : Runtime e :=
  RunReach.induction (fun _ _ h hs => h.runStep hs) hr h

theorem Descending.sUnion {d : Database} {S : Set Database} (h : Descending d)
    (hs : ∀ e ∈ S, Descending e) : Descending (d.sUnion S) := by
  intro a b hm
  simp only [Database.sUnion_terms, Set.mem_union, Set.mem_iUnion, exists_prop] at hm
  rcases hm with hm | ⟨e, he, hm⟩
  · exact h a b hm
  · exact hs e he a b hm

/-- Unioning all successful firings preserves each of their row invariants. -/
theorem runRules_preserves {src d : Database} {R : RulesetName}
    (hs : SoundTerms d src) (hd : Descending d)
    (hfire : ∀ r ∈ d.rules, r.ruleset = R → ∀ σ post,
      ValidQuerySubst d r.query σ → evalLocalActions d r.actions σ = some post →
        SoundTerms post src ∧ Descending post) :
    SoundTerms (RunRules R d) src ∧ Descending (RunRules R d) := by
  constructor
  · apply hs.sUnion
    rintro e ⟨r, hr, hR, σ, hσ, hf⟩
    exact (hfire r hr hR σ e hσ hf).1
  · apply hd.sUnion
    rintro e ⟨r, hr, hR, σ, hσ, hf⟩
    exact (hfire r hr hR σ e hσ hf).2

/-- A whole round includes every successful firing and any finite merge schedule. -/
theorem runStep_preserves {src d e : Database} {R : RulesetName} (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d)
    (hfire : ∀ r ∈ d.rules, r.ruleset = R → ∀ σ post,
      ValidQuerySubst d r.query σ → evalLocalActions d r.actions σ = some post →
        SoundTerms post src ∧ Descending post) (hr : RunStep R d e) :
    SoundTerms e src ∧ Descending e := by
  obtain ⟨hs', hd'⟩ := runRules_preserves hs hd hfire
  have h' := h.runRules R
  exact ⟨mergeClosure_soundTerms h'.shape h'.noUnions.diag h'.wf h'.declared h'.uf hs' hr,
    mergeClosure_descending h'.shape h'.noUnions.diag h'.wf h'.declared h'.uf hd' hr⟩

/-- Induction over the given finite derivation, without any assumption about the number
of rounds taken by the source. The callback handles a single actual firing. -/
theorem runReach_preserves {src d e : Database} {R : RulesetName} (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d)
    (hfire : ∀ mid, Runtime mid → mid.sig = d.sig → mid.rules = d.rules → mid.env = d.env →
      SoundTerms mid src → Descending mid → ∀ r ∈ mid.rules, r.ruleset = R → ∀ σ post,
      ValidQuerySubst mid r.query σ → evalLocalActions mid r.actions σ = some post →
        SoundTerms post src ∧ Descending post)
    (hr : Relation.ReflTransGen (RunStep R) d e) : SoundTerms e src ∧ Descending e := by
  have hi : Runtime e ∧ e.sig = d.sig ∧ e.rules = d.rules ∧ e.env = d.env ∧
      SoundTerms e src ∧ Descending e := by
    apply RunReach.induction (P := fun mid => Runtime mid ∧ mid.sig = d.sig ∧
      mid.rules = d.rules ∧ mid.env = d.env ∧ SoundTerms mid src ∧ Descending mid) _ hr
      ⟨h, rfl, rfl, rfl, hs, hd⟩
    rintro mid post ⟨hm, hsig, hrules, henv, hsound, hdesc⟩ hstep
    have hpostrules : post.rules = d.rules := by
      rw [(MergeClosure.envRules hstep).2]
      exact hrules
    exact ⟨hm.runStep hstep, (RunStep.sig hstep).trans hsig, hpostrules,
      (RunStep.env hstep).trans henv,
      runStep_preserves hm hsound hdesc (hfire mid hm hsig hrules henv hsound hdesc) hstep⟩
  exact hi.2.2.2.2

/-- A dedicated rebuilding run only fires maintenance; all such firings are sound. -/
theorem rebuild_preserves {P : Program} {src d e : Database} (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (hr : Relation.ReflTransGen (RunStep rebuildRuleset) d e) :
    SoundTerms e src ∧ Descending e := by
  apply runReach_preserves h hs hd _ hr
  intro mid hm _ hrules _ hsound hdesc r hr hR σ post hσ hf
  obtain ⟨c, hc, hcr⟩ := honly r (hrules ▸ hr) hR
  exact ⟨maintenance_soundTerms hc hcr hm.noUnions.diag hm.wf hsound hσ hf,
    maintenance_descending hc hcr hm.noUnions.diag hm.wf hdesc hσ hf⟩

/-- The mathematical `saturate @rebuild` command preserves the row invariants. -/
theorem rebuild_cmd_preserves {P : Program} {src d e : Database} (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (hr : CmdStep d (.saturate rebuildRuleset) e) : SoundTerms e src ∧ Descending e :=
  rebuild_preserves h hs hd honly ((cmdStep_saturate_iff.mp hr).1)

end Egglog.Congruence.Abstract
