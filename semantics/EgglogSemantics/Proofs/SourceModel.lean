import EgglogSemantics.Proofs.Completion
import EgglogSemantics.Proofs.StatePreservation

/-! Semantic saturation makes the completed source a model of its rules. -/

namespace Egglog.SourceMeaning

open InferredFacts

theorem firing_contained_round {d out : Database} {r : Rule} {R : RulesetName}
    (hr : r ∈ d.rules) (hR : r.ruleset = R) (ho : out ∈ RuleResults d r) :
    out.Contained (RunRules R d) := by
  rw [RunRules.eq_sUnion]
  exact ⟨fun _ hp => Or.inr (Set.mem_iUnion₂.mpr ⟨out, ⟨r, hr, hR, ho⟩, hp⟩)⟩

theorem round_extends (d : Database) (R : RulesetName) : d.Contained (RunRules R d) :=
  ⟨fun _ hp => Or.inl hp⟩

theorem firing_transport {d e out : Database} (hd : d.WF) (he : e.WF)
    (hs : e.StoreOk) (hc : d.sig.AllConstructors) (h : d.SameMeaning e)
    {r : Rule} (hn : r.OrderingFree)
    (ho : out ∈ RuleResults d r) :
    ∃ out', out' ∈ RuleResults e r ∧ out.SameMeaning out' := by
  obtain ⟨σ, hσ, hfire⟩ := ho
  obtain ⟨τ, hτ, hrel⟩ := validQuerySubst_transport hd he hs hc h hn.1 hσ
  obtain ⟨out', hfire', hsame⟩ := evalLocalActions_transport hd he hc h
    hσ.mem_terms hτ.mem_terms hrel hn.2 hfire
  exact ⟨out', ⟨τ, hτ, hfire'⟩, hsame⟩

private theorem round_infers {d e : Database} (hd : d.WF) (he : e.WF)
    (hs : e.StoreOk) (hc : d.sig.AllConstructors) (h : d.SameMeaning e)
    {R : RulesetName}
    (hn : ∀ r ∈ d.rules, r.ruleset = R → r.OrderingFree) {a b : Term}
    (hi : (RunRules R d).Infers a b) : (RunRules R e).Infers a b := by
  apply infers_of_assertions_only (RunRules.wf he) ?_ hi
  rw [RunRules.eq_sUnion R d]
  rintro p (hp | hp)
  · exact infers_mono (round_extends e R)
      ((h.inferred _ _).mp (infers_of_cong (.direct hp)))
  · obtain ⟨out, ⟨r, hr, hR, ho⟩, hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨out', ho', hh⟩ := firing_transport hd he hs hc h (hn r hr hR) ho
    exact infers_mono (firing_contained_round (h.rules ▸ hr) hR ho')
      ((hh.inferred _ _).mp (infers_of_cong (.direct hp)))

/-- Source rounds depend only on inferred facts, despite different stored spellings. -/
theorem round_sameMeaning {d e : Database} (hd : d.WF) (he : e.WF)
    (hdStore : d.StoreOk) (heStore : e.StoreOk)
    (hc : d.sig.AllConstructors) (h : d.SameMeaning e)
    {R : RulesetName}
    (hn : ∀ r ∈ d.rules, r.ruleset = R → r.OrderingFree) :
    (RunRules R d).SameMeaning (RunRules R e) := by
  refine Database.SameMeaning.of_inferred h.sig h.env h.rules (fun a b => ⟨?_, ?_⟩)
  · exact round_infers hd he heStore hc h hn
  · exact round_infers he hd hdStore (h.sig ▸ hc) h.symm
      (fun r hr hR => hn r (h.rules.symm ▸ hr) hR)

/-- Completing a semantic fixed point yields an ordinary assertion fixed point. -/
theorem completion_closed {d : Database} (hw : d.WF) (hs : d.StoreOk)
    (hc : d.sig.AllConstructors) {R : RulesetName}
    (hn : ∀ r ∈ d.rules, r.ruleset = R → r.OrderingFree)
    (hfixed : d.SameMeaning (RunRules R d)) :
    RunRules R d.completion = d.completion := by
  apply (runRules_eq_self_iff R d.completion).mpr
  intro r hr hR out ho
  obtain ⟨out', ho', hh⟩ := firing_transport hw.completion hw hs hc
    (d.sameMeaning_completion hw).symm (hn r hr hR) ho
  constructor
  intro p hp
  exact (hfixed.inferred _ _).mpr
    (infers_mono (firing_contained_round (d := d) hr hR ho')
      ((hh.inferred _ _).mp (infers_of_cong (.direct hp))))

theorem completion_closed_of_saturated {d : Database} (hw : d.WF) (hs : d.StoreOk)
    (hc : d.sig.AllConstructors) {R : RulesetName}
    (hn : ∀ r ∈ d.rules, r.ruleset = R → r.OrderingFree)
    (hfixed : RunSaturated R d) : RunRules R d.completion = d.completion := by
  obtain ⟨_, post, hstep, hh⟩ := hfixed
  rw [hstep.eq_of_allConstructors hc] at hh
  exact completion_closed hw hs hc hn hh

/-- The returned state of source saturation is closed, including its last round. -/
theorem saturation_completion_closed {d e : Database} (hw : d.WF) (hs : d.StoreOk)
    (hc : d.sig.AllConstructors) {R : RulesetName}
    (hn : ∀ r ∈ d.rules, r.ruleset = R → r.OrderingFree)
    (hr : SaturateReach R d e) : RunRules R e.completion = e.completion := by
  induction hr using SaturateReach.induction with
  | done hstep hh =>
      have hh' := hh
      rw [hstep.eq_of_allConstructors hc] at hh'
      rw [← hh.completion_eq]
      exact completion_closed hw hs hc hn hh'
  | @step d mid e hstep _ _ ih =>
      obtain rfl := hstep.eq_of_allConstructors hc
      exact ih (RunRules.wf hw) (RunRules.storeOk_of_allConstructors hs hc) hc hn

end Egglog.SourceMeaning
