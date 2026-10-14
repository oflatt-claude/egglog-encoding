import EgglogSemantics.Proofs.Congruence.AbstractSoundHead
import EgglogSemantics.Proofs.Congruence.AbstractRunState

/-! Source rounds justify target rounds and target saturation independently of round counts. -/

namespace Egglog.Congruence.Abstract

/-- Readback of a compiled rule is sound in any source state containing its source result. -/
theorem source_firing_preserves {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ rest) {src ref d post : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d) (hsig : d.sig = encodeSig P)
    {r : Rule} (hr : r ∈ src.rules)
    (hupper : ∀ out ∈ RuleResults src r, out.Contained ref) {σ : Env}
    (hm : ValidQuerySubst d (encodeRule r).query σ)
    (hf : evalLocalActions d (encodeRule r).actions σ = some post) :
    SoundTerms post ref ∧ Descending post := by
  have hmem : Cmd.rule r ∈ P := by
    rw [hP]
    apply List.mem_append_left
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr
  obtain ⟨τ, out, hτ, hout, hs', hd'⟩ := encodedRule_firing_of_programStep hp hP hpre
    hmem hr h.wf h.noUnions.diag hs hd hsig hm hf
  exact ⟨hs'.mono_src (hupper out ⟨τ, hτ, hout⟩).eqs, hd'⟩

/-- Every target rule result and merge in an aligned round is justified by that source round. -/
theorem source_round_preserves {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d) (hsig : d.sig = encodeSig P)
    (hrules : RulesEncoded P src d) {R : RulesetName}
    (hsource : RunStep R src post) (htarget : RunStep R d e) :
    SoundTerms e post ∧ Descending e := by
  apply runStep_preserves h (hs.mono_src hsource.contained.eqs) hd _ htarget
  intro r hr hR σ out hm hf
  rcases (hrules r).mp hr with ⟨c, hc, hcr⟩ | ⟨s, hs', rfl⟩
  · exact ⟨(maintenance_soundTerms hc hcr h.noUnions.diag h.wf hs hm hf).mono_src
      hsource.contained.eqs, maintenance_descending hc hcr h.noUnions.diag h.wf hd hm hf⟩
  · apply source_firing_preserves hp hP hpre h hs hd hsig hs' _ hm hf
    intro result hresult
    refine Database.Contained.trans ?_ (MergeClosure.contained hsource)
    exact ⟨fun p hpair => Or.inr
      (Set.mem_iUnion₂.mpr ⟨result, ⟨s, hs', hR, hresult⟩, hpair⟩)⟩

/-- A fixed source state justifies an arbitrary finite target saturation execution.
It already contains every source firing reconstructed from an intermediate target match. -/
theorem source_saturation_preserves {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ rest) {src d e : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d) (hsig : d.sig = encodeSig P)
    (hrules : RulesEncoded P src d) {R : RulesetName} (hsat : RunSaturated R src)
    (htarget : Relation.ReflTransGen (RunStep R) d e) :
    SoundTerms e src ∧ Descending e := by
  apply runReach_preserves h hs hd _ htarget
  intro mid hm hmSig hmRules _ hsound hdesc r hr hR σ out hσ hf
  rcases (hrules r).mp (hmRules ▸ hr) with ⟨c, hc, hcr⟩ | ⟨s, hs', rfl⟩
  · exact ⟨maintenance_soundTerms hc hcr hm.noUnions.diag hm.wf hsound hσ hf,
      maintenance_descending hc hcr hm.noUnions.diag hm.wf hdesc hσ hf⟩
  · exact source_firing_preserves hp hP hpre hm hsound hdesc (hmSig.trans hsig) hs'
      ((runRules_eq_self_iff R src).mp hsat.1 s hs' hR) hσ hf

end Egglog.Congruence.Abstract
