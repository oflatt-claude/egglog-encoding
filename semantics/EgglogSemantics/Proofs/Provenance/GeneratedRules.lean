import EgglogSemantics.Proofs.Provenance.GeneratedEvaluation
import EgglogSemantics.Proofs.Congruence.AbstractSoundRounds
import EgglogSemantics.Proofs.Congruence.AbstractRowWrites
import EgglogSemantics.Proofs.SourceModel

/-! Accepted generated rule facts extend a finite, source-sound witness store. -/

namespace Egglog.Provenance.Generated

open Congruence Congruence.Abstract

private theorem maintenanceRules_rowActions {P : Program} {c : Command}
    (hc : c ∈ maintenanceRules P) {r : Rule} (hr : c.command = .rule r) :
    ∀ a ∈ r.actions, RowAction a := by
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · obtain rfl : pathCompressRule = r := Cmd.rule.inj hr
    intro a ha
    obtain rfl := List.mem_singleton.mp ha
    exact RowAction.uf _ _
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩
    · obtain rfl : eclassRule f k = r := Cmd.rule.inj hr
      intro a ha
      obtain rfl := List.mem_singleton.mp ha
      exact RowAction.view _ _ _
    · obtain rfl : childRule f k i = r := Cmd.rule.inj hr
      intro a ha
      obtain rfl := List.mem_singleton.mp ha
      exact RowAction.view _ _ _

private theorem maintenance_rowActions {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) :
    ∀ a ∈ r.actions, RowAction a := by
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenanceRules_rowActions hc hr
  · unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl : { s with ruleset := R } = r := Cmd.rule.inj hr
      exact maintenanceRules_rowActions (r := s) hc hs
    next => exact maintenanceRules_rowActions hc hr

private theorem generated_rule_cases {P : Program} {r : Rule}
    (hr : Cmd.rule r ∈ encode P) :
    (∃ c ∈ allMaintenanceRules P, c.command = .rule r) ∨
      ∃ s, Cmd.rule s ∈ P ∧ r = encodeRule s := by
  simpa only [encode, compile, List.map_append, List.mem_append,
    rule_mem_prelude, rule_mem_encodeCmds] using hr

private theorem local_runtime {d post : Database} {r : Rule} {σ : Env}
    (h : Live.Runtime d) (hu : Actions.UnionFree r.actions) (hq : r.query.Safe)
    (hm : ValidQuerySubst d r.query σ)
    (hf : evalLocalActions d r.actions σ = some post) : Live.Runtime post := by
  refine ⟨evalLocalActions_wf h.wf hm.mem_terms hf,
    evalLocalActions_storeOk h.storeOk (fun b hb => (hm.mem_values h.storeOk hq b hb).2) hf,
    ⟨evalLocalActions_diag hu h.noUnions.diag hf, ?_, ?_⟩,
    h.state.evalLocalActions h.generated h.storeOk
      (fun b hb => (hm.mem_values h.storeOk hq b hb).2) hf, ?_, ?_⟩
  · rw [evalLocalActions_sig hf]; exact h.noUnions.sig
  · rw [evalLocalActions_rules hf]; exact h.noUnions.rules
  · rw [evalLocalActions_sig hf]; exact h.generated
  · simpa only [Database.RulesSafe, evalLocalActions_rules hf] using h.rulesSafe

/-- Source saturation justifies both compiled source heads and maintenance heads. -/
theorem rule_firing_sound {P : Program} (hp : P.Fragment) {src d post : Database}
    (hsource : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src)
    (h : Live.Runtime d) (hsig : d.sig = encodeSig P)
    (hs : SoundTerms d src.completion) (hd : Descending d)
    {r : Rule} (hr : Cmd.rule r ∈ encode P) {σ : Env}
    (hm : ValidQuerySubst d r.query σ)
    (hf : evalLocalActions d r.actions σ = some post) :
    SoundTerms post src.completion ∧ Descending post ∧
      post.terms ⊆ d.terms ∪ (src.completion.terms ∪ SoundRows src.completion) := by
  have hcs := hsource.ctorState Database.CtorState.empty hp.ctorsOnly
  suffices hpost : SoundTerms post src.completion ∧ Descending post ∧
      (∀ a ∈ r.actions, RowAction a) by
    exact ⟨hpost.1, hpost.2.1,
      evalLocalActions_rows_newTerms hcs.wf.completion hpost.1 hpost.2.2 hf⟩
  rcases generated_rule_cases hr with ⟨c, hc, hcr⟩ | ⟨s, hsP, rfl⟩
  · exact ⟨maintenance_soundTerms hc hcr h.noUnions.diag h.wf hs hm hf,
      maintenance_descending hc hcr h.noUnions.diag h.wf hd hm hf,
      maintenance_rowActions hc hcr⟩
  · have hsRule : s ∈ src.rules := (hsource.mem_rules_iff s).mpr (Or.inr hsP)
    have hstore := storeOk_of_sourceTerms hcs.wf
      (termsBuild_of_programStep hp.ctorsOnly hsource) hcs.sig
    have hfixed : RunRules s.ruleset src.completion = src.completion := by
      apply SourceMeaning.completion_closed_of_saturated hcs.wf hstore hcs.sig
        (fun r hr _ => ?_)
        (hclosed s.ruleset)
      have hmem : Cmd.rule r ∈ P := by
        simpa [Database.empty] using (hsource.mem_rules_iff r).mp hr
      exact Program.OrderingFree.of_mem hp.noMin hmem
    obtain ⟨hsound, hdesc⟩ := source_firing_preserves (rest := []) hp (by simp)
      hsource h hs hd hsig
      hsRule ((runRules_eq_self_iff s.ruleset src.completion).mp hfixed s hsRule rfl) hm hf
    exact ⟨hsound, hdesc, encodeActions_rowActions _⟩

private theorem ruleFacts_eval {d : Database} (hw : d.WF) (henv : d.env = [])
    {r : Rule} {σ : Env} {premises fs : List Term}
    (hprem : ∀ t ∈ premises, t ∈ d.terms)
    (hf : ruleFacts d.sig r σ premises = some fs) :
    ∃ τ post, ValidQuerySubst d r.query τ ∧
      evalLocalActions d r.actions τ = some post ∧
      evalLocalActions d r.actions σ = some post ∧ Actions.UnionFree r.actions ∧
      ∀ t ∈ fs, t ∈ post.terms := by
  unfold ruleFacts at hf
  split at hf
  · rename_i hchecks
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true] at hchecks
    have hval : ∀ b ∈ σ, b.2 ∈ d.values := by
      intro b hb
      obtain ⟨p, hpm, hsub⟩ := List.any_eq_true.mp (hchecks.1.2 b hb).2
      exact ⟨hw.subtermClosed p (hprem p hpm)
        ((Term.mem_subtermList p).mp (of_decide_eq_true hsub)),
        SourceProof.valueOk_isValue (hchecks.1.2 b hb).1⟩
    obtain ⟨τ, hτ, hag⟩ := SourceProof.querySubst_of_matches hchecks.1.1 hval
      (premisesMatch_sound hprem hchecks.2)
    obtain ⟨out, hout, hfs⟩ := actionsFacts_sound (db := { d with env := σ }) hf
    let post : Database := { out with env := d.env, rules := d.rules }
    have hlocal : evalLocalActions d r.actions σ = some post := by
      simp only [evalLocalActions, henv, hout, Option.map_some]
      simp only [post, henv]
    refine ⟨τ, post, hτ, ?_, hlocal, actionsFacts_unionFree hf, ?_⟩
    · rw [evalLocalActions_agree _ hag]; exact hlocal
    · exact fun t ht => (show out.Contained post from ⟨fun _ h => h⟩).terms (hfs t ht)
  · contradiction

/-- Every accepted generated rule fact has a finite source-sound post-state witness. -/
theorem ruleFacts_sound {P : Program} (hp : P.Fragment) {src d : Database}
    (hsource : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src)
    (h : Live.Runtime d) (hsig : d.sig = encodeSig P) (henv : d.env = [])
    (hs : SoundTerms d src.completion) (hd : Descending d)
    {r : Rule} (hr : Cmd.rule r ∈ encode P) {σ : Env} {premises fs : List Term}
    (hprem : ∀ t ∈ premises, t ∈ d.terms)
    (hf : ruleFacts d.sig r σ premises = some fs) :
    ∃ post, evalLocalActions d r.actions σ = some post ∧ Live.Runtime post ∧
      post.sig = d.sig ∧ post.env = d.env ∧ post.rules = d.rules ∧
      SoundTerms post src.completion ∧ Descending post ∧
      post.terms ⊆ d.terms ∪ (src.completion.terms ∪ SoundRows src.completion) ∧
      ∀ t ∈ fs, t ∈ post.terms := by
  obtain ⟨τ, post, hτ, hfire, hlocal, hu, hfs⟩ := ruleFacts_eval h.wf henv hprem hf
  obtain ⟨hsound, hdesc, hbound⟩ := rule_firing_sound hp hsource hclosed h hsig hs hd
    hr hτ hfire
  exact ⟨post, hlocal, local_runtime h hu (encode_querySafe hp r hr) hτ hfire, evalLocalActions_sig hlocal,
    evalLocalActions_env hlocal, evalLocalActions_rules hlocal, hsound, hdesc, hbound, hfs⟩

end Egglog.Provenance.Generated
