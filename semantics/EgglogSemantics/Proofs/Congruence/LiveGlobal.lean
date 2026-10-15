import EgglogSemantics.Proofs.Congruence.UFCoverage
import EgglogSemantics.Proofs.Congruence.AbstractBuild
import EgglogSemantics.Proofs.Congruence.AbstractRunState
import EgglogSemantics.Proofs.Congruence.AbstractSoundHead
import EgglogSemantics.Proofs.Congruence.LiveRunRead

/-! Actual compiled global actions preserve the live source correspondence. -/

namespace Egglog.Congruence.Live

open Abstract

/-- A successful compiled rule head supplies its own operand evaluation witnesses. -/
theorem encodedRule_firing_ufTotal {P : Program} (hp : P.Fragment) {r : Rule}
    (hrule : Cmd.rule r ∈ P) {d e : Database} {ρ : Env} (h : Runtime d)
    (hsig : d.sig = encodeSig P) (hu : UFTotal d)
    (hρ : ValidQuerySubst d (encodeRule r).query ρ)
    (hfire : evalLocalActions d (encodeRule r).actions ρ = some e) : UFTotal e := by
  apply encodeLocalActions_ufTotal_of_run (as := r.actions.map leaderAction)
    h.wf hu hρ.mem_terms ?_ ?_ h.state.uf hfire
  · intro a ha x hx
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ha
    rw [leaderAction_exprs] at hx
    obtain ⟨expr, hexpr, rfl⟩ := List.mem_map.mp hx
    exact (leaderExpr_orderingFree expr).mpr
      (orderingFree_actionExprs (Program.OrderingFree.of_mem hp.noMin hrule).2
        original horiginal expr hexpr)
  · intro a ha x hx fk hfk
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ha
    rw [leaderAction_exprs] at hx
    obtain ⟨expr, hexpr, rfl⟩ := List.mem_map.mp hx
    have hk : fk ∈ P.ctors := mem_program_ctors hrule
      (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨original, horiginal, actionExprs_ctors hexpr (leaderExpr_ctors expr ▸ hfk)⟩))
    exact hsig ▸ (encodeSig_tables hp hk).2

theorem target_firing_ufTotal {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src : Database}
    (hpre : ProgramStep Database.empty pre src) {d e : Database} (h : Runtime d)
    (hsig : d.sig = encodeSig P) (hrules : RulesEncoded P src d) (hu : UFTotal d)
    {r : Rule} (hr : r ∈ d.rules) {ρ : Env} (hρ : ValidQuerySubst d r.query ρ)
    (hfire : evalLocalActions d r.actions ρ = some e) : UFTotal e := by
  rcases (hrules r).mp hr with ⟨c, hc, hcr⟩ | ⟨s, hs, rfl⟩
  · exact maintenance_ufTotal hp hc hcr hsig h.wf hu hρ hfire
  · have hm : Cmd.rule s ∈ P := by
      apply hsub
      simpa only [Database.empty, Set.mem_empty_iff_false, false_or] using
        (hpre.mem_rules_iff s).mp hs
    exact encodedRule_firing_ufTotal hp hm h hsig hu hρ hfire

theorem target_runReach_ufTotal {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src : Database}
    (hpre : ProgramStep Database.empty pre src) {d e : Database} (h : Runtime d)
    (hsig : d.sig = encodeSig P) (hrules : RulesEncoded P src d) (hu : UFTotal d)
    {R : RulesetName} (hr : Relation.ReflTransGen (RunStep R) d e) : UFTotal e := by
  apply hu.runReach h (hsig ▸ encodeSig_mergeShape P) ?_ hr
  intro mid hm hs hrules' _ hum r hmem _ ρ post hρ hfire
  apply target_firing_ufTotal hp hsub hpre hm (hs.trans hsig) ?_ hum hmem hρ hfire
  intro r
  rw [hrules']
  exact hrules r

theorem global_writes_of_programStep {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) {a : Action} (ha : Cmd.action a ∈ P)
    (hsrc : CmdStep src (.action a) post) {d e : Database} (h : Runtime d)
    (hsig : d.sig = encodeSig P) (henv : d.env = [])
    (hs : SoundTerms d src.completion) (hd : Descending d)
    (hreads : Reads d src) (hu : UFTotal d)
    (htgt : ProgramStep d ((encodeAction a).map Cmd.action) e) :
    Runtime e ∧ SoundTerms e post.completion ∧ Descending e ∧ Reads e post ∧ UFTotal e := by
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))
  have hact : evalAction src a = some post := by
    obtain ⟨mid, hm, hn⟩ := hsrc
    have he : post = mid := hn.1.eq_of_allConstructors (by
      rw [evalAction_sig hm]; exact hcs.sig)
    exact he.symm ▸ hm
  have hpostwf := evalAction_wf hcs.wf hact
  have hsourceStore := storeOk_of_sourceTerms hcs.wf
    (termsBuild_of_programStep (fun c hc => hp.ctorsOnly c (hsub c hc)) hpre) hcs.sig
  have hpostStore := evalAction_storeOk hsourceStore hact
  have hpostCtor : post.sig.AllConstructors := by rw [evalAction_sig hact]; exact hcs.sig
  have hsafe : SourceSafe post.completion := sourceSafe_completion hpostwf hpostStore
    hpostCtor (by
      intro f dc hf
      rw [evalAction_sig hact] at hf
      exact sourceNames_of_programStep hp hsub hpre f dc hf)
  have hsrcenv : src.env = [] := hpre.env
  have hctor := sourceConstructors_of_programStep hp hsub hpre hsig
  have hof := Action.orderingFree_exprs (Program.OrderingFree.of_mem hp.noMin ha)
  have hviews : ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2) := by
    intro x hx fk hk
    exact hsig ▸ (encodeSig_tables hp (mem_program_ctors ha (actionExprs_ctors hx hk))).2
  have heval : ∀ x ∈ actionExprs a, ∀ t,
      x.eval src.sig src.env = some t → x.eval d.sig d.env = some t := by
    intro x _ t ht
    apply eval_transport x (fun f _ => hctor f) ?_ ?_ ht
    · intro v _; rw [hsrcenv, henv]
    · intro v _ t ht _; simp [hsrcenv] at ht
  have hρ : EnvReads d src.env d.env := by
    intro v t ht
    simp [hsrcenv] at ht
  have hwrite := (encodeAction_sourceWrites hpostwf hcs.sig hof hviews h.state.uf heval hact).mono
    post.contained_completion
  have hcontained : src.completion.Contained post.completion :=
    ⟨fun _ hi => InferredFacts.infers_mono (evalAction_contained hact) hi⟩
  obtain ⟨hruntime, hsound, hdesc⟩ := sourceWrites_program_preserves hpostwf.completion
    hsafe h (hsig ▸ encodeSig_mergeShape P) (hs.mono_src hcontained.eqs) hd hwrite htgt
  obtain ⟨raw, hraw, hreadraw⟩ := encodeAction_reads hcs.sig hof
    (fun _ _ f _ => hctor f) hviews h.state.uf hρ hreads hact
  have huraw := encodeAction_ufTotal h.wf hu hof hviews h.state.uf
    (encodeAction_evaluates hof hraw) hraw
  exact ⟨hruntime, hsound, hdesc,
    (evalActions_covers_program (Covers.refl d) rfl h (encodeAction_unionFree a)
      hraw htgt).reads hreadraw,
    UFTotal.of_evalActions_program h (hsig ▸ encodeSig_mergeShape P)
      (encodeAction_unionFree a) hraw huraw htgt⟩

private theorem append_inv {p q : Program} {d e : Database}
    (hr : ProgramStep d (p ++ q) e) : ∃ mid, ProgramStep d p mid ∧ ProgramStep mid q e := by
  induction p generalizing d with
  | nil => exact ⟨d, .nil, hr⟩
  | cons c cs ih =>
      obtain ⟨mid, hc, hrest⟩ := hr.cons_inv
      obtain ⟨post, hp, hq⟩ := ih hrest
      exact ⟨post, .cons hc hp, hq⟩

private theorem action_program_rules {d e : Database} {as : List Action}
    (h : ProgramStep d (as.map Cmd.action) e) : e.rules = d.rules := by
  ext r
  rw [h.mem_rules_iff]
  constructor
  · rintro (hr | hr)
    · exact hr
    · obtain ⟨a, _, ha⟩ := List.mem_map.mp hr
      cases ha
  · exact Or.inl

private theorem action_program_sig {d e : Database} {as : List Action}
    (h : ProgramStep d (as.map Cmd.action) e) : e.sig = d.sig := by
  induction as generalizing d with
  | nil => obtain rfl := h.nil_inv; rfl
  | cons a as ih =>
      obtain ⟨mid, hm, hr⟩ := h.cons_inv
      exact (ih hr).trans hm.sig

theorem global_command_of_programStep {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) {a : Action} (ha : Cmd.action a ∈ P)
    (hsrc : CmdStep src (.action a) post) {d e : Database} (h : Runtime d)
    (hsig : d.sig = encodeSig P) (henv : d.env = [])
    (hs : SoundTerms d src.completion) (hd : Descending d)
    (hreads : Reads d src) (hu : UFTotal d)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    {i : Nat} (htgt : ProgramStep d ((encodeCmd i (.action a)).map Command.command) e) :
    Runtime e ∧ SoundTerms e post.completion ∧ Descending e ∧ Reads e post ∧
      UFTotal e ∧ RunSaturated rebuildRuleset e := by
  have hprog : ProgramStep d
      ((encodeAction a).map Cmd.action ++ [.saturate rebuildRuleset]) e := by
    simpa only [encodeCmd, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def] using htgt
  obtain ⟨mid, hwrite, hrest⟩ := append_inv hprog
  obtain ⟨post', hsat, hnil⟩ := hrest.cons_inv
  obtain rfl := hnil.nil_inv
  obtain ⟨hm, hsound, hdesc, hread, hutotal⟩ :=
    global_writes_of_programStep hp hsub hpre ha hsrc h hsig henv hs hd hreads hu hwrite
  have hmsig : mid.sig = encodeSig P := (action_program_sig hwrite).trans hsig
  have hrules := action_program_rules hwrite
  have honly' : ∀ r ∈ mid.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r :=
    fun r hr hR => honly r (hrules ▸ hr) hR
  have hsaturate := cmdStep_saturate_iff.mp hsat
  obtain ⟨hsound', hdesc'⟩ :=
    rebuild_cmd_preserves hm (hmsig ▸ encodeSig_mergeShape P) hsound hdesc honly' hsat
  exact ⟨hm.runReach hsaturate.reach, hsound', hdesc',
    (Covers.runReach hm hsaturate.reach).reads hread,
    hutotal.rebuild hp hm hmsig honly' hsaturate.reach,
    saturated_endpoint hm hsaturate⟩

end Egglog.Congruence.Live
