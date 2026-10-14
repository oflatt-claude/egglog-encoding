import EgglogSemantics.Proofs.StepMonotone
import EgglogSemantics.Proofs.Congruence.AbstractHead
import EgglogSemantics.Proofs.Congruence.AbstractMetadata
import EgglogSemantics.Proofs.Congruence.AbstractState
import EgglogSemantics.Proofs.Congruence.ActionExprs

/-! A mathematical compiled fixed point represents each finite source round sequence. -/

namespace Egglog.Congruence

namespace Abstract

/-- The source fragment discharges the syntax and declaration premises of forward firing.
The represented source state may precede the state justifying target rows. -/
theorem encodedRule_firing_reads_of_programStep {P pre : Program}
    (hp : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    {src querySrc post : Database} (hpre : ProgramStep Database.empty pre src)
    (hqsig : querySrc.sig = src.sig) (hqenv : querySrc.env = [])
    {d : Database} (h : Rebuilt d) (hdg : d.Diag) (hs : SoundTerms d src)
    (hsig : d.sig = encodeSig P) (hreads : SourceReads d querySrc)
    {r : Rule} (hr : Cmd.rule r ∈ P) {σ : Env}
    (hm : ValidQuerySubst querySrc r.query σ)
    (hf : evalLocalActions querySrc r.actions σ = some post) :
    ∃ ρ d', ValidQuerySubst d (encodeRule r).query ρ ∧
      evalLocalActions d (encodeRule r).actions ρ = some d' ∧ SourceReads d' post := by
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))
  have hcensus := ctorsIn_of_prefixStep hp hsub hpre
  have hdecl : ViewDeclared d := by
    intro f cs e ho
    obtain ⟨as, ha, hcs, _⟩ := hs.viewsSound hdg f cs e ho
    have hk : (f, cs.length) ∈ P.ctors := hcs.length_eq ▸ hcensus f as ha
    simp [hsig, (encodeSig_tables hp hk).2]
  have hhead : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, fk ∈ P.ctors := by
    intro a ha e he fk hk
    apply mem_program_ctors hr
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, actionExprs_ctors he hk⟩)
  apply encodedRule_firing_reads h hdg hdecl (hs.edgesSound hdg)
    (hpre.wf Database.WF.empty) (by rw [hqsig]; exact hcs.sig) hreads hqenv
    ?_ (hp.queryEncodable _ hr).2
    (fun p hm => ((hp.queryEncodable _ hr).1 p hm).1) ?_ ?_ ?_ ?_ ?_ hm hf
  · exact (Program.OrderingFree.of_mem hp.noMin hr).1
  · intro v hv
    apply hp.noAt v
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_dedup.mpr
    apply List.mem_flatMap.mpr
    exact ⟨Cmd.rule r, hr, List.mem_union_iff.mpr (Or.inl hv)⟩
  · exact orderingFree_actionExprs (Program.OrderingFree.of_mem hp.noMin hr).2
  · intro _ _ _ _ f _ hctor
    exact sourceConstructors_of_programStep hp hsub hpre hsig f (hqsig ▸ hctor)
  · simp [hsig, encodeSig_ufName hp]
  · intro a ha e he fk hk
    simp [hsig, (encodeSig_tables hp (hhead a ha e he fk hk)).2]

/-- A target fixed point contains every source firing whose premises it represents. -/
theorem SourceReads.round_of_closed {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src querySrc : Database}
    (hpre : ProgramStep Database.empty pre src)
    (hqsig : querySrc.sig = src.sig) (hqenv : querySrc.env = [])
    {d : Database} (h : Rebuilt d) (hdg : d.Diag) (hs : SoundTerms d src)
    (hsig : d.sig = encodeSig P) (hreads : SourceReads d querySrc)
    (hrules : ∀ r ∈ querySrc.rules, Cmd.rule r ∈ P ∧ encodeRule r ∈ d.rules)
    {R : RulesetName} (hclosed : RunRules R d = d) : SourceReads d (RunRules R querySrc) := by
  apply hreads.runRules
  intro r hr hR post hpost
  obtain ⟨σ, hm, hf⟩ := hpost
  obtain ⟨ρ, d', hmatch, hfire, hreads'⟩ := encodedRule_firing_reads_of_programStep
    hp hsub hpre hqsig hqenv h hdg hs hsig hreads (hrules r hr).1 hm hf
  exact hreads'.mono ((runRules_eq_self_iff R d).mp hclosed (encodeRule r)
    (hrules r hr).2 hR d' ⟨ρ, hmatch, hfire⟩)

/-- A fixed mathematical target represents every finite source-round sequence.
No agreement between the numbers of source and target rounds is required. -/
theorem SourceReads.reach_of_closed {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src start post : Database}
    (hpre : ProgramStep Database.empty pre src)
    (hssig : start.sig = src.sig) (hsenv : start.env = [])
    {d : Database} (h : Rebuilt d) (hdg : d.Diag) (hs : SoundTerms d src)
    (hsig : d.sig = encodeSig P) (hreads : SourceReads d start)
    (hrules : ∀ r ∈ start.rules, Cmd.rule r ∈ P ∧ encodeRule r ∈ d.rules)
    {R : RulesetName} (hclosed : RunRules R d = d)
    (hreach : Relation.ReflTransGen (RunStep R) start post) : SourceReads d post := by
  have hctor := (hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))).sig
  have go : SourceReads d post ∧ post.sig = src.sig ∧ post.env = [] ∧
      post.rules = start.rules := by
    induction hreach with
    | refl => exact ⟨hreads, hssig, hsenv, rfl⟩
    | @tail m e hreach hstep ih =>
        have hresult := SourceReads.round_of_closed hp hsub hpre ih.2.1 ih.2.2.1 h hdg hs
          hsig ih.1 (fun r hr => hrules r (ih.2.2.2 ▸ hr)) hclosed
        refine ⟨?_, hstep.sig.trans ih.2.1, hstep.env.trans ih.2.2.1,
          hstep.envRules.2.trans ih.2.2.2⟩
        rw [hstep.eq_of_allConstructors (by rw [ih.2.1]; exact hctor)]
        exact hresult
  exact go.1


/-- An actual target round represents every result of the corresponding source round.
The arbitrary target merge phase only extends those facts. -/
theorem round_reads {P pre : Program} (hp : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    {src post : Database} (hpre : ProgramStep Database.empty pre src)
    {R : RulesetName} (hsource : RunStep R src post) {d e : Database}
    (h : Rebuilt d) (hdg : d.Diag) (hs : SoundTerms d src)
    (hsig : d.sig = encodeSig P) (hrules : RulesEncoded P src d)
    (hreads : SourceReads d src) (htarget : RunStep R d e) : SourceReads e post := by
  have hcs := (hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))).sig
  rw [hsource.eq_of_allConstructors hcs]
  apply (hreads.mono htarget.contained).runRules
  intro r hr hR out hout
  obtain ⟨σ, hm, hf⟩ := hout
  have hmem : Cmd.rule r ∈ P := hsub _ (by
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr)
  obtain ⟨ρ, d', hmatch, hfire, hreads'⟩ := encodedRule_firing_reads_of_programStep
    hp hsub hpre rfl hpre.env h hdg hs hsig hreads hmem hm hf
  apply hreads'.mono
  apply Database.Contained.trans ?_ (MergeClosure.contained htarget)
  refine ⟨fun p hpair => Or.inr (Set.mem_iUnion₂.mpr ⟨d', ?_, hpair⟩)⟩
  exact ⟨encodeRule r, (hrules _).mpr (Or.inr ⟨r, hr, rfl⟩), hR, ρ, hmatch, hfire⟩

/-- A terminating target saturation represents the terminating source saturation once
its endpoint is rebuilt and source-sound. The two finite executions may take different
numbers of rounds. -/
theorem saturation_reads {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src start : Database}
    (hpre : ProgramStep Database.empty pre src) {R : RulesetName}
    (hsource : SaturateReach R start src) (henv : start.env = [])
    {initial d : Database} (htarget : SaturateReach R initial d)
    (h : Rebuilt d) (hdg : d.Diag) (hs : SoundTerms d src)
    (hsig : d.sig = encodeSig P) (hrules : RulesEncoded P src d)
    (hreads : SourceReads initial start) : SourceReads d src := by
  apply SourceReads.reach_of_closed hp hsub hpre (RunReach.sig hsource.1).symm henv
    h hdg hs hsig (hreads.mono (RunReach.contained htarget.1)) ?_
    htarget.2.1 hsource.1
  intro r hr
  have hr' : r ∈ src.rules := runReach_rules hsource.1 ▸ hr
  have hmem : Cmd.rule r ∈ P := hsub _ (by
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr')
  exact ⟨hmem, (hrules _).mpr (Or.inr ⟨r, hr', rfl⟩)⟩

end Abstract
end Egglog.Congruence
