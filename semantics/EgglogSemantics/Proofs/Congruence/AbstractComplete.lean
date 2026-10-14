import EgglogSemantics.Proofs.Congruence.AbstractSetup
import EgglogSemantics.Proofs.Congruence.AbstractBoundary
import EgglogSemantics.Proofs.Congruence.AbstractWidths
import EgglogSemantics.Proofs.Congruence.AbstractGlobals
import EgglogSemantics.Proofs.Congruence.Observation

/-! Composition of mathematical congruence compilation at original command boundaries. -/

namespace Egglog.Congruence.Abstract

/-- Rebuilding closes a sound representation without losing any source facts. -/
theorem boundary_of_rebuild {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src d e : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d) (hrules : RulesEncoded P src d)
    (hreads : SourceReads d src) (ht : CmdStep d (.saturate rebuildRuleset) e) :
    Boundary src e := by
  obtain ⟨hs', hd'⟩ := rebuild_cmd_preserves h hs hd
    (hrules.rebuild_only hp hpre hsub) ht
  exact ⟨hs', hd', hreads.mono ht.contained, (cmdStep_saturate_iff.mp ht).2⟩

/-- Extend the compiled prefix at the same source-command index. -/
theorem compiled_prefix_step {P pre : Program} {d e : Database} {c : Cmd}
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (hc : ProgramStep d ((encodeCmd pre.length c).map Command.command) e) :
    ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds (pre ++ [c]) 0).map Command.command) e := by
  have hex : encodeCmds (pre ++ [c]) 0 = encodeCmds pre 0 ++ encodeCmd pre.length c := by
    rw [encodeCmds_append]
    simp only [Nat.zero_add, encodeCmds, List.append_nil]
  simpa only [hex, List.append_assoc, List.map_append] using ht.append hc

/-- An original run is one paired round followed by dedicated target rebuilding. -/
theorem Boundary.run {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ Cmd.run R :: rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hrt : Runtime d) (hsource : CmdStep src (.run R) post)
    (htarget : ProgramStep d ((encodeCmd pre.length (.run R)).map Command.command) e) :
    Boundary post e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hnext := hpre.append (ProgramStep.cons hsource .nil)
  have hsub' : ∀ c ∈ pre ++ [Cmd.run R], c ∈ P := by
    intro c hc
    rw [hP]
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · exact List.mem_append_right _ (List.mem_singleton.mp hc ▸ List.mem_cons_self)
  have hm := metadata_of_prefix hpre htpre
  have hs : RunStep R src post := by
    obtain ⟨mid, rfl, hs⟩ := hsource
    exact hs
  obtain ⟨mid, hfirst, hrest⟩ := htarget.cons_inv
  obtain ⟨last, hlast, hnil⟩ := hrest.cons_inv
  obtain rfl := hnil.nil_inv
  have ht : RunStep R d mid := by
    obtain ⟨out, rfl, ht⟩ := hfirst
    exact ht
  obtain ⟨hsound, hdesc⟩ := source_round_preserves hp hP hpre hrt
    h.sound h.descend hm.sig hm.rules hs ht
  have hreads := round_reads hp hsub hpre hs (h.rebuilt hp hsub hpre htpre)
    hrt.noUnions.diag h.sound hm.sig hm.rules h.reads ht
  have hrules : RulesEncoded P post mid := by
    intro r
    simpa only [cmdStep_rules_of_run hsource, cmdStep_rules_of_run hfirst] using hm.rules r
  exact boundary_of_rebuild hp hsub' hnext (hrt.runStep ht) hsound hdesc hrules hreads hlast

/-- Source and target saturations are compared through their final fixed points. -/
theorem Boundary.saturate {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ Cmd.saturate R :: rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hrt : Runtime d) (hsource : CmdStep src (.saturate R) post)
    (htarget : ProgramStep d ((encodeCmd pre.length (.saturate R)).map Command.command) e) :
    Boundary post e := by
  have hnext := hpre.append (ProgramStep.cons hsource .nil)
  have hP' : P = (pre ++ [.saturate R]) ++ rest := by
    simpa only [List.append_assoc, List.singleton_append] using hP
  have hsub' : ∀ c ∈ pre ++ [Cmd.saturate R], c ∈ P :=
    fun c hc => hP' ▸ List.mem_append_left _ hc
  have hR : R ∈ P.saturateRulesets := by rw [hP]; simp [Program.saturateRulesets]
  have hm := metadata_of_prefix hpre htpre
  have hs := cmdStep_saturate_iff.mp hsource
  obtain ⟨mid, hfirst, hrest⟩ := htarget.cons_inv
  obtain ⟨last, hlast, hnil⟩ := hrest.cons_inv
  obtain rfl := hnil.nil_inv
  have ht := cmdStep_saturate_iff.mp hfirst
  have hrules : RulesEncoded P post d := by
    intro r
    simpa only [cmdStep_rules_of_saturate hsource] using hm.rules r
  obtain ⟨hsound, hdesc⟩ := source_saturation_preserves hp hP' hnext hrt
    (h.sound.mono_src hsource.contained.eqs) h.descend hm.sig hrules hs.2 ht.1
  have hmid := hrt.runReach ht.1
  have hrules' : RulesEncoded P post mid := by
    intro r
    simpa only [runReach_rules ht.1] using hrules r
  have hmeta : Metadata P post mid :=
    ⟨(RunReach.sig ht.1).trans hm.sig, hrules', (RunReach.env ht.1).trans hm.env⟩
  have hmidSat : RunSaturated rebuildRuleset mid :=
    ⟨hrules'.rebuild_closed hp hnext hsub' hR ht.2.1, ht.2.2⟩
  have hmidExec := htpre.append (ProgramStep.cons hfirst .nil)
  have hrebuild : Rebuilt mid := rebuilt_of_saturated hmid.noUnions.diag hmid.wf
    (Database.finite_terms hmidExec.finite_from_empty.1) hmidSat
    (hmeta.tablesPresent hp (hsound.viewsSound hmid.noUnions.diag)
      (ctorsIn_of_prefixStep hp hsub' hnext)) (hmeta.uf hp) hmeta.path
    (fun _ _ ho => hdesc.out hmid.noUnions.diag ho)
  have hreads := saturation_reads hp hsub' hnext hs hpre.env ht hrebuild
    hmid.noUnions.diag hsound hmeta.sig hrules' h.reads
  exact boundary_of_rebuild hp hsub' hnext hmid hsound hdesc hrules' hreads hlast

/-- Every original command preserves the boundary relation in the two given executions. -/
theorem Boundary.step {P pre rest : Program} (hp : P.Fragment) {c : Cmd}
    (hP : P = pre ++ c :: rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hs : CmdStep src c post)
    (ht : ProgramStep d ((encodeCmd pre.length c).map Command.command) e) :
    Boundary post e := by
  have hsub : ∀ cmd ∈ pre, cmd ∈ P := fun cmd hm => hP ▸ List.mem_append_left _ hm
  have hmem : c ∈ P := hP ▸ List.mem_append_right _ List.mem_cons_self
  have hcs := (hpre.ctorState Database.CtorState.empty
    (fun cmd hm => hp.ctorsOnly cmd (hsub cmd hm))).sig
  have hrt := prefix_runtime hp hsub htpre
  cases c with
  | decl f dc => exact h.decl hcs (hp.ctorsOnly _ hmem) hs ht
  | rule r => exact h.rule hcs (ruleset_ne_rebuild hp hmem) hs ht
  | check q => exact h.check hs ht
  | action a =>
      obtain ⟨_, hsound, hdesc, hreads, hsat⟩ := encodeAction_command_preserves_of_programStep
        hp hsub hpre hmem hs hrt (metadata_of_prefix hpre htpre) h.sound h.descend h.reads ht
      exact ⟨hsound, hdesc, hreads, hsat⟩
  | run R => exact h.run hp hP hpre htpre hrt hs ht
  | saturate R => exact h.saturate hp hP hpre htpre hrt hs ht

/-- Compose command preservation without requiring either execution to determine the other. -/
theorem Boundary.program {P pre todo rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ todo ++ rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hs : ProgramStep src todo post)
    (ht : ProgramStep d ((encodeCmds todo pre.length).map Command.command) e) :
    Boundary post e := by
  induction todo generalizing pre src d with
  | nil =>
      obtain rfl := hs.nil_inv
      obtain rfl := ht.nil_inv
      exact h
  | cons c cs ih =>
      obtain ⟨mid, hc, hcs⟩ := hs.cons_inv
      have ht' : ProgramStep d ((encodeCmd pre.length c).map Command.command ++
          (encodeCmds cs (pre.length + 1)).map Command.command) e := by
        simpa only [encodeCmds, List.map_append] using ht
      obtain ⟨targetMid, htc, htcs⟩ := ht'.append_inv
      have hPstep : P = pre ++ c :: (cs ++ rest) := by
        simpa only [List.append_assoc, List.cons_append] using hP
      have hnext := h.step hp hPstep hpre htpre hc htc
      apply ih (pre := pre ++ [c]) ?_ (hpre.append (.cons hc .nil))
        (compiled_prefix_step htpre htc) hnext hcs
      · simpa only [List.length_append, List.length_singleton] using htcs
      · simpa only [List.append_assoc, List.singleton_append, List.cons_append,
          List.nil_append] using hP

/-- The relation holds at every pair of corresponding successful mathematical prefixes. -/
theorem boundary_prefix {P pre rest : Program} (hp : P.Fragment) (hP : P = pre ++ rest)
    {src d : Database} (hs : ProgramStep Database.empty pre src)
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d) : Boundary src d := by
  have ht' : ProgramStep Database.empty
      ((encodePrelude P).map Command.command ++ (encodeCmds pre 0).map Command.command) d := by
    simpa only [List.map_append] using ht
  obtain ⟨initial, hi, hr⟩ := ht'.append_inv
  apply Boundary.program (pre := []) hp (by simpa using hP) ProgramStep.nil
    (by simpa [encodeCmds] using hi) (prelude_boundary hi) hs hr

/-- The supported source fragment supplies every query premise at each reached check. -/
theorem checkAgreement {P : Program} (hp : P.Fragment) : CheckAgreement P := by
  intro pre q rest src d hP hs ht
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hmem : Cmd.check q ∈ P := hP ▸ List.mem_append_right _ List.mem_cons_self
  have h := boundary_prefix hp hP hs ht
  have hm := metadata_of_prefix hs ht
  have hdiag := (prefix_noUnions ht).diag
  have hviews := h.sound.viewsSound hdiag
  apply (h.rebuilt hp hsub hs ht).queryHolds_iff hdiag
    (hm.viewDeclared hp hviews (ctorsIn_of_prefixStep hp hsub hs))
    (h.sound.edgesSound hdiag) hviews (hs.wf Database.WF.empty)
    (termsBuild_of_programStep (fun c hc => hp.ctorsOnly c (hsub c hc)) hs)
    (hs.ctorState Database.CtorState.empty (fun c hc => hp.ctorsOnly c (hsub c hc))).sig
    h.reads.terms h.reads.unions (Program.OrderingFree.of_mem hp.noMin hmem)
    (fun p hpat => ((hp.queryEncodable _ hmem).1 p hpat).1)
    (hp.queryEncodable _ hmem).2 ?_ 0
  intro v hv
  apply hp.noAt v
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  exact ⟨Cmd.check q, hmem, hv⟩

end Egglog.Congruence.Abstract

namespace Egglog.Congruence

/-- Congruence compilation preserves success versus check failure whenever both
mathematical executions terminate. No interpreter-correctness theorem is used. -/
theorem preservesObservations : PreservesObservations := by
  intro P _hw hp source target hs ht
  exact observations_of_checkAgreement (Abstract.checkAgreement hp) hs ht

end Egglog.Congruence
