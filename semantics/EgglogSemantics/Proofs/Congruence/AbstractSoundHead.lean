import EgglogSemantics.Proofs.Congruence.AbstractRounds
import EgglogSemantics.Proofs.Congruence.AbstractWrites
import EgglogSemantics.Proofs.Congruence.HeadMatch
import EgglogSemantics.Proofs.Congruence.HeadConditions
import EgglogSemantics.Proofs.Congruence.MetadataSyntax

/-! Every mathematical compiled firing is justified by a source firing. -/

namespace Egglog.Congruence.Abstract

/-- Reconstructing the source match gives the exact values used by the compiled head. -/
theorem encodedRule_firing_sound {src d d' : Database} {r : Rule} {σ : Env}
    (hw : src.WF) (hb : src.TermsBuild) (hcs : src.sig.AllConstructors)
    (hr : d.Diag) (htw : d.WF) (hs : SoundTerms d src) (hdesc : Descending d)
    (hof : ∀ p ∈ r.query, p.OrderingFree)
    (hg : ∀ p ∈ r.query, p.Grounded) (hk : Query.VarsKeyed r.query)
    (hp : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hf : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      d.sig.IsCtor f ↔ src.sig.IsCtor f)
    (hv : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ v ∈ e.vars, v ∈ Query.vars r.query)
    (hd : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true)
    (hmatch : ValidQuerySubst d (encodeRule r).query σ)
    (hfire : evalLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ, ValidQuerySubst src r.query τ ∧ ∀ post,
      evalLocalActions src r.actions τ = some post → SourceSafe post →
        SoundTerms d' post ∧ Descending d' := by
  obtain ⟨τ, hτ, heval⟩ := sourceMatch_evaluations hb (hs.viewsSound hr) hr
    htw.subtermClosed hof hg hk hmatch
  refine ⟨τ, hτ, fun post hpost hsafe => ?_⟩
  obtain ⟨sp, hsp, rfl⟩ := Option.map_eq_some_iff.mp hpost
  obtain ⟨tp, htp, rfl⟩ := Option.map_eq_some_iff.mp hfire
  have hsafe' : SourceSafe sp := by
    simpa only [SourceSafe, Database.terms_setEnvRules] using hsafe
  have htterms : ({d with env := σ ++ d.env} : Database).terms = d.terms :=
    Database.terms_eq_of_eqs_eq rfl
  have hsenv : SoundTerms {d with env := σ ++ d.env} {src with env := τ ++ src.env} :=
    SoundTerms.mono_src (src := src) (src' := {src with env := τ ++ src.env})
      (Set.Subset.refl _) (hs.congr_terms htterms)
  obtain ⟨hsound, hdown⟩ := encodeActions_preserves (hw.appendEnv hτ.mem_terms)
    hsafe' hcs hsenv (hdesc.mono_terms htterms.subset) hp hd huf
    (fun a ha e hem t ht => (heval e (hf a ha e hem) (hv a ha e hem)).trans ht) hsp htp
  have hpterms : ({tp with env := d.env, rules := d.rules} : Database).terms = tp.terms :=
    Database.terms_setEnvRules
  exact ⟨SoundTerms.mono_src (src := sp)
      (src' := {sp with env := src.env, rules := src.rules})
      (Set.Subset.refl _) (hsound.congr_terms hpterms),
    hdown.mono_terms hpterms.subset⟩

/-- Source head conditions ensure that readback yields an actual successful source firing. -/
theorem encodedRule_firing {src d d' : Database} {r : Rule} {σ : Env}
    (hw : src.WF) (hb : src.TermsBuild) (hcs : src.sig.AllConstructors)
    (hnames : ∀ f dc, src.sig f = some dc → ¬ "@".isPrefixOf f)
    (hr : d.Diag) (htw : d.WF) (hs : SoundTerms d src) (hdesc : Descending d)
    (hof : r.OrderingFree) (hg : ∀ p ∈ r.query, p.Grounded) (hk : Query.VarsKeyed r.query)
    (hscoped : Actions.Scoped r.actions (Query.vars r.query))
    (hbuild : Actions.Builds r.actions src.sig) (hrun : Actions.UnionRunnable r.actions src)
    (hctor : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true)
    (hmatch : ValidQuerySubst d (encodeRule r).query σ)
    (hfire : evalLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ post, ValidQuerySubst src r.query τ ∧ evalLocalActions src r.actions τ = some post ∧
      SoundTerms d' post ∧ Descending d' := by
  have hbexpr := builds_exprs hbuild
  obtain ⟨τ, hτ, hsound⟩ := encodedRule_firing_sound hw hb hcs hr htw hs hdesc hof.1 hg hk
    (orderingFree_actionExprs hof.2)
    (fun a ha e hem f hfm =>
      ⟨fun _ => hbexpr a ha e hem f hfm, fun hf => hctor f hf⟩)
    (scoped_exprs hscoped) hd huf hmatch hfire
  have hscope : Actions.Scoped r.actions (Query.bind r.query (Env.dom src.env)) :=
    Actions.Scoped.mono r.actions
      (fun v hv => List.mem_union_iff.mpr (Or.inr hv)) hscoped
  obtain ⟨post, _, hpost⟩ := evalLocalActions_isSome_of_builds (Scope.Models.dom src.env)
    hw hscope hbuild hrun hτ
  refine ⟨τ, _, hτ, hpost, hsound _ hpost ?_⟩
  apply sourceSafe_of_names (evalLocalActions_termsBuild hw hb hcs hτ.mem_terms hpost)
  intro f dc hf
  rw [evalLocalActions_sig hpost] at hf
  exact hnames f dc hf

/-- At a source prefix, all head-side obligations come from the agreed source domain.
The prelude signature supplies constructor coverage; only target execution invariants remain. -/
theorem encodedRule_firing_of_programStep {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src : Database} (hpre : ProgramStep Database.empty pre src)
    {r : Rule} (hmem : Cmd.rule r ∈ P) (hrule : r ∈ src.rules)
    {d d' : Database} {σ : Env} (hi : d.WF) (hn : d.Diag)
    (hs : SoundTerms d src) (hdesc : Descending d)
    (hsig : d.sig = encodeSig P)
    (hmatch : ValidQuerySubst d (encodeRule r).query σ)
    (hfire : evalLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ post, ValidQuerySubst src r.query τ ∧ evalLocalActions src r.actions τ = some post ∧
      SoundTerms d' post ∧ Descending d' := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => by
    rw [hP]; exact List.mem_append_left _ hc
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hdom.ctorsOnly c (hsub c hc))
  have hbuild := headsBuild_of_programStep hdom hP hpre r hrule
  have hrun : Actions.UnionRunnable r.actions src := by
    rcases hdom.noLitUnion with huf | hlit
    · exact Or.inl ((Cmd.ruleUnionFreeB_iff r).mp (huf _ hmem))
    · exact Or.inr ⟨(noLits_of_programStep hdom hlit hsub hpre).terms,
        Cmd.NoLits.of_domain hdom hlit hmem⟩
  apply encodedRule_firing hcs.wf
    (termsBuild_of_programStep (fun c hc => hdom.ctorsOnly c (hsub c hc)) hpre) hcs.sig
    (sourceNames_of_programStep hdom hsub hpre) hn hi hs hdesc
    (Program.OrderingFree.of_mem hdom.noMin hmem)
    (fun p hp => ((hdom.queryEncodable _ hmem).1 p hp).1)
    (hdom.queryEncodable _ hmem).2 (hdom.headsScoped _ hmem) hbuild hrun
    (sourceConstructors_of_programStep hdom hsub hpre hsig) ?_ ?_ hmatch hfire
  · intro a ha e he fk hk
    have hfk : fk ∈ P.ctors := mem_program_ctors hmem
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, actionExprs_ctors he hk⟩))
    rw [hsig, (encodeSig_tables hdom hfk).2]
    rfl
  · rw [hsig, encodeSig_ufName hdom]
    rfl

end Egglog.Congruence.Abstract
