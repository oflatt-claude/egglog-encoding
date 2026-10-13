import EgglogSemantics.Congruence.Match
import EgglogSemantics.Congruence.BuildDescent
import EgglogSemantics.Congruence.Declared
import EgglogSemantics.Encoding.SourceExecution

/-! A compiled rule firing reads a source match and writes only facts justified by
that source rule. Both traversals use the original query. -/

namespace Egglog.Congruence

mutual

/-- **An evaluation transports along `Signature.IsCtor` at the names it applies.** -/
theorem eval_transport {s₁ s₂ : Signature} :
    ∀ (e : Expr) {ρ₁ ρ₂ : Env} {t : Term}, (∀ f ∈ e.fns, s₁.IsCtor f → s₂.IsCtor f) →
      (∀ v ∈ e.vars, Env.lookup v ρ₁ = Env.lookup v ρ₂) → e.eval s₁ ρ₁ = some t →
      e.eval s₂ ρ₂ = some t
  | .lit _, _, _, _, _, _, h => h
  | .var v, _, _, _, _, hv, h => by
      rw [Expr.eval] at h ⊢
      rw [← hv v (by simp [Expr.vars]), h]
  | .app f args, _, _, _, hc, hv, h => by
      have hfn : ∀ g ∈ Expr.fnsList args, s₁.IsCtor g → s₂.IsCtor g :=
        fun g hg => hc g (by simp [Expr.fns, hg])
      have hvl : ∀ v ∈ Expr.varsList args, Env.lookup v _ = Env.lookup v _ :=
        fun w hw => hv w (by simpa [Expr.vars] using hw)
      cases hp : Prim.ofName f with
      | some p =>
        simp only [Expr.eval, hp] at h ⊢
        obtain ⟨ts, hts, hap⟩ := Option.bind_eq_some_iff.mp h
        rw [evalList_transport args hfn hvl hts]
        exact hap
      | none =>
        simp only [Expr.eval, hp] at h ⊢
        by_cases hct : s₁.IsCtor f
        · rw [if_pos hct] at h
          obtain ⟨ts, hts, hap⟩ := Option.map_eq_some_iff.mp h
          rw [if_pos (hc f (by simp [Expr.fns]) hct),
            evalList_transport args hfn hvl hts]
          exact congrArg some hap
        · rw [if_neg hct] at h
          exact absurd h (by simp)

@[inherit_doc eval_transport]
theorem evalList_transport {s₁ s₂ : Signature} :
    ∀ (es : List Expr) {ρ₁ ρ₂ : Env} {ts : List Term},
      (∀ f ∈ Expr.fnsList es, s₁.IsCtor f → s₂.IsCtor f) →
      (∀ v ∈ Expr.varsList es, Env.lookup v ρ₁ = Env.lookup v ρ₂) →
      Expr.evalList s₁ es ρ₁ = some ts → Expr.evalList s₂ es ρ₂ = some ts
  | [], _, _, _, _, _, h => h
  | e :: es, _, _, _, hc, hv, h => by
      rw [Expr.evalList] at h ⊢
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, hcons⟩ := Option.map_eq_some_iff.mp hrest
      rw [eval_transport e (fun g hg => hc g (by simp [Expr.fnsList, hg]))
          (fun w hw => hv w (by simp [Expr.varsList, hw])) ht,
        evalList_transport es (fun g hg => hc g (by simp [Expr.fnsList, hg]))
          (fun w hw => hv w (by simp [Expr.varsList, hw])) hts]
      exact congrArg some hcons

end

/-- The source match preserves every evaluation a scoped rule head performs. Since
source heads have no let-bound globals, only the query's variables need transporting. -/
theorem sourceMatch_evaluations {src tgt : Database} (hb : src.TermsBuild)
    (hs : ViewsSound tgt src) (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hg : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∃ τ, ValidQuerySubst src q τ ∧
      ∀ (e : Expr), (∀ f ∈ e.fns, tgt.sig.IsCtor f ↔ src.sig.IsCtor f) →
        (∀ v ∈ e.vars, v ∈ Query.vars q) →
        e.eval tgt.sig (σ ++ tgt.env) = e.eval src.sig (τ ++ src.env) := by
  obtain ⟨τ, hτ, _, hlookup⟩ := sourceMatch_of_encodedQuery hb hs hd hsc hg hk h
  have hread := patternReads_of_encodeQuery hd hsc hk h
  have henv : ∀ v ∈ Query.vars q,
      Env.lookup v (σ ++ tgt.env) = Env.lookup v (τ ++ src.env) := by
    intro v hv
    obtain ⟨p, hp, hvp⟩ := hk v hv
    obtain ⟨i, hi, _⟩ := mem_terms_of_patternArgVar hs (hread p hp) hvp
    rw [Env.lookup_append_of_some hi, hlookup v hv i hi]
  refine ⟨τ, hτ, fun e hf hv => ?_⟩
  have hvars := fun v hv' => henv v (hv v hv')
  cases ht : e.eval tgt.sig (σ ++ tgt.env) with
  | some t =>
      exact (eval_transport e (fun f hm => (hf f hm).mp) hvars ht).symm
  | none =>
      cases hs : e.eval src.sig (τ ++ src.env) with
      | none => rfl
      | some t =>
          have hback := eval_transport e (fun f hm => (hf f hm).mpr)
            (fun v hm => (hvars v hm).symm) hs
          rw [ht] at hback
          contradiction

/-- An actual compiled firing supplies a source match. If that source head runs, every
retained target entry is justified by its post-state. Source-head totality is separate:
the source fragment rules out unbound variables and literal unions. -/
theorem encodedRule_firing_sound {src : Database} {d d' : FDatabase} {r : Rule} {σ : Env}
    (hw : src.WF) (hb : src.TermsBuild) (hcs : src.sig.AllConstructors)
    (hr : d.EqsRefl) (he : d.EqsInTerms) (hi : d.IndexOk) (hsc : d.SubtermClosed)
    (hs : SoundTerms d src)
    (hg : ∀ p ∈ r.query, p.Grounded) (hk : Query.VarsKeyed r.query)
    (hp : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, Prim.ofName f = none)
    (hf : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      d.sig.IsCtor f ↔ src.sig.IsCtor f)
    (hv : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ v ∈ e.vars, v ∈ Query.vars r.query)
    (hmatch : σ ∈ matchQuery d (encodeRule r).query)
    (hfire : execLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ, ValidQuerySubst src r.query τ ∧ ∀ post,
      evalLocalActions src r.actions τ = some post → SourceSafe post →
        SoundTerms d' post ∧ (MergeShape d.sig → EntryRowsUF d → EntryRowsUF d') ∧
      (UFTermsDescend d → UFTermsDescend d') := by
  obtain ⟨σ', hσ', hagree⟩ := validQuerySubst_of_mem_matchQuery_diag he hr hi hmatch
  obtain ⟨τ, hτ, heval⟩ := sourceMatch_evaluations hb
    (viewsSound_of_soundTerms hr hs).1 hr.toDatabase
    (fun t ht s hst => by
      rw [Egglog.FDatabase.toDatabase_terms] at ht ⊢
      exact hsc t ht s ((Term.mem_subtermList t).mpr hst)) hg hk hσ'
  refine ⟨τ, hτ, fun post hpost hsafe => ?_⟩
  obtain ⟨sp, hsp, rfl⟩ := Option.map_eq_some_iff.mp hpost
  obtain ⟨tp, htp, rfl⟩ := Option.map_eq_some_iff.mp hfire
  have hsafe' : SourceSafe sp := by simpa only [SourceSafe, Database.terms_setEnvRules] using hsafe
  have hsenv : SoundTerms { d with env := σ ++ d.env }
      { src with env := τ ++ src.env } :=
    SoundTerms.mono_src (src := src) (src' := { src with env := τ ++ src.env })
      (Set.Subset.refl _) hs
  have hvalues : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a,
      e.eval d.sig (σ ++ d.env) = e.eval src.sig (τ ++ src.env) := by
    intro a ha e hem
    rw [← Expr.eval_agree (hagree.append_right d.env) e]
    exact heval e (hf a ha e hem) (hv a ha e hem)
  have hsound := encodeActions_soundTerms (hw.appendEnv hτ.mem_terms)
    hsafe' hcs hp hvalues hsenv hsp htp
  refine ⟨SoundTerms.mono_src (src := sp)
    (src' := { sp with env := src.env, rules := src.rules }) (Set.Subset.refl _) hsound, ?_⟩
  constructor
  · intro hshape hhistory
    exact encodeActions_entryRowsUF (d := { d with env := σ ++ d.env }) (d' := tp)
      (hw.appendEnv hτ.mem_terms) hsafe' hcs hp hvalues hshape hhistory hsp htp
  · intro hdes
    exact encodeActions_ufTermsDescend (d := { d with env := σ ++ d.env }) (d' := tp)
      (hw.appendEnv hτ.mem_terms) hsafe' hcs hp hvalues hdes hsp htp

private theorem builds_exprs {sig : Signature} {as : List Action}
    (h : Actions.Builds as sig) : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.Evaluable sig := by
  induction as with
  | nil => simp
  | cons a as ih =>
      intro b hb e he
      rcases List.mem_cons.mp hb with rfl | hb
      · cases b with
        | expr x => obtain rfl := List.mem_singleton.mp he; exact h.1
        | union x y =>
            rcases List.mem_cons.mp he with rfl | he
            · exact h.1.1
            · obtain rfl := List.mem_singleton.mp he; exact h.1.2
      · exact ih h.2 b hb e he

private theorem scoped_exprs {Γ : Scope} {as : List Action}
    (h : Actions.Scoped as Γ) : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ v ∈ e.vars, v ∈ Γ := by
  induction as with
  | nil => simp
  | cons a as ih =>
      intro b hb e he
      rcases List.mem_cons.mp hb with rfl | hb
      · cases b with
        | expr x => obtain rfl := List.mem_singleton.mp he; exact h.1.2
        | union x y =>
            rcases List.mem_cons.mp he with rfl | he
            · exact h.1.1
            · obtain rfl := List.mem_singleton.mp he; exact h.1.2
      · exact ih h.2 b hb e he

/-- Every compiled firing is justified by an actual source firing. The source-domain
head conditions ensure that the reconstructed match runs successfully, rather than
assuming the existence of a convenient source post-state. -/
theorem encodedRule_firing {src : Database} {d d' : FDatabase} {r : Rule} {σ : Env}
    (hw : src.WF) (hb : src.TermsBuild) (hcs : src.sig.AllConstructors)
    (hnames : ∀ f dc, src.sig f = some dc → ¬ "@".isPrefixOf f)
    (hr : d.EqsRefl) (he : d.EqsInTerms) (hi : d.IndexOk) (hsc : d.SubtermClosed)
    (hs : SoundTerms d src)
    (hg : ∀ p ∈ r.query, p.Grounded) (hk : Query.VarsKeyed r.query)
    (hscoped : Actions.Scoped r.actions (Query.vars r.query))
    (hbuild : Actions.Builds r.actions src.sig) (hrun : Actions.UnionRunnable r.actions src)
    (hctor : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    (hmatch : σ ∈ matchQuery d (encodeRule r).query)
    (hfire : execLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ post, ValidQuerySubst src r.query τ ∧ evalLocalActions src r.actions τ = some post ∧
      SoundTerms d' post ∧ (MergeShape d.sig → EntryRowsUF d → EntryRowsUF d') ∧
      (UFTermsDescend d → UFTermsDescend d') := by
  have hbexpr := builds_exprs hbuild
  obtain ⟨τ, hτ, hsound⟩ := encodedRule_firing_sound hw hb hcs hr he hi hsc hs hg hk
    (fun a ha e hem f hfm => (hbexpr a ha e hem f hfm).1)
    (fun a ha e hem f hfm =>
      ⟨fun _ => (hbexpr a ha e hem f hfm).2,
        fun hf => hctor f hf⟩) (scoped_exprs hscoped) hmatch hfire
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
theorem encodedRule_firing_of_programStep {P pre rest : Program} (hdom : P.EncodeDomain)
    (hP : P = pre ++ rest) {src : Database} (hpre : ProgramStep Database.empty pre src)
    {r : Rule} (hmem : Cmd.rule r ∈ P) (hrule : r ∈ src.rules)
    {d d' : FDatabase} {σ : Env} (hi : d.Inv) (hn : d.NoUnions) (hs : SoundTerms d src)
    (hsig : d.sig = encodeSig P)
    (hmatch : σ ∈ matchQuery d (encodeRule r).query)
    (hfire : execLocalActions d (encodeRule r).actions σ = some d') :
    ∃ τ post, ValidQuerySubst src r.query τ ∧ evalLocalActions src r.actions τ = some post ∧
      SoundTerms d' post ∧ (MergeShape d.sig → EntryRowsUF d → EntryRowsUF d') ∧
      (UFTermsDescend d → UFTermsDescend d') := by
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
  exact encodedRule_firing hcs.wf
    (termsBuild_of_programStep (fun c hc => hdom.ctorsOnly c (hsub c hc)) hpre) hcs.sig
    (sourceNames_of_programStep hdom hsub hpre) hn.eqsRefl hi.eqs hi.index
    (Egglog.FDatabase.SubtermClosed.of_wf hi.wf) hs
    (fun p hp => ((hdom.queryEncodable _ hmem).1 p hp).1)
    (hdom.queryEncodable _ hmem).2 (hdom.headsScoped _ hmem) hbuild hrun
    (sourceConstructors_of_programStep hdom hsub hpre hsig) hmatch hfire

end Egglog.Congruence
