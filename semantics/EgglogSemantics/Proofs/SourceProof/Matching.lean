import EgglogSemantics.SourceProof.Checker
import EgglogSemantics.Proofs.SourceProof.Ledger

namespace Egglog.SourceProof

theorem premiseMatches_sound {db : Database} {σ : Env} {p : Pattern} {c : Claim}
    (hc : c.Holds db) (h : premiseMatches db.sig σ p c = true) : Matches db p σ := by
  cases p with
  | expr e =>
      simp only [premiseMatches, beq_iff_eq] at h
      exact .expr (eqsInTerms_free hc).1 (Expr.evalAtom_of_eval h)
        (Cong.mono (Database.Contained.addTerms _ _) hc)
  | eq a b =>
      simp only [premiseMatches, Bool.and_eq_true_iff, beq_iff_eq] at h
      exact .eq (eqsInTerms_free hc).1 h.1 h.2
        (Cong.mono (Database.Contained.addTerms _ _) (eqsInTerms_free hc).1)
        (Cong.mono (Database.Contained.addTerms _ _) hc)

theorem premisesMatch_sound {db : Database} {σ : Env} {q : Query} {cs : List Claim}
    (hc : ∀ c ∈ cs, c.Holds db) (h : premisesMatch db.sig σ q cs = true) :
    ∀ p ∈ q, Matches db p σ := by
  induction q generalizing cs with
  | nil => simp
  | cons p ps ih =>
      cases cs with
      | nil => simp [premisesMatch] at h
      | cons c cs =>
          simp only [premisesMatch, Bool.and_eq_true_iff] at h
          intro p' hp'
          rcases List.mem_cons.mp hp' with rfl | hp'
          · exact premiseMatches_sound (hc c (by simp)) h.1
          · exact ih (fun c hc' => hc c (by simp [hc'])) h.2 p' hp'

theorem supportedValue_sound {db : Database} (hw : db.WF) {cs : List Claim}
    (hc : ∀ c ∈ cs, c.Holds db) {t : Term} (ht : supportedValue cs t = true) :
    t ∈ db.terms := by
  simp only [supportedValue, List.any_eq_true, decide_eq_true_eq] at ht
  obtain ⟨c, hcm, hsub⟩ := ht
  rcases hsub with hl | hr
  · exact hw.subtermClosed _ (eqsInTerms_free (hc c hcm)).1
      ((Term.mem_subtermList _).mp hl)
  · exact hw.subtermClosed _ (eqsInTerms_free (hc c hcm)).2
      ((Term.mem_subtermList _).mp hr)

private def selectEnv (vars : List Var) (σ : Env) : Env :=
  vars.filterMap fun v => (Env.lookup v σ).map (v, ·)

private theorem mem_selectEnv {vars : List Var} {σ : Env} {b : Var × Term}
    (h : b ∈ selectEnv vars σ) : b.1 ∈ vars ∧ Env.lookup b.1 σ = some b.2 := by
  obtain ⟨v, hv, hb⟩ := List.mem_filterMap.mp h
  cases hlk : Env.lookup v σ with
  | none => rw [hlk] at hb; simp at hb
  | some t =>
    rw [hlk] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    exact ⟨hb ▸ hv, hb ▸ hlk⟩

private theorem dom_selectEnv_subset {vars : List Var} {σ : Env} :
    Env.dom (selectEnv vars σ) ⊆ vars := fun _ hv =>
  (mem_selectEnv (Env.mem_dom_iff.mp hv).choose_spec).1

private theorem selectEnv_cons_none {v : Var} {vs : List Var} {σ : Env}
    (h : Env.lookup v σ = none) : selectEnv (v :: vs) σ = selectEnv vs σ := by
  simp [selectEnv, h]

private theorem selectEnv_cons_some {v : Var} {vs : List Var} {σ : Env} {t : Term}
    (h : Env.lookup v σ = some t) : selectEnv (v :: vs) σ = (v, t) :: selectEnv vs σ := by
  simp [selectEnv, h]

private theorem dom_selectEnv {vars : List Var} {σ : Env}
    (h : ∀ v ∈ vars, (Env.lookup v σ).isSome) : Env.dom (selectEnv vars σ) = vars := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h v (by simp))
    rw [selectEnv_cons_some ht, Env.dom_cons, ih fun w hw => h w (by simp [hw])]

private theorem lookup_selectEnv {vars : List Var} {σ : Env} (hnd : vars.Nodup) {v : Var}
    (hv : v ∈ vars) : Env.lookup v (selectEnv vars σ) = Env.lookup v σ := by
  induction vars with
  | nil => simp at hv
  | cons w vs ih =>
    rw [List.nodup_cons] at hnd
    cases hlk : Env.lookup w σ with
    | none =>
      rw [selectEnv_cons_none hlk]
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hlk]
        exact Env.lookup_eq_none_iff.mpr fun hc => hnd.1 (dom_selectEnv_subset hc)
      · exact ih hnd.2 hv
    | some t =>
      rw [selectEnv_cons_some hlk, Env.lookup_cons]
      rcases List.mem_cons.mp hv with rfl | hv
      · simp [hlk]
      · rw [if_neg (fun hc : v = w => hnd.1 (hc ▸ hv)), ih hnd.2 hv]

theorem querySubst_of_matches {db : Database} {q : Query} {σ : Env}
    (hdom : (Env.dom σ).Perm q.vars) (hval : ∀ b ∈ σ, b.2 ∈ db.values)
    (hm : ∀ p ∈ q, Matches db p σ) :
    ∃ τ, ValidQuerySubst db q τ ∧ Env.Agree τ σ := by
  have hpvar : ∀ p ∈ q, ∀ v ∈ p.freeVars [], v ∈ Env.dom σ := by
    intro p hp v hv
    exact hdom.mem_iff.mpr (Query.mem_vars.mpr ⟨p, hp, (p.mem_freeVars.mp hv).1⟩)
  have hcanon : ∀ p ∈ q, Env.dom (selectEnv (p.freeVars []) σ) = p.freeVars [] := by
    intro p hp
    exact dom_selectEnv fun v hv => Env.lookup_isSome_iff_mem_dom.mpr (hpvar p hp v hv)
  have hvsub : ∀ p ∈ q, ValidSubst db p (selectEnv (p.freeVars []) σ) := by
    intro p hp
    refine ⟨⟨by rw [hcanon p hp], ?_⟩, (hm p hp).of_agreeOn ?_⟩
    · intro b hb
      exact hval b (Env.mem_of_lookup (mem_selectEnv hb).2)
    · intro v hv
      exact (lookup_selectEnv (p.freeVars_nodup [])
        (p.mem_freeVars.mpr ⟨hv, by simp [Env.dom]⟩)).symm
  obtain ⟨τ, hu, hr⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => selectEnv (p.freeVars []) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact fun _ hb => (mem_selectEnv hb).2)
  refine ⟨τ, ⟨_, List.forall₂_map_self hvsub, hu⟩, Env.agree_of_refines hr ?_⟩
  intro v hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp (hdom.mem_iff.mp hv)
  refine hu.mem_dom_iff.mpr ⟨selectEnv (p.freeVars []) σ, List.mem_map_of_mem hp, ?_⟩
  rw [hcanon p hp]
  exact p.mem_freeVars.mpr ⟨hvp, by simp [Env.dom]⟩

end Egglog.SourceProof
