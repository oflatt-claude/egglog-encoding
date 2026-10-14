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

theorem querySubst_of_matches {db : Database} {q : Query} {σ : Env}
    (hdom : (Env.dom σ).Perm q.vars) (hval : ∀ b ∈ σ, b.2 ∈ db.terms)
    (hm : ∀ p ∈ q, Matches db p σ) :
    ∃ τ, ValidQuerySubst db q τ ∧ Env.Agree τ σ := by
  have hpvar : ∀ p ∈ q, ∀ v ∈ p.freeVars [], v ∈ Env.dom σ := by
    intro p hp v hv
    exact hdom.mem_iff.mpr (Query.mem_vars.mpr ⟨p, hp, (p.mem_freeVars.mp hv).1⟩)
  have hcanon : ∀ p ∈ q, Env.dom (Env.canon (p.freeVars []) σ) = p.freeVars [] := by
    intro p hp
    exact Env.dom_canon fun v hv => Env.lookup_isSome_iff_mem_dom.mpr (hpvar p hp v hv)
  have hvsub : ∀ p ∈ q, ValidSubst db p (Env.canon (p.freeVars []) σ) := by
    intro p hp
    refine ⟨⟨by rw [hcanon p hp], ?_⟩, (hm p hp).of_agreeOn ?_⟩
    · intro b hb
      exact hval b (Env.mem_of_lookup (Env.mem_canon hb).2)
    · intro v hv
      exact (Env.lookup_canon (p.freeVars_nodup [])
        (p.mem_freeVars.mpr ⟨hv, by simp [Env.dom]⟩)).symm
  obtain ⟨τ, hu, hr⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => Env.canon (p.freeVars []) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact Env.refines_canon)
  refine ⟨τ, ⟨_, List.forall₂_map_self hvsub, hu⟩, Env.agree_of_refines hr ?_⟩
  intro v hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp (hdom.mem_iff.mp hv)
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars []) σ, List.mem_map_of_mem hp, ?_⟩
  rw [hcanon p hp]
  exact p.mem_freeVars.mpr ⟨hvp, by simp [Env.dom]⟩

end Egglog.SourceProof
