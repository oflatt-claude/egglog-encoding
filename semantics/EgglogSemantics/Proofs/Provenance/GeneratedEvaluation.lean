import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Proofs.SourceProof.Matching

namespace Egglog.Provenance.Generated

theorem actionFacts_sound {db : Database} {a : Action} {fs : List Term}
    (h : actionFacts db.sig db.env a = some fs) :
    ∃ d, evalAction db a = some d ∧ ∀ t ∈ fs, t ∈ d.terms := by
  cases a with
  | union _ _ => simp [actionFacts] at h
  | expr e =>
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases Option.some.inj h
      refine ⟨db.addTerm t, by simp [evalAction, ht], ?_⟩
      intro s hs
      exact (db.addTerm t).subtermClosed t (Database.mem_addTerm t db)
        ((Term.mem_subtermList t).mp hs)
    · contradiction

theorem actionsFacts_sound {db : Database} {as : List Action} {fs : List Term}
    (h : actionsFacts db.sig db.env as = some fs) :
    ∃ d, evalActions db as = some d ∧ ∀ t ∈ fs, t ∈ d.terms := by
  induction as generalizing db fs with
  | nil => cases Option.some.inj h; exact ⟨db, rfl, by simp⟩
  | cons a as ih =>
    obtain ⟨first, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hr, heq⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj heq
    obtain ⟨d₁, hd₁, hm₁⟩ := actionFacts_sound hf
    have hr' : actionsFacts d₁.sig d₁.env as = some rest := by
      rw [evalAction_sig hd₁, evalAction_env hd₁]; exact hr
    obtain ⟨d₂, hd₂, hm₂⟩ := ih hr'
    refine ⟨d₂, by simp [evalActions, hd₁, hd₂], ?_⟩
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (evalActions_contained hd₂).terms (hm₁ t ht)
    · exact hm₂ t ht

/-- A fact premise is a complete atom, so it is matched by `Expr.evalAtom` rather than by
the source checker's `Expr.eval`; an equality premise is the source checker's. -/
theorem premiseMatches_sound {db : Database} {σ : Env} {p : Pattern} {t : Term}
    (ht : t ∈ db.terms) (h : premiseMatches db.sig σ p t = true) : Matches db p σ := by
  cases p with
  | expr e =>
    simp only [premiseMatches, beq_iff_eq] at h
    exact .expr ht h (StoredCong.mono (Database.Contained.addTerms _ _) ht)
  | eq a b =>
    apply SourceProof.premiseMatches_sound (c := ⟨t, t⟩) (Database.toStored ht)
    simpa [premiseMatches, SourceProof.premiseMatches] using h

theorem premisesMatch_sound {db : Database} {σ : Env} {q : Query} {ts : List Term}
    (ht : ∀ t ∈ ts, t ∈ db.terms) (h : premisesMatch db.sig σ q ts = true) :
    ∀ p ∈ q, Matches db p σ := by
  induction q generalizing ts with
  | nil => simp
  | cons p ps ih =>
    cases ts with
    | nil => simp [premisesMatch] at h
    | cons t ts =>
      simp only [premisesMatch, Bool.and_eq_true_iff] at h
      intro p' hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact premiseMatches_sound (ht t (by simp)) h.1
      · exact ih (fun t ht' => ht t (by simp [ht'])) h.2 p' hp'

theorem actionsFacts_unionFree {sig : Signature} {σ : Env} {as : List Action}
    {fs : List Term} (h : actionsFacts sig σ as = some fs) : Actions.UnionFree as := by
  induction as generalizing fs with
  | nil => trivial
  | cons a as ih =>
      obtain ⟨first, hf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hr, _⟩ := Option.bind_eq_some_iff.mp h
      refine ⟨?_, ih hr⟩
      cases a with
      | expr _ => trivial
      | union _ _ => simp [actionFacts] at hf

end Egglog.Provenance.Generated
