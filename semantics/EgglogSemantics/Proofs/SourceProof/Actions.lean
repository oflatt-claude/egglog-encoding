import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Proofs.Eval

namespace Egglog.SourceProof

mutual

theorem valueOk_isValue {sig : Signature} : ∀ {t : Term},
    valueOk sig t = true → t.IsValue sig
  | .lit _, _ => rfl
  | .app f args, h => by
      simp only [valueOk, Option.any_eq_true, Bool.and_eq_true_iff, beq_iff_eq] at h
      obtain ⟨d, hd, h⟩ := h
      exact Term.IsValue.app ⟨d, hd, Option.isNone_iff_eq_none.mp h.1.1⟩
        (valuesOk_isValue h.2)

theorem valuesOk_isValue {sig : Signature} : ∀ {ts : List Term},
    valuesOk sig ts = true → ∀ t ∈ ts, t.IsValue sig
  | [], _ => by simp
  | t :: ts, h => by
      simp only [valuesOk, Bool.and_eq_true_iff] at h
      have ht := valueOk_isValue h.1
      have hts := valuesOk_isValue h.2
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ht
      · exact hts u hu

end

def Claim.Holds (db : Database) (c : Claim) : Prop := Cong db c.lhs c.rhs

theorem Claim.Holds.mono {A B : Database} (h : A.Contained B) {c : Claim}
    (hc : c.Holds A) : c.Holds B := Cong.mono h hc

theorem reflClaims_sound {db : Database} {t : Term} {c : Claim}
    (hc : c ∈ reflClaims t) : c.Holds (db.addTerm t) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  exact Cong.assert (Or.inr ⟨s, (Term.mem_subtermList t).mp hs, rfl⟩)

theorem actionFacts_sound {db : Database} {a : Action} {fs : List Claim}
    (h : actionFacts db.sig db.env a = some fs) :
    ∃ d, evalAction db a = some d ∧ ∀ c ∈ fs, c.Holds d := by
  cases a with
  | expr e =>
      simp only [actionFacts, Option.bind_eq_bind] at h
      obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · cases Option.some.inj h
        exact ⟨db.addTerm t, by simp [evalAction, ht], fun _ hc => reflClaims_sound hc⟩
      · contradiction
  | union e₁ e₂ =>
      simp only [actionFacts, Option.bind_eq_bind] at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hok
        simp only [Bool.and_eq_true_iff, Bool.not_eq_true', Bool.or_eq_false_iff] at hok
        cases Option.some.inj h
        refine ⟨db.addEq x y, by simp [evalAction, hx, hy, hok.2.1, hok.2.2], ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Cong.assert (Set.mem_insert _ _)
        rcases List.mem_cons.mp hc with rfl | hc
        · exact (Cong.assert (db := db.addEq x y) (Set.mem_insert _ _)).symm
        rcases List.mem_append.mp hc with hc | hc
        · exact (reflClaims_sound (db := db) hc).mono
            ((Database.Contained.addTerm y _).trans ⟨Set.subset_insert _ _⟩)
        · exact (reflClaims_sound (db := db.addTerm x) hc).mono ⟨Set.subset_insert _ _⟩
      · contradiction

theorem actionsFacts_sound {db : Database} {as : List Action} {fs : List Claim}
    (h : actionsFacts db.sig db.env as = some fs) :
    ∃ d, evalActions db as = some d ∧ ∀ c ∈ fs, c.Holds d := by
  induction as generalizing db fs with
  | nil =>
      cases Option.some.inj h
      exact ⟨db, rfl, by simp⟩
  | cons a as ih =>
      obtain ⟨fs₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨fs₂, h₂, heq⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj heq
      obtain ⟨d₁, hd₁, hf₁⟩ := actionFacts_sound h₁
      have h₂' : actionsFacts d₁.sig d₁.env as = some fs₂ := by
        rw [evalAction_sig hd₁, evalAction_env hd₁]; exact h₂
      obtain ⟨d₂, hd₂, hf₂⟩ := ih h₂'
      refine ⟨d₂, by simp [evalActions, hd₁, hd₂], ?_⟩
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact (hf₁ c hc).mono (evalActions_contained hd₂)
      · exact hf₂ c hc

end Egglog.SourceProof
