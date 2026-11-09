import EgglogSemantics.Proofs.Congruence.Diverge
import EgglogSemantics.Proofs.Congruence.Check
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Source.WellFormed

/-! The congruence pass correctness theorem, assembled: from the empty states, which are
related, the simulation gives equal outcomes and equal divergence. -/

namespace Egglog.Congruence

/-- Nothing is congruent in a state without equations. -/
theorem cong_empty_eqs {d : Database} (hd : d.eqs = ∅) {a b : Term} (h : Cong d a b) : False := by
  induction h using Cong.rec (motive_2 := fun _ _ _ => True) with
  | direct hp => rw [hd] at hp; exact hp
  | child _ _ ih => exact ih
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | congr _ _ ih _ => exact ih
  | nil => trivial
  | cons => trivial

theorem keys_empty : Keys Database.empty = ∅ := by
  ext k
  constructor
  · rintro ⟨p, hp⟩
    exact hp
  · intro h
    exact h.elim

/-- The empty states are related. -/
theorem rel_empty : Rel Database.empty Database.empty where
  diag := fun _ hq => hq.elim
  ufOnly := fun _ hq => hq.elim
  finite := Set.finite_empty
  marks := fun _ ht => ht.elim
  down := fun _ _ hr => hr.elim
  selfLoop := fun _ _ hr => hr.elim
  keys := by rw [keys_empty, Database.empty_terms]
  avoids := by intro t ht; rw [Database.empty_terms] at ht; exact ht.elim
  cong := fun a b => ⟨fun h => (cong_empty_eqs rfl h).elim, fun h => (cong_empty_eqs rfl h).elim⟩
  liveCong := fun _ _ hr => hr.elim
  srcSubsumed := rfl

/-- The empty state is canonical. -/
theorem canon_empty : Canon Database.empty where
  unique := fun _ _ _ he _ => (cong_empty_eqs rfl he.1).elim
  root := fun _ _ he => (cong_empty_eqs rfl he.1).elim
  congr := fun _ _ _ _ _ _ _ _ _ _ he _ => (cong_empty_eqs rfl he.1).elim

/-- The compiled program's outcomes and divergence agree with the source's. -/
theorem encode_correct (P : Program) (_hW : P.WellFormed) (hP : P.Fragment) :
    (∀ o : Result, Eval Database.empty (encode P) o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty (encode P).schedule ↔ Diverges Database.empty P.schedule) := by
  have hinv : SrcInv P Database.empty := SrcInv.empty P
  have hrel : RelC P Database.empty Database.empty :=
    ⟨Database.empty, hinv, Database.SameMeaning.refl _, rel_empty, canon_empty⟩
  have hS : P.schedule.rules ⊆ P.rules := fun _ hr => hr
  -- A finite source result and a finite compiled result with related final states agree on
  -- the check.
  have hcheck : ∀ {e d : Database}, SrcInv P e → RelC P e d →
      (QueryHolds e.forgetSubsumed P.check ↔ QueryHolds d.forgetSubsumed (encode P).check) := by
    intro e d he ⟨x, hx, hm, hd, hc⟩
    rw [encode_check, Database.forgetSubsumed_eq_self he.subsumed]
    rw [← check_corr hP hx hd hc]
    exact SourceMeaning.queryHolds_iff he.wf hx.wf hm he.hasReps hx.hasReps hP.noMin.2
  refine ⟨fun o => ?_, ?_⟩
  · cases o with
    | ok =>
      rw [Eval.ok_iff, Eval.ok_iff, encode_schedule]
      constructor
      · rintro ⟨d, hd, hq⟩
        obtain ⟨e, he, hrel'⟩ := bwd_relC hP hS hinv hrel hd
        exact ⟨e, he, (hcheck (hinv.reach hP hS he) hrel').mpr hq⟩
      · rintro ⟨e, he, hq⟩
        obtain ⟨d, hd, hrel'⟩ := fwd_relC hP hS hinv hrel he
        exact ⟨d, hd, (hcheck (hinv.reach hP hS he) hrel').mp hq⟩
    | checkFailed =>
      rw [Eval.failed_iff, Eval.failed_iff, encode_schedule]
      constructor
      · rintro ⟨d, hd, hq⟩
        obtain ⟨e, he, hrel'⟩ := bwd_relC hP hS hinv hrel hd
        exact ⟨e, he, fun h => hq ((hcheck (hinv.reach hP hS he) hrel').mp h)⟩
      · rintro ⟨e, he, hq⟩
        obtain ⟨d, hd, hrel'⟩ := fwd_relC hP hS hinv hrel he
        exact ⟨d, hd, fun h => hq ((hcheck (hinv.reach hP hS he) hrel').mpr h)⟩
  · rw [encode_schedule]
    exact (sim_div hP P.schedule hS hinv hrel).symm

end Egglog.Congruence
