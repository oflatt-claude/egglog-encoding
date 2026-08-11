import EgglogSemantics.Spec.Step

/-!
# Nothing in the `eqs`-only design is dischargeable by reflexivity

Scratch, not part of the library. `Cong` lost its `refl` rule, so the guards that used to
read "the witness is one of the database's own terms" have to be rechecked: a term is now
present exactly when an equation says so, and `Database.empty` says nothing.
-/

namespace Egglog
namespace Scratch

/-- **Nothing exists by default.** No equations, no terms: `Cong` is not secretly
reflexive. -/
theorem not_cong_of_no_eqs {db : Database} (h : db.eqs = ∅) {a b : Term} :
    ¬ Cong db a b := by
  intro hc
  induction hc using Cong.rec (motive_2 := fun _ _ _ => True) with
  | assert hab => rw [h] at hab; exact absurd hab (Set.notMem_empty _)
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | congr _ _ _ ih _ _ => exact ih
  | nil => trivial
  | cons => trivial

theorem empty_terms : Database.empty.terms = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ht => not_cong_of_no_eqs rfl ht

/-- The other direction: `addTerm` records what it is given, subterms included. -/
theorem mem_addTerm {db : Database} {t s : Term} (h : s ∈ t.subterms) :
    s ∈ (db.addTerm t).terms := Cong.assert (Or.inr ⟨s, h, rfl⟩)

/-- **`Matches` still says something.** The witness must be a term the database already
holds, and `withOperands` cannot supply one. -/
theorem not_matches_empty {p : Pattern} {σ : Env} : ¬ Matches Database.empty p σ := by
  intro h
  cases h with
  | expr hw _ _ => exact not_cong_of_no_eqs rfl hw
  | eq hw _ _ _ _ => exact not_cong_of_no_eqs rfl hw
  | values hw _ _ _ => exact not_cong_of_no_eqs rfl hw

/-- **`Recorded` still says something.** `withOperands` makes both sides of `p` self-equal,
but the witness `q` has to be one of `d₂`'s own equations. -/
theorem recorded_empty {d : Database} (h : d.Recorded Database.empty) : d.eqs = ∅ :=
  Set.eq_empty_of_forall_notMem fun p hp =>
    absurd (h.eqs p hp).choose_spec.1 (Set.notMem_empty _)

/-- **`MergeStep` still says something**, and so `Database.empty` is `MergeSaturated`
vacuously rather than by a step that changes nothing. -/
theorem not_mergeStep_empty (db' : Database) : ¬ MergeStep Database.empty db' := by
  intro h
  cases h with
  | collide _ _ _ _ hmem _ _ _ _ => exact not_cong_of_no_eqs rfl hmem

end Scratch
end Egglog
