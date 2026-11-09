import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.DiagonalPreservation

/-! Union-free executable runs have diagonal congruence, including runs with subsumption. -/

namespace Egglog

abbrev Database.EqsRefl := Database.Diag

def FDatabase.EqsRefl (d : FDatabase) : Prop := ∀ p ∈ d.eqs, p.1 = p.2

theorem FDatabase.EqsRefl.toDatabase {d : FDatabase} (h : d.EqsRefl) :
    d.toDatabase.EqsRefl := by
  rintro p (⟨he, _⟩ | ⟨hp, _, _⟩)
  · exact he
  · exact h p hp

/-- No raw equations have been asserted. -/
structure FDatabase.NoUnions (d : FDatabase) : Prop where
  eqs : d.eqs = []

theorem FDatabase.NoUnions.subsume {d : FDatabase} (hn : d.NoUnions) (t : Term) :
    (d.subsume t).NoUnions := ⟨by simpa using hn.eqs⟩

theorem execAction_noUnions {σ : Env} {d d' : FDatabase} {a : Action}
    (hu : a.UnionFree) (hn : d.NoUnions) (h : execAction σ d a = some d') : d'.NoUnions := by
  cases a with
  | expr e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hn.eqs⟩
  | union _ _ => exact hu.elim
  | subsume e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact hn.subsume _

theorem execActions_noUnions {σ : Env} {d d' : FDatabase} {as : List Action}
    (hu : Actions.UnionFree as) (hn : d.NoUnions) (h : execActions σ d as = some d') :
    d'.NoUnions := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact hn
  | cons a as ih =>
    obtain ⟨e, he, ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih hu.2 (execAction_noUnions hu.1 hn he) ht

theorem fireInto_noUnions {r : Rule} {d : FDatabase} {σ : Env}
    (hu : Actions.UnionFree r.actions) (hn : d.NoUnions) :
    (fireInto r d σ).NoUnions := by
  unfold fireInto
  cases h : execActions σ d r.actions with
  | none => exact hn
  | some e => exact execActions_noUnions hu hn h

theorem execRunRules_noUnions {R : List Rule} {d : FDatabase}
    (hn : d.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) :
    (execRunRules R d).NoUnions :=
  execRunRules_induction_ruleset hn
    (fun r hr _ _ _ ha => fireInto_noUnions (hu r hr) ha)

theorem FDatabase.NoUnions.empty : FDatabase.empty.NoUnions := ⟨rfl⟩

theorem FDatabase.NoUnions.toDatabase {d : FDatabase} (hn : d.NoUnions) :
    d.toDatabase.NoUnions :=
  ⟨(show d.EqsRefl by simp [FDatabase.EqsRefl, hn.eqs]).toDatabase⟩

end Egglog
