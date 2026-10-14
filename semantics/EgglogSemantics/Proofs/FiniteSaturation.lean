import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import EgglogSemantics.Proofs.StepMonotone

/-! A uniform finite bound on reachable equations supplies an actual finite fixed point.
Finiteness of each individual state alone would not suffice. -/

namespace Egglog

/-- Among states reachable within one finite equation universe, choose a state whose
equations cannot grow further. No finiteness assumption on the state type is needed. -/
theorem exists_reachable_maximal_eqs (step : Database → Database → Prop) (d : Database)
    {bound : Set (Term × Term)} (hf : bound.Finite)
    (hb : ∀ e, Relation.ReflTransGen step d e → e.eqs ⊆ bound) :
    ∃ e, Relation.ReflTransGen step d e ∧
      ∀ e', Relation.ReflTransGen step d e' → e.eqs ⊆ e'.eqs → e'.eqs = e.eqs := by
  let stores : Set (Set (Term × Term)) :=
    {s | ∃ e, Relation.ReflTransGen step d e ∧ s = e.eqs}
  have hfin : stores.Finite := hf.finite_subsets.subset (by
    rintro s ⟨e, he, rfl⟩
    exact hb e he)
  obtain ⟨s, ⟨e, he, rfl⟩, hmax⟩ :=
    Set.exists_max_image stores Set.ncard hfin ⟨d.eqs, d, .refl, rfl⟩
  refine ⟨e, he, fun e' he' hsub => ?_⟩
  exact (Set.eq_of_subset_of_ncard_le hsub
    (hmax e'.eqs ⟨e', he', rfl⟩) (hf.subset (hb e' he'))).symm

/-- A uniform finite bound on generated merge equations guarantees a finite merge
closure ending at a merge fixed point. This is existence, not a bound on all schedules. -/
theorem mergeSaturated_exists_of_finite_bound (d : Database)
    {bound : Set (Term × Term)} (hf : bound.Finite)
    (hb : ∀ e, MergeClosure d e → e.eqs ⊆ bound) :
    ∃ e, MergeClosure d e ∧ MergeSaturated e := by
  obtain ⟨e, he, hmax⟩ := exists_reachable_maximal_eqs MergeStep d hf hb
  refine ⟨e, he, fun e' hs => ?_⟩
  exact Database.ext hs.sig (hmax e' (he.tail hs) hs.contained.eqs)
    hs.envRules.1 hs.envRules.2

/-- If every finite sequence of rounds stays in a common finite equation universe,
there is a finite sequence reaching both rule closure and merge closure. -/
theorem saturateReach_exists_of_finite_bound (R : RulesetName) (d : Database)
    {bound : Set (Term × Term)} (hf : bound.Finite)
    (hb : ∀ e, Relation.ReflTransGen (RunStep R) d e → e.eqs ⊆ bound) :
    ∃ e, SaturateReach R d e := by
  obtain ⟨e, he, hmax⟩ := exists_reachable_maximal_eqs (RunStep R) d hf hb
  have hround : RunStep R e (RunRules R e) := .refl
  have hclosed : RunRules R e = e :=
    Database.ext rfl (hmax _ (he.tail hround) hround.contained.eqs) rfl rfl
  refine ⟨e, he, hclosed, fun e' hs => ?_⟩
  have hstep : RunStep R e e' := by
    change MergeClosure (RunRules R e) e'
    rw [hclosed]
    exact .single hs
  exact Database.ext hs.sig (hmax e' (he.tail hstep) hs.contained.eqs)
    hs.envRules.1 hs.envRules.2

end Egglog
