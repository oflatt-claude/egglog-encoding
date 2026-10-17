import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import EgglogSemantics.Spec.Sequential
import EgglogSemantics.Proofs.Writes

/-! Existence of finite normalization and saturation requires actual progress.

A finite equation universe still supplies a maximal equation set, but no longer proves
normalization: destructive changes to current entries can cycle while
equations remain unchanged. The execution theorems below instead require well-founded
progress and totality at reachable states. The generated compiler must prove those
premises for its merge bodies and rules. -/

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

/-- A reachable state with no outgoing work exists when every unfinished state has
an actual successor decreasing a well-founded relation. Only the chosen successor needs
to decrease; arbitrary scheduling is not asserted to terminate. -/
theorem exists_reachable_normal_of_wellFounded {α : Type*}
    (step : α → α → Prop) (normal : α → Prop) (d : α)
    (lt : α → α → Prop) (hwf : WellFounded lt)
    (hprogress : ∀ e, Relation.ReflTransGen step d e → ¬ normal e →
      ∃ e', step e e' ∧ lt e' e) :
    ∃ e, Relation.ReflTransGen step d e ∧ normal e := by
  classical
  have aux : ∀ e, Relation.ReflTransGen step d e →
      ∃ e', Relation.ReflTransGen step e e' ∧ normal e' := by
    intro e
    induction e using hwf.induction with
    | h e ih =>
      intro he
      by_cases hn : normal e
      · exact ⟨e, .refl, hn⟩
      · obtain ⟨mid, hs, hlt⟩ := hprogress e he hn
        obtain ⟨last, hreach, hlast⟩ := ih mid hlt (he.tail hs)
        exact ⟨last, (Relation.ReflTransGen.single hs).trans hreach, hlast⟩
  exact aux d .refl

/-- A principled replacement for the former finite-equation-bound normalization
helper. The hypothesis includes both availability of a merge and well-founded progress
whenever current-entry collisions remain. -/
theorem mergeNormalize_exists_of_wellFounded (d : Database)
    (lt : Database → Database → Prop) (hwf : WellFounded lt)
    (hprogress : ∀ e, MergeClosure d e → ¬ MergeNormal e →
      ∃ e', MergeStep e e' ∧ lt e' e) :
    ∃ e, MergeNormalize d e := by
  obtain ⟨e, hc, hn⟩ :=
    exists_reachable_normal_of_wellFounded MergeStep MergeNormal d lt hwf hprogress
  exact ⟨e, .of_normal hc hn⟩

/-- A natural-number potential is enough when generated merges each
have a strictly decreasing weighted store size. -/
theorem mergeNormalize_exists_of_measure (d : Database) (rank : Database → Nat)
    (hprogress : ∀ e, MergeClosure d e → ¬ MergeNormal e →
      ∃ e', MergeStep e e' ∧ rank e' < rank e) :
    ∃ e, MergeNormalize d e :=
  mergeNormalize_exists_of_wellFounded d (fun e' e => rank e' < rank e)
    (measure rank).wf hprogress

/-- Repeated completed rounds terminate when a round always exists and every round
that changes meaning decreases a well-founded relation. The constructed execution stops
at its first unchanged round, as required by `SaturateReach`. -/
theorem saturateReach_exists_of_wellFounded (R : RulesetName) (d : Database)
    (lt : Database → Database → Prop) (hwf : WellFounded lt)
    (htotal : ∀ e, Relation.ReflTransGen (RunStep R) d e → ∃ e', RunStep R e e')
    (hprogress : ∀ e e', Relation.ReflTransGen (RunStep R) d e →
      RunStep R e e' → ¬ e.SameMeaning e' → lt e' e) :
    ∃ e, SaturateReach R d e := by
  classical
  have aux : ∀ e, Relation.ReflTransGen (RunStep R) d e →
      ∃ e', SaturateReach R e e' := by
    intro e
    induction e using hwf.induction with
    | h e ih =>
      intro he
      obtain ⟨mid, hs⟩ := htotal e he
      by_cases hm : e.SameMeaning mid
      · exact ⟨mid, .done hs hm⟩
      · obtain ⟨last, hlast⟩ := ih mid (hprogress e mid he hs hm) (he.tail hs)
        exact ⟨last, .step hs hm hlast⟩
  exact aux d .refl

/-- Specialization to a natural-number potential on completed rounds. -/
theorem saturateReach_exists_of_measure (R : RulesetName) (d : Database)
    (rank : Database → Nat)
    (htotal : ∀ e, Relation.ReflTransGen (RunStep R) d e → ∃ e', RunStep R e e')
    (hprogress : ∀ e e', Relation.ReflTransGen (RunStep R) d e →
      RunStep R e e' → ¬ e.SameMeaning e' → rank e' < rank e) :
    ∃ e, SaturateReach R d e :=
  saturateReach_exists_of_wellFounded R d (fun e' e => rank e' < rank e)
    (measure rank).wf htotal hprogress

end Egglog
