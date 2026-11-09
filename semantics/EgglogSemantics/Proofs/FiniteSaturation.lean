import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import EgglogSemantics.Spec.Facts
import EgglogSemantics.Proofs.Writes

/-! Existence of finite normalization and saturation requires actual progress.

A finite equation universe supplies a maximal reachable equation set, but deleting
and rebuilding rows can cycle within that universe. The execution theorems below
therefore require well-founded progress at reachable states. -/

namespace Egglog

/-- Saturation terminates when every changing round decreases a well-founded relation. -/
theorem saturateReach_exists_of_wellFounded (R : List Rule) (d : Database)
    (lt : Database → Database → Prop) (hwf : WellFounded lt)
    (hprogress : ∀ e, Relation.ReflTransGen (fun a b => b = RunRules R a) d e →
      ¬ e.SameMeaning (RunRules R e) → lt (RunRules R e) e) :
    ∃ e, Reach d (.saturate (.run R)) e := by
  classical
  have aux : ∀ e, Relation.ReflTransGen (fun a b => b = RunRules R a) d e →
      ∃ e', Reach e (.saturate (.run R)) e' := by
    intro e
    induction e using hwf.induction with
    | h e ih =>
      intro he
      by_cases hm : e.SameMeaning (RunRules R e)
      · exact ⟨_, .fixpoint .run hm⟩
      · obtain ⟨last, hlast⟩ := ih _ (hprogress e he hm) (he.tail rfl)
        exact ⟨last, .again .run hm hlast⟩
  exact aux d .refl

theorem saturateReach_exists_of_measure (R : List Rule) (d : Database)
    (rank : Database → Nat)
    (hprogress : ∀ e, Relation.ReflTransGen (fun a b => b = RunRules R a) d e →
      ¬ e.SameMeaning (RunRules R e) → rank (RunRules R e) < rank e) :
    ∃ e, Reach d (.saturate (.run R)) e :=
  saturateReach_exists_of_wellFounded R d (fun e' e => rank e' < rank e)
    (measure rank).wf hprogress

end Egglog
