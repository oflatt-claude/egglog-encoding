import EgglogSemantics.Spec.Divergence
import EgglogSemantics.Proofs.Step
import Mathlib.Order.WellFounded

namespace Egglog

/-- Divergence splits at a sequence boundary. -/
theorem Diverges.append_iff {p q : Schedule} {d : Database} :
    Diverges d (.seq p q) ↔
      Diverges d p ∨ ∃ mid, Reach d p mid ∧ Diverges mid q := by
  constructor
  · intro h
    cases h with
    | seqLeft h => exact Or.inl h
    | seqRight hs h => exact Or.inr ⟨_, hs, h⟩
  · rintro (h | ⟨mid, hs, h⟩)
    · exact .seqLeft h
    · exact .seqRight hs h

/-- A saturation-free schedule cannot diverge. -/
theorem not_cmdDiverges_of_allConstructors {d : Database} {S : Schedule}
    (hn : S.NoSaturate) : ¬ Diverges d S := by
  intro h
  induction h with
  | seqLeft _ ih => exact ih hn.1
  | seqRight _ _ ih => exact ih hn.2
  | body | later | forever => exact hn.elim

end Egglog
