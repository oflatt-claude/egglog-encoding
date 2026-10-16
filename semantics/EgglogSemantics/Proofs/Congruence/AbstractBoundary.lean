import EgglogSemantics.Proofs.Congruence.AbstractSoundRounds
import EgglogSemantics.Proofs.Congruence.LiveRead
import EgglogSemantics.Proofs.Congruence.UFCoverage

/-! Data invariants at boundaries between original source commands. -/

namespace Egglog

/-- Completed command phases retain merge normality, including unchanged checks. -/
theorem CmdStep.mergeNormal {d e : Database} {c : Cmd} (h : CmdStep d c e)
    (hn : MergeNormal d) : MergeNormal e := by
  cases c with
  | check q => obtain ⟨_, rfl⟩ := h; exact hn
  | decl | rule | run | saturate => exact h.choose_spec.2.2

theorem ProgramStep.mergeNormal {d e : Database} {p : Program}
    (h : ProgramStep d p e) (hn : MergeNormal d) : MergeNormal e := by
  induction h with
  | nil => exact hn
  | cons hc _ ih => exact ih (hc.mergeNormal hn)

namespace Congruence.Abstract

/-- The relation maintained between corresponding successful command prefixes. -/
structure Boundary (src d : Database) : Prop where
  sound : SoundTerms d src.completion
  descend : Descending d
  reads : Live.Reads d src
  rebuilt : Rebuilt d
  total : Live.UFTotal d

theorem prelude_boundary {P : Program} {d : Database} (hp : P.Fragment)
    (ht : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) :
    Boundary Database.empty d := by
  obtain ⟨_, hterms, _⟩ := Live.prelude_empty ht
  have hr := Live.prelude_runtime hp ht
  have hnone {f : FnName} {cs vs : List Term} (ho : d.Out f cs vs) : False := by
    have hm := ho.term hr.noUnions.diag
    simp only [hterms, Set.mem_empty_iff_false] at hm
  have hfinite : d.terms.Finite := hterms ▸ Set.finite_empty
  refine ⟨?_, ?_, ?_, ⟨hr.wf, hfinite, ?_, ?_⟩,
    Live.prelude_ufTotal ht⟩
  · constructor <;> intros <;> simp_all
  · intro a b hm
    simp [hterms] at hm
  · constructor
    · intro t ht
      simp at ht
    · intro a b hab _
      cases hab
  · constructor
    · intro a b c ho _; exact (hnone ho).elim
    · intro a b c ho _; exact (hnone ho).elim
    · intro f cs a b ho _; exact (hnone ho).elim
    · intro f cs a b ho _; exact (hnone ho).elim
    · intro f cs ds e ho _; exact (hnone ho).elim
  · intro a b ho; exact (hnone ho).elim

end Congruence.Abstract
end Egglog
