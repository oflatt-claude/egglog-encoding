import EgglogSemantics.Proofs.Merge
import EgglogSemantics.Proofs.SignatureLookup
/-! Signature lookup through command sequences. -/

namespace Egglog

theorem FDatabase.execProgramM_sig {p : Program} : ∀ {d d' : FDatabase},
    d.execProgramM p = some d' → d'.sig = p.foldl (fun sig c => c.sigBind sig) d.sig := by
  induction p with
  | nil =>
    intro d d' hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ rfl
  | cons c cs ih =>
    intro d d' hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [ih h₂, execCmdM_sig h₁]
    rfl

end Egglog
