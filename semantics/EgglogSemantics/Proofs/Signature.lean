import EgglogSemantics.Proofs.Merge
import EgglogSemantics.Proofs.Step
/-! Signature lookup through command sequences. -/

namespace Egglog

/-- A declaration repeated with the same definition preserves a known signature entry. -/
theorem foldl_sigBind_preserve {f : FnName} {dc : FnDecl} : ∀ (p : Program),
    (∀ dc', Cmd.decl f dc' ∈ p → dc' = dc) → ∀ {sig : Signature}, sig f = some dc →
      (p.foldl (fun s c => c.sigBind s) sig) f = some dc := by
  intro p
  induction p with
  | nil => intro _ _ h; exact h
  | cons c cs ih =>
      intro hp sig hs
      apply ih (fun dc' h => hp dc' (List.mem_cons_of_mem c h))
      cases c with
      | decl g dg =>
          by_cases hg : g = f
          · subst g
            rw [hp dg List.mem_cons_self]
            simp [Cmd.sigBind]
          · simpa [Cmd.sigBind, Function.update_of_ne (Ne.symm hg)] using hs
      | _ => exact hs

/-- Read a declaration from a program whose other declarations of this name agree. -/
theorem foldl_sigBind_found {f : FnName} {dc : FnDecl} : ∀ (p : Program),
    Cmd.decl f dc ∈ p → (∀ dc', Cmd.decl f dc' ∈ p → dc' = dc) →
    ∀ (sig : Signature), (p.foldl (fun s c => c.sigBind s) sig) f = some dc := by
  intro p
  induction p with
  | nil => simp
  | cons c cs ih =>
      intro hm hp sig
      rcases List.mem_cons.mp hm with rfl | hm
      · exact foldl_sigBind_preserve cs
          (fun dc' h => hp dc' (List.mem_cons_of_mem _ h)) (by simp [Cmd.sigBind])
      · exact ih hm (fun dc' h => hp dc' (List.mem_cons_of_mem c h)) _

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

/-- A source signature entry comes from the initial signature or an actual declaration. -/
theorem ProgramStep.declared {d e : Database} {p : Program} (h : ProgramStep d p e)
    {f : FnName} {dc : FnDecl} (hf : e.sig f = some dc) :
    d.sig f = some dc ∨ Cmd.decl f dc ∈ p := by
  induction h with
  | nil => exact Or.inl hf
  | @cons d m e c cs hc _ ih =>
      rcases ih hf with hm | hm
      · rw [hc.sig] at hm
        cases c with
        | decl g dg =>
            by_cases hg : f = g
            · subst g
              rw [Cmd.sigBind, Function.update_self, Option.some.injEq] at hm
              subst dg
              exact Or.inr List.mem_cons_self
            · rw [Cmd.sigBind, Function.update_of_ne hg] at hm
              exact Or.inl hm
        | action a => exact Or.inl hm
        | rule r => exact Or.inl hm
        | run R => exact Or.inl hm
        | saturate R => exact Or.inl hm
        | check _ => exact Or.inl hm
      · exact Or.inr (List.mem_cons_of_mem c hm)

end Egglog
