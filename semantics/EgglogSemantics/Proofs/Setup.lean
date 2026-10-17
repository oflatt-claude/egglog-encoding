import EgglogSemantics.Proofs.Step

/-! Data-free mathematical declaration and rule prefixes. -/

namespace Egglog

/-- A prelude command: a declaration or a rule, the two that write no data. -/
def Cmd.DeclOrRule : Cmd → Prop
  | .decl _ _ => True
  | .rule _ => True
  | _ => False


theorem Database.terms_empty_of_eqs_empty {d : Database} (h : d.eqs = ∅) :
    d.terms = ∅ := by
  rw [Database.terms_eq_of_eqs_eq (d₂ := Database.empty) h]
  exact Database.empty_terms

/-- Merges require existing rows, so they cannot create the first data. -/
theorem MergeStep.not_of_empty_eqs {d e : Database} (he : d.eqs = ∅)
    (h : MergeStep d e) : False := by
  obtain ⟨_, _, _, _, _, ho, _, _, _, _, _, _, rfl⟩ := mergeStep_iff.mp h
  have hp := ho.2
  rw [he] at hp
  exact hp

theorem MergeClosure.eq_of_empty_eqs {d e : Database} (he : d.eqs = ∅)
    (h : MergeClosure d e) : e = d := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (hs.not_of_empty_eqs (ih ▸ he)).elim

/-- Declarations and rule registrations leave empty data empty, including their merges. -/
theorem CmdStep.eqs_empty_of_declOrRule {d e : Database} {c : Cmd}
    (h : CmdStep d c e) (hc : c.DeclOrRule) (he : d.eqs = ∅) : e.eqs = ∅ := by
  obtain ⟨m, hm, hcl⟩ := h.reach
  have hme : m.eqs = ∅ := by
    cases c with
    | decl _ _ | rule _ => subst hm; exact he
    | _ => contradiction
  rw [hcl.eq_of_empty_eqs hme]
  exact hme

theorem ProgramStep.eqs_empty_of_declOrRule {d e : Database} {p : Program}
    (h : ProgramStep d p e) (hp : ∀ c ∈ p, c.DeclOrRule) (he : d.eqs = ∅) :
    e.eqs = ∅ := by
  induction h with
  | nil => exact he
  | cons hc _ ih =>
      exact ih (fun c hm => hp c (List.mem_cons_of_mem _ hm))
        (hc.eqs_empty_of_declOrRule (hp _ List.mem_cons_self) he)

end Egglog
