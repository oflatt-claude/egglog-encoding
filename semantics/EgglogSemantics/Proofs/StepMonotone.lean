import EgglogSemantics.Proofs.Step

/-! Mathematical commands retain every previously asserted equation. -/

namespace Egglog

/-- Merging preserves asserted equations even when it replaces current table rows. -/
theorem MergeStep.contained {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₁.Contained d₂ := by
  cases h with
  | @collide d old _ _ vs _ _ _ _ _ _ hv =>
      have hb : d₁.Contained d := ⟨hv.contained.eqs⟩
      exact hb.trans (.putEntry ⟨old.name, old.key, vs⟩ d)

theorem MergeClosure.contained {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₁.Contained d₂ := by
  induction h with
  | refl => exact Database.Contained.refl _
  | tail _ hstep ih => exact ih.trans (MergeStep.contained hstep)

/-- A completed round preserves the equation component, independently of table updates. -/
theorem RunStep.contained {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db.Contained db' :=
  Database.Contained.trans (Database.Contained.sUnion _ _) (MergeClosure.contained h.1)

theorem RunReach.contained {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : db.Contained d :=
  RunReach.induction (P := fun x => db.Contained x)
    (fun _ _ hp hs => hp.trans hs.contained) h (Database.Contained.refl _)

theorem CmdStep.contained {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db.Contained db' := by
  obtain ⟨d, hreach, hcl⟩ := h.reach
  refine Database.Contained.trans ?_ (MergeClosure.contained hcl)
  cases c with
  | saturate R => exact RunReach.contained (show SaturateReach R db d from hreach).reach
  | action a => exact evalAction_contained (hreach)
  | rule r => subst hreach; exact ⟨subset_rfl⟩
  | run R => subst hreach; exact Database.Contained.sUnion _ _
  | decl f dc => subst hreach; exact ⟨subset_rfl⟩
  | check q => rw [hreach.2]; exact .refl _

theorem ProgramStep.contained {db db' : Database} {p : Program}
    (h : ProgramStep db p db') : db.Contained db' := by
  induction h with
  | nil => exact Database.Contained.refl _
  | cons hc _ ih => exact (CmdStep.contained hc).trans ih

end Egglog
