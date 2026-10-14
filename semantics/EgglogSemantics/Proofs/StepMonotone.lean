import EgglogSemantics.Proofs.Step

/-! Mathematical commands retain every previously asserted equation. -/

namespace Egglog

/-- **A merge never shrinks the database.**

Constraint (3), discharged by the representation rather than by an argument: the step
adds the combined row beside the two it merged, so there is nothing to overwrite. This
is what lets `Cong.mono`, `Out.mono` and every `WF`-preservation lemma survive into
M9 unchanged. -/
theorem MergeStep.contained {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₁.Contained d₂ := by
  cases h with
  | @collide d f _ as _ _ _ vs _ _ _ _ _ _ _ _ _ _ _ _ hbody _ =>
    have hb : d₁.Contained d := ⟨(evalActions_contained hbody).eqs⟩
    exact ⟨(hb.trans (Database.Contained.addTerm _ d)).eqs⟩

theorem MergeClosure.contained {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₁.Contained d₂ := by
  induction h with
  | refl => exact Database.Contained.refl _
  | tail _ hstep ih => exact ih.trans (MergeStep.contained hstep)

/-- **Every command only adds.**

The formal content of "never delete a term row or a proof row", which the encoding
depends on and which the invariant argument needs: anything the checker reads is
positive in the state, so once true it stays true. `.rule` and `.decl` touch only
fields `Contained` ignores.

`CmdStep` is a `def` now — an effect followed by a merge phase — so the case split is on
the command rather than on the step. -/
theorem RunStep.contained {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db.Contained db' :=
  Database.Contained.trans (Database.Contained.sUnion _ _) (MergeClosure.contained h)

theorem RunReach.contained {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : db.Contained d :=
  RunReach.induction (P := fun x => db.Contained x)
    (fun _ _ hp hs => hp.trans hs.contained) h (Database.Contained.refl _)

theorem CmdStep.contained {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db.Contained db' := by
  obtain ⟨d, hreach, hcl⟩ := h.reach
  refine Database.Contained.trans ?_ (MergeClosure.contained hcl)
  cases c with
  | saturate R => exact RunReach.contained (show SaturateReach R db d from hreach).1
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
