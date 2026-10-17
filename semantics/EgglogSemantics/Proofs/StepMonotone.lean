import EgglogSemantics.Proofs.Step

/-! Merging preserves value equations while replacing row assertions. -/

namespace Egglog

structure Database.ValueContained (d e : Database) : Prop where
  sig : d.sig = e.sig
  eqs : ∀ p ∈ d.eqs, p.1.IsValue d.sig → p.2.IsValue d.sig → p ∈ e.eqs

theorem Database.ValueContained.refl (d : Database) : d.ValueContained d :=
  ⟨rfl, fun _ hp _ _ => hp⟩

theorem Database.ValueContained.trans {d e f : Database}
    (h : d.ValueContained e) (h' : e.ValueContained f) : d.ValueContained f :=
  ⟨h.sig.trans h'.sig, fun p hp ha hb => h'.eqs p (h.eqs p hp ha hb)
    (h.sig ▸ ha) (h.sig ▸ hb)⟩

theorem MergeStep.valueContained {d e : Database} (h : MergeStep d e) :
    d.ValueContained e := by
  refine ⟨h.sig.symm, ?_⟩
  obtain ⟨old, new, decl, mid, vs, hold, hnew, _, _, _, _, hv, rfl⟩ := mergeStep_iff.mp h
  intro p hp ha _
  have keep (row : Entry) (hr : row.Shape d.sig) : p ≠ (row.atom, row.atom) := by
    intro heq
    exact hr.atom_not_value (by simpa only [heq] using ha)
  have hp' : p ∈ ((d.eraseEntry old).eraseEntry new).eqs := by
    rw [Database.eraseEntry_eqs, Database.eraseEntry_eqs]
    exact Or.inl ⟨Or.inl ⟨hp, keep old hold.1⟩, keep new hnew.1⟩
  exact (Database.Contained.putEntry _ mid).eqs (hv.contained.eqs hp')

theorem MergeClosure.valueContained {d e : Database} (h : MergeClosure d e) :
    d.ValueContained e := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact ih.trans hs.valueContained

theorem RunStep.valueContained {R : RulesetName} {d e : Database}
    (h : RunStep R d e) : d.ValueContained e := by
  exact (show d.ValueContained (RunRules R d) from
    ⟨rfl, fun _ hp _ _ => Or.inl hp⟩).trans h.1.valueContained

theorem RunReach.valueContained {R : RulesetName} {d e : Database}
    (h : Relation.ReflTransGen (RunStep R) d e) : d.ValueContained e :=
  RunReach.induction (P := fun e => d.ValueContained e)
    (fun _ _ hp hs => hp.trans hs.valueContained) h (.refl _)

end Egglog
