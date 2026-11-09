import EgglogSemantics.Proofs.Writes

namespace Egglog

theorem RuleResults.wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ RuleResults db r) : d.WF := by
  obtain ⟨σ, _, hstep⟩ := h
  exact evalActions_wf hw hstep

theorem RunRules.wf {R : List Rule} {db : Database} (hw : db.WF) : (RunRules R db).WF := by
  rw [RunRules.eq_sUnion]
  exact hw.sUnion (fun _ ⟨_, _, hd⟩ => RuleResults.wf hw hd)

theorem runRules_eq_self_iff (R : List Rule) (db : Database) (hdf : ∀ r ∈ R, r.SubsumeFree) :
    RunRules R db = db ↔
      ∀ r ∈ R, ∀ d ∈ RuleResults db r,
        Database.Contained d db := by
  rw [RunRules.eq_sUnion _ _]
  constructor
  · intro h r hr d hd
    rw [← h]
    exact Database.Contained.mem_sUnion ⟨r, hr, hd⟩
  · intro h
    apply Database.ext
    · refine Set.Subset.antisymm ?_ Set.subset_union_left
      rintro p (hp | hp)
      · exact hp
      · obtain ⟨d, ⟨r, hr, hd⟩, hp⟩ := Set.mem_iUnion₂.mp hp
        exact (h r hr d hd).eqs hp
    · refine Set.Subset.antisymm ?_ Set.subset_union_left
      rintro t (ht | ht)
      · exact ht
      · obtain ⟨d, ⟨r, hr, hd⟩, ht⟩ := Set.mem_iUnion₂.mp ht
        exact (h r hr d hd).subsumed ht

/-- Every finite nested schedule preserves well-formedness. -/
theorem Reach.wf {S : Schedule} {db d : Database}
    (h : Reach db S d) (hw : db.WF) : d.WF := by
  induction h with
  | run => exact RunRules.wf hw
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hw)
  | fixpoint _ _ ih => exact ih hw
  | again _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hw)

/-- Subsume-free schedules preserve the entire subsumed set. -/
theorem Reach.subsumed_eq {S : Schedule} {db d : Database}
    (h : Reach db S d) (hdf : ∀ r ∈ S.rules, r.SubsumeFree) :
    d.subsumed = db.subsumed := by
  induction h with
  | run => exact RunRules.subsumed_eq hdf
  | seq _ _ ih₁ ih₂ =>
      exact (ih₂ (fun r hr => hdf r (List.mem_append_right _ hr))).trans
        (ih₁ (fun r hr => hdf r (List.mem_append_left _ hr)))
  | fixpoint _ _ ih => exact ih hdf
  | again _ _ _ ih₁ ih₂ => exact (ih₂ hdf).trans (ih₁ hdf)

/-- A schedule has at most one finite result, even with nested saturation and deletion. -/
theorem Reach.det {S : Schedule} {db d₁ d₂ : Database}
    (h₁ : Reach db S d₁) (h₂ : Reach db S d₂) : d₁ = d₂ := by
  induction h₁ generalizing d₂ with
  | run => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁ h₂ => obtain rfl := ih₁ h₁; exact ih₂ h₂
  | fixpoint _ he ih =>
    cases h₂ with
    | fixpoint h₂ _ => exact ih h₂
    | again h₂ hn _ => exact (hn (ih h₂ ▸ he)).elim
  | again _ hn _ ih₁ ih₂ =>
    cases h₂ with
    | fixpoint h₂ he => exact (hn ((ih₁ h₂).symm ▸ he)).elim
    | again h₂ _ ht => obtain rfl := ih₁ h₂; exact ih₂ ht

/-- Invert saturation into its first body pass and the stopping or repeating case. -/
theorem cmdStep_saturate_iff {S : Schedule} {db db' : Database} :
    Reach db (.saturate S) db' ↔ ∃ d, Reach db S d ∧
      ((db.SameMeaning d ∧ db' = d) ∨ (¬ db.SameMeaning d ∧ Reach d (.saturate S) db')) := by
  constructor
  · intro h
    cases h with
    | fixpoint hp he => exact ⟨_, hp, Or.inl ⟨he, rfl⟩⟩
    | again hp hn ht => exact ⟨_, hp, Or.inr ⟨hn, ht⟩⟩
  · rintro ⟨d, hp, (⟨he, rfl⟩ | ⟨hn, ht⟩)⟩
    · exact .fixpoint hp he
    · exact .again hp hn ht

/-- Invert a sequence at its schedule boundary. -/
theorem Reach.seq_inv {db d' : Database} {S₁ S₂ : Schedule}
    (h : Reach db (.seq S₁ S₂) d') : ∃ d, Reach db S₁ d ∧ Reach d S₂ d' := by
  cases h with | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩

def Term.Mentions (f : FnName) (t : Term) : Prop := ∃ args, Term.app f args ∈ t.subterms

theorem Term.mentions_head (f : FnName) (args : List Term) : Term.Mentions f (.app f args) :=
  ⟨args, Term.self_mem_subterms _⟩

end Egglog
