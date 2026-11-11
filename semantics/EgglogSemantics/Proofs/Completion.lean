import EgglogSemantics.Proofs.SourceMeaning

/-! A proof-only completion records exactly the facts already inferred. -/

namespace Egglog

open InferredFacts

/-- This may be infinite; operational executions still use the original database. -/
def Database.completion (d : Database) : Database :=
  {d with eqs := {p | d.Infers p.1 p.2}}

theorem Database.contained_completion (d : Database) : d.Contained d.completion :=
  ⟨fun _ hp => infers_of_cong (.direct hp), subset_rfl⟩

theorem Database.cong_completion_iff {d : Database} (hw : d.WF) {a b : Term} :
    StoredCong d.completion a b ↔ d.Infers a b := by
  refine ⟨fun hc => ?_, fun hi => .direct hi⟩
  exact infers_of_assertions_only (e := d.completion) hw (fun _ hp => hp)
    (infers_of_cong hc)

theorem Database.WF.completion {d : Database} (hw : d.WF) : d.completion.WF where
  litsIsolated := fun _ hp hl => infers_eq_of_isLit hw hp hl

theorem Database.sameMeaning_completion {d : Database} (hw : d.WF) :
    d.SameMeaning d.completion :=
  Database.SameMeaning.of_inferred rfl (fun _ _ => ⟨infers_mono d.contained_completion,
    infers_of_assertions_only (e := d.completion) hw (fun _ hp => hp)⟩)

end Egglog
