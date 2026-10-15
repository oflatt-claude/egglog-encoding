import EgglogSemantics.Spec.Behavior

namespace Egglog

theorem behaves_success_iff {d : Database} {P : Program} :
    Behaves d P .success ↔ ∃ r, Eval d P r ∧ r.succeeded = true := by
  constructor
  · rintro ⟨e, he⟩; exact ⟨.ok e, he, rfl⟩
  · rintro ⟨r, hr, hb⟩
    cases r with
    | ok e => exact ⟨e, hr⟩
    | checkFailed => contradiction

theorem behaves_failure_iff {d : Database} {P : Program} :
    Behaves d P .checkFailed ↔ ∃ r, Eval d P r ∧ r.succeeded = false := by
  constructor
  · intro h; exact ⟨.checkFailed, h, rfl⟩
  · rintro ⟨r, hr, hb⟩
    cases r with
    | ok e => contradiction
    | checkFailed => exact hr

end Egglog
