import EgglogSemantics.Spec.Step
import EgglogSemantics.Proofs.Query

/-! Finite success and check failure, independent of any executable interpreter. -/

namespace Egglog

@[simp] theorem CmdEval.ok_iff {db db' : Database} {c : Cmd} :
    CmdEval db c (.ok db') ↔ CmdStep db c db' := by
  constructor
  · intro h; cases h with | ok h => exact h
  · exact .ok

@[simp] theorem CmdEval.check_ok_iff {db db' : Database} {q : Query} :
    CmdEval db (.check q) (.ok db') ↔ QueryHolds db q ∧ db' = db :=
  CmdEval.ok_iff

@[simp] theorem CmdEval.check_failed_iff {db : Database} {q : Query} :
    CmdEval db (.check q) .checkFailed ↔ ¬ QueryHolds db q := by
  constructor
  · intro h; cases h with | checkFailed h => exact h
  · exact .checkFailed

/-- A successful result is exactly the pre-existing successful execution judgment. -/
@[simp] theorem Eval.ok_iff {db db' : Database} {p : Program} :
    Eval db p (.ok db') ↔ ProgramStep db p db' := by
  constructor
  · intro h
    generalize hr : Result.ok db' = r at h
    induction h generalizing db' with
    | nil => cases hr; exact .nil
    | cons hc _ ih => exact .cons (CmdEval.ok_iff.mp hc) (ih hr)
    | fail => cases hr
  · intro h
    induction h with
    | nil => exact .nil
    | cons hc _ ih => exact .cons (.ok hc) ih

/-- Passing checks preserve the database and discard their local substitutions. Failing
checks stop without evaluating any command in the suffix. -/
theorem Eval.check_cons_iff {db : Database} {q : Query} {cs : Program} {r : Result} :
    Eval db (.check q :: cs) r ↔
      (QueryHolds db q ∧ Eval db cs r) ∨ (¬ QueryHolds db q ∧ r = .checkFailed) := by
  constructor
  · intro h
    cases h with
    | cons hc ht =>
        obtain ⟨hq, rfl⟩ := CmdEval.check_ok_iff.mp hc
        exact .inl ⟨hq, ht⟩
    | fail hc => exact .inr ⟨CmdEval.check_failed_iff.mp hc, rfl⟩
  · rintro (⟨hq, ht⟩ | ⟨hq, rfl⟩)
    · exact .cons (.ok ⟨hq, rfl⟩) ht
    · exact .fail (.checkFailed hq)

/-- Finite evaluation composes through a successful prefix. -/
theorem Eval.append_of_ok {db mid : Database} {p q : Program} {r : Result}
    (hp : ProgramStep db p mid) (hq : Eval mid q r) : Eval db (p ++ q) r := by
  induction hp with
  | nil => exact hq
  | cons hc _ ih => exact .cons (.ok hc) (ih hq)

/-- A failure remains a failure after appending any suffix. -/
theorem Eval.append_of_failed {db : Database} {p : Program}
    (h : Eval db p .checkFailed) (q : Program) : Eval db (p ++ q) .checkFailed := by
  generalize hr : Result.checkFailed = r at h
  induction h with
  | nil => cases hr
  | cons hc _ ih => exact .cons hc (ih hr)
  | fail hc => exact .fail hc

/-- A terminating concatenation either failed in its prefix or reached its suffix through
a successful prefix. This does not presume that the suffix terminates after a failure. -/
theorem Eval.append_iff {db : Database} {p q : Program} {r : Result} :
    Eval db (p ++ q) r ↔
      (r = .checkFailed ∧ Eval db p .checkFailed) ∨
      ∃ mid, ProgramStep db p mid ∧ Eval mid q r := by
  constructor
  · intro h
    induction p generalizing db with
    | nil => exact Or.inr ⟨db, .nil, h⟩
    | cons c cs ih =>
        cases h with
        | cons hc ht =>
            rcases ih ht with ⟨rfl, hf⟩ | ⟨mid, hp, hq⟩
            · exact Or.inl ⟨rfl, .cons hc hf⟩
            · exact Or.inr ⟨mid, .cons (CmdEval.ok_iff.mp hc) hp, hq⟩
        | fail hc => exact Or.inl ⟨rfl, .fail hc⟩
  · rintro (⟨rfl, hf⟩ | ⟨mid, hp, hq⟩)
    · exact hf.append_of_failed q
    · exact Eval.append_of_ok hp hq

/-- Every failure has a successful prefix and a particular false check. The suffix is
unrestricted, so it need not terminate or even have a successful execution. -/
theorem Eval.failed_iff {db : Database} {p : Program} :
    Eval db p .checkFailed ↔
      ∃ pre q post mid, p = pre ++ .check q :: post ∧
        ProgramStep db pre mid ∧ ¬ QueryHolds mid q := by
  constructor
  · intro h
    generalize hr : Result.checkFailed = r at h
    induction h with
    | nil => cases hr
    | @cons db mid c cs r hc _ ih =>
        obtain ⟨pre, q, post, last, hp, hs, hq⟩ := ih hr
        exact ⟨c :: pre, q, post, last, by simp [hp],
          .cons (CmdEval.ok_iff.mp hc) hs, hq⟩
    | @fail db c cs hc =>
        cases hc with
        | @checkFailed q hq => exact ⟨[], q, cs, db, rfl, .nil, hq⟩
  · rintro ⟨pre, q, post, mid, rfl, hp, hq⟩
    exact Eval.append_of_ok hp (.fail (.checkFailed hq))

/-- Checks are the only semantic failure. A terminating block containing none succeeds. -/
theorem Eval.ok_of_no_checks {db : Database} {p : Program} {r : Result}
    (hp : ∀ q, Cmd.check q ∉ p) (h : Eval db p r) :
    ∃ d, r = .ok d ∧ ProgramStep db p d := by
  cases r with
  | ok d => exact ⟨d, rfl, Eval.ok_iff.mp h⟩
  | checkFailed =>
      obtain ⟨pre, q, post, mid, rfl, _, _⟩ := Eval.failed_iff.mp h
      exact (hp q (by simp)).elim

theorem Eval.append_of_no_checks {db : Database} {p q : Program} {r : Result}
    (hp : ∀ q, Cmd.check q ∉ p) (h : Eval db (p ++ q) r) :
    ∃ mid, ProgramStep db p mid ∧ Eval mid q r := by
  rcases Eval.append_iff.mp h with ⟨_, hf⟩ | hs
  · obtain ⟨_, heq, _⟩ := hf.ok_of_no_checks hp
    cases heq
  · exact hs

/-- An empty conjunction always passes, including in an empty database. -/
theorem QueryHolds.nil (db : Database) : QueryHolds db [] :=
  queryHolds_iff_validQuerySubst.mpr ⟨[], [], .nil, .nil⟩

/-- Query correspondence is enough to compare both outcomes of a check. No equality
between source and target databases is needed. -/
theorem CmdEval.check_observation {src tgt : Database} {q q' : Query} {r s : Result}
    (hq : QueryHolds src q ↔ QueryHolds tgt q')
    (hr : CmdEval src (.check q) r) (hs : CmdEval tgt (.check q') s) :
    r.succeeded = s.succeeded := by
  cases hr with
  | ok hr =>
      cases hs with
      | ok => rfl
      | checkFailed hs => exact (hs (hq.mp hr.1)).elim
  | checkFailed hr =>
      cases hs with
      | ok hs => exact (hr (hq.mpr hs.1)).elim
      | checkFailed => rfl

end Egglog
