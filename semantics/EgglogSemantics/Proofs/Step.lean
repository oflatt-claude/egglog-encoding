import EgglogSemantics.Spec.Step
import EgglogSemantics.Proofs.Match

namespace Egglog
@[simp] theorem runProgram_nil {db : Database} : runProgram db [] = some db := rfl

@[simp] theorem runProgram_cons {db : Database} {c : Cmd} {cs : Program} :
    runProgram db (c :: cs) = (stepCmd db c).bind fun db' => runProgram db' cs := rfl

theorem runProgram_append {db : Database} {p q : Program} :
    runProgram db (p ++ q) = (runProgram db p).bind fun db' => runProgram db' q := by
  induction p generalizing db with
  | nil => rfl
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv]
    | some db₁ => simp [hv, ih]

/-! ### Rule results agree with the caller on env and rules

This is what makes `Database.sUnion`'s left bias faithful to the Redex `U_d`: the
operands `(run)` unions all carry the pre-state's environment and rules, so taking
them from the left operand loses nothing. -/
theorem ruleResults_env {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    d.env = db.env :=
  evalLocalActions_env h.choose_spec.2

theorem ruleResults_rules {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    d.rules = db.rules :=
  evalLocalActions_rules h.choose_spec.2

theorem ruleResults_contained {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    db.Contained d :=
  evalLocalActions_contained h.choose_spec.2

theorem ruleResults_wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ ruleResults db r) : d.WF :=
  evalLocalActions_wf hw h.choose_spec.1.mem_terms h.choose_spec.2

/-! ### Steps only add, and preserve well-formedness -/
@[simp] theorem runRules_env {db : Database} : (runRules db).env = db.env := rfl

@[simp] theorem runRules_rules {db : Database} : (runRules db).rules = db.rules := rfl

theorem runRules_contained (db : Database) : db.Contained (runRules db) :=
  Database.Contained.sUnion db _

theorem runRules_wf {db : Database} (hw : db.WF) : (runRules db).WF :=
  hw.sUnion fun _ hd => ruleResults_wf hw hd.choose_spec.2

theorem stepCmd_contained {db db' : Database} {c : Cmd} (h : stepCmd db c = some db') :
    db.Contained db' := by
  cases c with
  | action a => exact evalAction_contained h
  | rule r =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact ⟨subset_rfl, subset_rfl, subset_rfl⟩
  | run =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact runRules_contained db
  | decl f d =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem stepCmd_wf {db db' : Database} (hw : db.WF) {c : Cmd}
    (h : stepCmd db c = some db') : db'.WF := by
  cases c with
  | action a => exact evalAction_wf hw h
  | rule r =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ ⟨hw.subtermClosed, hw.eqsInTerms, hw.envInTerms⟩
  | run =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ runRules_wf hw
  | decl f d =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ ⟨hw.subtermClosed, hw.eqsInTerms, hw.envInTerms⟩

theorem runProgram_contained {db db' : Database} {p : Program}
    (h : runProgram db p = some db') : db.Contained db' := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ .refl db
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [runProgram_cons, hv, Option.bind_some] at h
      exact (stepCmd_contained hv).trans (ih h)

theorem runProgram_wf {db db' : Database} (hw : db.WF) {p : Program}
    (h : runProgram db p = some db') : db'.WF := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hw
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [runProgram_cons, hv, Option.bind_some] at h
      exact ih (stepCmd_wf hw hv) h

theorem run_wf {p : Program} {db : Database} (h : run p = some db) : db.WF :=
  runProgram_wf Database.WF.empty h

@[simp] theorem runRounds_zero {db : Database} : runRounds 0 db = db := rfl

theorem runRounds_succ {n : Nat} {db : Database} :
    runRounds (n + 1) db = runRounds n (runRules db) := rfl

/-- The other way round: a round can be taken last as well as first. -/
theorem runRounds_succ' {n : Nat} {db : Database} :
    runRounds (n + 1) db = runRules (runRounds n db) := by
  induction n generalizing db with
  | zero => rfl
  | succ m ih => rw [runRounds_succ, ih, runRounds_succ]

theorem runRounds_contained (n : Nat) (db : Database) : db.Contained (runRounds n db) := by
  induction n generalizing db with
  | zero => exact .refl db
  | succ n ih => exact (runRules_contained db).trans (ih (runRules db))

theorem runRounds_wf {db : Database} (hw : db.WF) (n : Nat) : (runRounds n db).WF := by
  induction n generalizing db with
  | zero => exact hw
  | succ n ih => exact ih (runRules_wf hw)

@[simp] theorem runRounds_env {n : Nat} {db : Database} : (runRounds n db).env = db.env := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, ih, runRules_env]

@[simp] theorem runRounds_rules {n : Nat} {db : Database} :
    (runRounds n db).rules = db.rules := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, ih, runRules_rules]

/-- Once saturated, every further round changes nothing. -/
theorem Saturated.runRounds_eq {db : Database} (h : Saturated db) (n : Nat) :
    runRounds n db = db := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, h, ih h]

/-- A round that adds nothing means the next round's result is the same database.
This is the stopping condition a saturating schedule tests for. -/
theorem Saturated.runRounds_succ_eq {db : Database} {n : Nat}
    (h : Saturated (runRounds n db)) : runRounds (n + 1) db = runRounds n db := by
  rw [runRounds_succ', h]

/-! ### `runRules` sees a substitution only up to agreement

An executable enumerator emits one substitution per agreement class, where the spec
admits the whole class (`ValidEnv` fixes the domain only up to permutation). This is
what makes those contribute the same databases. -/
theorem ruleResults_of_agree {db : Database} {r : Rule} {σ σ' : Env} (hag : Env.Agree σ σ')
    (hσ' : ValidQuerySubst db r.query σ') {d : Database}
    (hd : evalLocalActions db r.actions σ = some d) : d ∈ ruleResults db r :=
  ⟨σ', hσ', (evalLocalActions_agree r.actions hag).symm.trans hd⟩

/-! ### Equalities survive -/
/-- Nothing a program derives is ever retracted: the semantics only adds terms and
equalities, so `Cong` is monotone along a run. -/
theorem cong_runProgram {db db' : Database} {p : Program} (h : runProgram db p = some db')
    {a b : Term} (hc : Cong db a b) : Cong db' a b :=
  hc.mono (runProgram_contained h)

end Egglog
