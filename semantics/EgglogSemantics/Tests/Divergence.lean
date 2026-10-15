import EgglogSemantics.Proofs.Divergence
import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.LiveTables
import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Spec.Behavior

/-! A merge that restores both conflicting rows really diverges. Failed checks stop first. -/

namespace Egglog.Tests.Divergence

private def zero : Term := .lit (.int 0)
private def one : Term := .lit (.int 1)
private def oldRow : Entry := ⟨"T", [], [zero]⟩
private def newRow : Entry := ⟨"T", [], [one]⟩
private def body : List Action :=
  [.expr (.app "T" [.var "old"]), .expr (.app "T" [.var "new"])]
private def decl : FnDecl :=
  { arity := 0, outArity := 1,
    merge := some (.merge ["old"] ["new"] body [.var "old"]) }
private def base : Database :=
  { Database.empty with sig := fun f => if f = "T" then some decl else none }
private def start : Database := (base.putEntry oldRow).putEntry newRow
private def erased : Database := (start.eraseEntry oldRow).eraseEntry newRow
private def restored : Database := (erased.putEntry oldRow).putEntry newRow

private theorem old_valid : oldRow.Valid start.sig := by
  refine ⟨decl, by simp [start, base, oldRow], by simp [decl], rfl, rfl, ?_⟩
  simp [oldRow, Entry.columns, zero, Term.IsValue, Term.isValue]

private theorem new_valid : newRow.Valid start.sig := by
  refine ⟨decl, by simp [start, base, newRow], by simp [decl], rfl, rfl, ?_⟩
  simp [newRow, Entry.columns, one, Term.IsValue, Term.isValue]

private theorem restore_eq : restored.putEntry oldRow = start := by
  apply Database.ext <;> try rfl
  ext p
  simp [restored, erased, start, base, Database.putEntry, Database.addTerm,
    Database.eraseEntry, Database.empty, oldRow, newRow, Entry.atom, Entry.columns,
    zero, one, Term.subterms_app, Term.subterms_lit]
  tauto

theorem merge_self_loop : MergeStep start start := by
  let ρ := mergeEnv ["old"] ["new"] [zero] [one]
  have hb : evalActions { erased with env := ρ } body =
      some { restored with env := ρ } := by rfl
  have hr : Expr.evalList restored.sig [.var "old"] ρ = some [zero] := by
    simp [Expr.evalList, Expr.eval, ρ, mergeEnv, Option.filter, zero, Term.isValue]
  have hm : MergeValues erased decl [zero] [one] restored [zero] :=
    .changed rfl (by simp [MergeConflict, FnDecl.unchangedWidth, decl, body, zero, one]) hb hr
  have ho : oldRow ∈ start.entries := by
    refine ⟨old_valid, ?_⟩
    exact Or.inl (Or.inr ⟨oldRow.atom, Term.self_mem_subterms _, rfl⟩)
  have hn : newRow ∈ start.entries :=
    ⟨new_valid, Or.inr ⟨newRow.atom, Term.self_mem_subterms _, rfl⟩⟩
  have hs := MergeStep.collide ho hn (by decide +kernel) rfl
    (show start.sig oldRow.name = some decl by simp [start, base, oldRow])
    CongList.nil hm
  change MergeStep start (restored.putEntry oldRow) at hs
  exact restore_eq ▸ hs

theorem merge_diverges : MergeDiverges start :=
  ⟨fun _ => start, rfl, fun _ => merge_self_loop⟩

theorem run_diverges : ProgramDiverges start [.run "R"] := by
  apply ProgramDiverges.head
  apply CmdDiverges.merge (fun _ => by simp) (fun _ => by simp)
    (mid := start) ?_ merge_diverges
  exact (LiveTables.runRules_eq_of_no_rules (by simp [start, base, Database.empty])).symm

private def falseQuery : Query := [.eq (.lit (.int 0)) (.lit (.int 1))]

private theorem start_diag : start.Diag := by
  apply Database.Diag.addTerm (t := newRow.atom)
  apply Database.Diag.addTerm (t := oldRow.atom)
  intro p hp
  exact hp.elim

private theorem false_query : ¬ QueryHolds start falseQuery := by
  rintro ⟨σ, hσ⟩
  have hm := hσ.matches_of_mem (show Pattern.eq (.lit (.int 0)) (.lit (.int 1)) ∈
    falseQuery by simp [falseQuery])
  cases hm with
  | eq _ he₁ he₂ _ he =>
      cases Option.some.inj he₁
      cases Option.some.inj he₂
      have heq := congOn_eq_of_diag start_diag he
      cases heq

theorem failed_check_stops : Eval start [.check falseQuery, .run "R"] .checkFailed :=
  .fail (.checkFailed false_query)

theorem failed_check_does_not_diverge : ¬ ProgramDiverges start [.check falseQuery, .run "R"] := by
  intro h
  cases h with
  | head hc =>
      cases hc with
      | merge hcheck _ _ _ => exact hcheck _ rfl
  | tail hc _ => exact false_query hc.1

theorem divergent_behavior_exists : ∃ d P, Behaves d P .diverges :=
  ⟨start, [.run "R"], run_diverges⟩

theorem finite_wellFormed_divergent_store :
    ∃ d, d.WF ∧ d.FiniteStore ∧ MergeDiverges d := by
  refine ⟨start, ?_, ?_, merge_diverges⟩
  · exact ((Database.WF.empty.congr (d₂ := base) rfl rfl).addTerm oldRow.atom).addTerm
      newRow.atom
  · exact ((Database.FiniteStore.empty.setSig base.sig).putEntry oldRow).putEntry newRow

private theorem first_normal : MergeNormal (base.putEntry oldRow) := by
  have hrows : (base.putEntry oldRow).entries = {oldRow} := by
    rw [Database.putEntry_entries (show oldRow.Valid base.sig from old_valid)]
    simp [base, Database.entries, Database.empty]
  intro a ha b hb _ _
  rw [hrows] at ha hb
  exact (Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm

/-- The loop is reached by ordinary commands from the empty database. -/
theorem divergent_from_empty : ∃ P, ProgramDiverges Database.empty P := by
  refine ⟨[.decl "T" decl, .action (.expr (.app "T" [.lit (.int 0)])),
    .action (.expr (.app "T" [.lit (.int 1)]))], ?_⟩
  apply ProgramDiverges.tail (mid := base)
  · apply CmdStep.of_reach
    · change base = _
      apply Database.ext <;> try rfl
      funext f
      simp [base, Database.empty, Function.update]
    · intro row hr
      exact hr.2.elim
  · apply ProgramDiverges.tail (mid := base.putEntry oldRow)
    · apply CmdStep.of_reach ?_ first_normal
      simp [cmdReach, evalAction, Expr.evalAtom, Expr.evalList, Expr.eval, base, decl,
        FnDecl.entryWidth, oldRow, Entry.atom, Entry.columns, zero, Database.putEntry]
    · apply ProgramDiverges.head
      apply CmdDiverges.merge (mid := start) (fun _ => by simp) (fun _ => by simp)
        ?_ merge_diverges
      simp [cmdReach, evalAction, Expr.evalAtom, Expr.evalList, Expr.eval, base, decl,
        FnDecl.entryWidth, oldRow, newRow, Entry.atom, Entry.columns, zero, one,
        Database.putEntry, start]

end Egglog.Tests.Divergence
