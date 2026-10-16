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
private def prepared : Database := (base.addTerm zero).addTerm one
private def start : Database := (prepared.putEntry oldRow).putEntry newRow
private def erased : Database := (start.eraseEntry oldRow).eraseEntry newRow
private def restored : Database := (erased.putEntry oldRow).putEntry newRow

private theorem old_valid : oldRow.Valid start.sig := by
  refine ⟨decl, by simp [start, prepared, base, oldRow], by simp [decl], rfl, rfl, ?_⟩
  simp [oldRow, Entry.columns, zero, Term.IsValue, Term.isValue]

private theorem new_valid : newRow.Valid start.sig := by
  refine ⟨decl, by simp [start, prepared, base, newRow], by simp [decl], rfl, rfl, ?_⟩
  simp [newRow, Entry.columns, one, Term.IsValue, Term.isValue]

private theorem restore_eq : restored.putEntry oldRow = start := by
  apply Database.ext <;> try rfl
  ext p
  simp [restored, erased, start, prepared, base, Database.putEntry, Database.addTerm,
    Database.eraseEntry, Database.empty, oldRow, newRow, Entry.atom, Entry.columns,
    zero, one]
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
    exact Or.inr (Or.inl rfl)
  have hn : newRow ∈ start.entries :=
    ⟨new_valid, Or.inl rfl⟩
  have hs := MergeStep.collide ho hn (by decide +kernel) rfl
    (show start.sig oldRow.name = some decl by simp [start, prepared, base, oldRow])
    CongList.nil hm
  change MergeStep start (restored.putEntry oldRow) at hs
  exact restore_eq ▸ hs

theorem merge_diverges : MergeDiverges start :=
  ⟨fun _ => start, rfl, fun _ => merge_self_loop⟩

theorem run_diverges : ProgramDiverges start [.run "R"] := by
  apply ProgramDiverges.head
  apply CmdDiverges.merge (fun _ => by simp) (fun _ => by simp)
    (mid := start) ?_ merge_diverges
  exact (LiveTables.runRules_eq_of_no_rules
    (by simp [start, prepared, base, Database.empty])).symm

private def falseQuery : Query := [.eq (.lit (.int 0)) (.lit (.int 1))]

private theorem start_diag : start.Diag := by
  apply Database.Diag.addTerm (t := newRow.atom)
  apply Database.Diag.addTerm (t := oldRow.atom)
  apply Database.Diag.addTerm (t := one)
  apply Database.Diag.addTerm (t := zero)
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
  · have hw : prepared.WF :=
      ((Database.WF.empty.congr (d₂ := base) rfl rfl).addTerm zero).addTerm one
    exact (hw.addTerm oldRow.atom).addTerm newRow.atom
  · have hf : prepared.FiniteStore :=
      ((Database.FiniteStore.empty.setSig base.sig).addTerm zero).addTerm one
    exact (hf.putEntry oldRow).putEntry newRow

private def seed : Rule :=
  ⟨[], [.expr (.lit (.int 0)), .expr (.lit (.int 1)),
    .expr (.app "T" [.lit (.int 0)]), .expr (.app "T" [.lit (.int 1)])], "seed"⟩
private def registered : Database := { base with rules := {seed} }
private def seeded : Database := { start with rules := {seed} }

private theorem seed_eval : evalLocalActions registered seed.actions [] = some seeded := rfl

private theorem seed_run : RunRules "seed" registered = seeded := by
  have hresults : {d | ∃ r ∈ registered.rules, r.ruleset = "seed" ∧
      d ∈ RuleResults registered r} = {seeded} := by
    ext d
    constructor
    · rintro ⟨r, hr, _, σ, hσ, he⟩
      have hr : r = seed := by simpa [registered] using hr
      subst r
      have hσ : σ = [] := ValidQuerySubst.nil_iff.mp hσ
      subst σ
      rw [seed_eval] at he
      exact (Option.some.inj he).symm
    · intro hd
      obtain rfl := Set.mem_singleton_iff.mp hd
      exact ⟨seed, by simp [registered], rfl, [],
        ValidQuerySubst.nil_iff.mpr rfl, seed_eval⟩
  unfold RunRules
  rw [hresults]
  apply Database.ext <;> try rfl
  simp [Database.sUnion, registered, base, Database.empty]

/-- An empty-query rule reaches the loop in an ordinary run from the empty database. -/
theorem divergent_from_empty : ∃ P, ProgramDiverges Database.empty P := by
  refine ⟨[.decl "T" decl, .rule seed, .run "seed"], ?_⟩
  apply ProgramDiverges.tail (mid := base)
  · apply CmdStep.of_reach
    · change base = _
      apply Database.ext <;> try rfl
      funext f
      simp [base, Database.empty, Function.update]
    · intro row hr
      exact hr.2.elim
  · apply ProgramDiverges.tail (mid := registered)
    · apply CmdStep.of_reach
      · change registered = _
        simp [registered, base, Database.empty]
      · intro row hr
        exact hr.2.elim
    · apply ProgramDiverges.head
      apply CmdDiverges.merge (d := registered) (c := .run "seed") (mid := seeded)
        (fun _ => by simp) (fun _ => by simp) seed_run.symm
      exact ⟨fun _ => seeded, rfl, fun _ => merge_self_loop.setRules {seed}⟩

end Egglog.Tests.Divergence
