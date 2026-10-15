import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Proofs.Step

namespace Egglog.Provenance.Counterexamples

private def row (n : Int) : Term := .app "T" [.lit (.int n)]

private def constantDecl : FnDecl :=
  ⟨0, 1, some (.merge ["old"] ["new"] [] [.lit (.int 9)]), none⟩

private def base : Database :=
  { Database.empty with sig := fun f => if f = "T" then some constantDecl else none }

private def single : Database := base.addTerm (row 1)

private theorem single_wf : single.WF :=
  (show base.WF from Database.WF.congr Database.WF.empty rfl rfl).addTerm _

private theorem single_normal : MergeNormal single := by
  let entry : Entry := ⟨"T", [], [.lit (.int 1)]⟩
  have hv : entry.Valid base.sig := by
    refine ⟨constantDecl, rfl, by decide, rfl, rfl, ?_⟩
    simp [entry, Entry.columns, Term.IsValue, Term.isValue]
  have only : ∀ e ∈ single.entries, e = entry := by
    intro e he
    rcases Database.mem_addTerm_entries.mp he with he | ⟨he, ht⟩
    · exact he.2.elim
    · exact he.atom_subterm hv ht
  intro a ha b hb _ _
  exact (only a ha).trans (only b hb).symm

private theorem single_lacks_result : row 9 ∉ single.terms := by
  have hempty : base.terms = ∅ :=
    (Database.terms_eq_of_eqs_eq (d₁ := base) (d₂ := Database.empty) rfl).trans Database.empty_terms
  simp [single, Database.addTerm_terms, hempty, row, Term.subterms_app, Term.subterms_lit]

/-- The old merge-fact endpoint claim fails even for a normal one-row mathematical store. -/
theorem single_row_merge_counterexample :
    ∃ (db : Database) (input : Term) (facts : MergeFacts),
      db.WF ∧ MergeNormal db ∧ input ∈ db.terms ∧
      mergeFacts db.sig "T" input input = some facts ∧ facts.result ∉ db.terms := by
  refine ⟨single, row 1, ⟨[], row 9⟩, single_wf, single_normal, ?_, ?_,
    single_lacks_result⟩
  · exact Cong.assert (Or.inr ⟨row 1, Term.self_mem_subterms _, rfl⟩)
  · rfl

end Egglog.Provenance.Counterexamples
