import EgglogSemantics.Proofs.Query

namespace Egglog.Tests.SemanticCong

private def a : Term := .app "a" []
private def b : Term := .app "b" []
private def f (t : Term) : Term := .app "f" [t]
private def d : Database := (Database.empty.addEq a b).addTerm (f a)

/-- Congruence represents a spelling absent from the stored subterms. -/
theorem alternate_spelling : Cong d (f a) (f b) := by
  apply Cong.congr (.direct (Set.mem_insert _ _))
  exact .cons (.direct (Or.inr (Set.mem_insert _ _))) .nil

theorem alternate_not_stored : f b ∉ d.terms := by
  simp [d, Database.addTerm_terms, Database.addEq_terms, a, b, f, Term.subterms_app]

private def cyclic : Database := Database.empty.addEq a (f a)

/-- A cycle can represent arbitrarily nested spellings without growing the binding domain. -/
theorem nested_represented : Cong cyclic (f (f a)) (f (f a)) := by
  have h : Cong cyclic a (f a) := .direct (Set.mem_insert _ _)
  have hf : Cong cyclic (f a) (f (f a)) := .congr (h.symm.trans h) (.cons h .nil)
  exact hf.symm.trans hf

theorem nested_not_stored : f (f a) ∉ cyclic.terms := by
  simp [cyclic, Database.addEq_terms, a, f, Term.subterms_app]

/-- Mentioning a term alone does not establish its existence. -/
theorem empty_has_no_facts {s t : Term} : ¬ Cong Database.empty s t := by
  intro h
  induction h using Cong.rec (motive_2 := fun _ _ _ => True) with
  | direct h => exact h
  | subterm _ _ ih => exact ih
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | congr _ _ ih _ => exact ih
  | nil => trivial
  | cons => trivial

end Egglog.Tests.SemanticCong
