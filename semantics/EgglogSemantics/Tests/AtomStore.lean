import EgglogSemantics.Proofs.Diagonal

/-! One assertion store: row replacement preserves values and removes stale matches. -/

namespace Egglog.Tests.AtomStore

private def value (n : Int) : Term := .lit (.int n)
private def row (n : Int) : Entry := ⟨"cost", [value 0], [value n]⟩
private def decl : FnDecl :=
  ⟨1, 1, some (.merge ["old"] ["new"] [] [.min (.var "old") (.var "new")]), none⟩
private def sig : Signature := fun f => if f = "cost" then some decl else none
private def atom (n : Int) : Expr := .app "cost" [.lit (.int 0), .lit (.int n)]
private def base : Database := { Database.empty with sig := sig }
private def before : Database := (base.putEntry (row 7)).putEntry (row 3)
private def after : Database := before.eraseEntry (row 7)

private theorem valid (n : Int) : (row n).Valid sig := by
  refine ⟨decl, by simp [sig, row], by simp [decl], rfl, rfl, ?_⟩
  simp [Entry.columns, row, value, Term.IsValue, Term.isValue]

private theorem before_diag : before.Diag :=
  ((show base.Diag from by simp [Database.Diag, base, Database.empty]).putEntry _).putEntry _

private theorem eval_atom (n : Int) : (atom n).evalAtom sig [] = some (row n).atom := by
  simp [atom, Expr.evalAtom, sig, decl, FnDecl.entryWidth, Expr.evalList, Expr.eval,
    row, Entry.atom, Entry.columns, value]

private theorem before_entries : before.entries = {row 3, row 7} := by
  have hb : base.entries = ∅ := by simp [base, Database.empty, Database.entries]
  unfold before
  rw [Database.putEntry_entries (d := base.putEntry (row 7)) (valid 3),
    Database.putEntry_entries (d := base) (valid 7), hb]
  simp

private theorem remaining : after.entries = {row 3} := by
  unfold after
  rw [Database.eraseEntry_entries (d := before) (valid 7), before_entries]
  ext e
  simp [row, value]

/-- The state change is an actual completed minimum merge. -/
theorem minimum_normalizes : MergeNormalize before after := by
  have hmin : Term.least (value 7) (value 3) = value 3 := by decide +kernel
  let mid := (before.eraseEntry (row 7)).eraseEntry (row 3)
  have hm : MergeValues mid decl [value 7] [value 3] mid [value 3] := by
    apply MergeValues.changed (body := []) (res := [.min (.var "old") (.var "new")])
      (oldVars := ["old"]) (newVars := ["new"]) rfl (by trivial) rfl
    simp [Expr.evalList, Expr.eval, mergeEnv, Env.lookup, Option.filter_some,
      show (value 7).isValue mid.sig = true from rfl,
      show (value 3).isValue mid.sig = true from rfl, hmin]
  have hc : ∀ t ∈ (row 3).columns, ∀ u ∈ t.subterms, (u, u) ∈ mid.eqs := by
    intro t ht u hu
    simp only [row, Entry.columns, List.singleton_append, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      obtain rfl : u = _ := by simpa [value] using hu
    all_goals simp [mid, before, base, Database.empty, Database.eraseEntry,
      Database.putEntry, Database.addTerm, row, Entry.atom, Entry.columns,
      value, Term.subterms_app]
  have heq : mid.putEntry (row 3) = after := by
    apply Database.ext <;> try rfl
    rw [Database.putEntry_eqs_of_columns hc]
    have hm : ((row 3).atom, (row 3).atom) ∈ after.eqs :=
      (show row 3 ∈ after.entries from remaining ▸ Set.mem_singleton _).2
    change insert ((row 3).atom, (row 3).atom)
      (after.eqs \ {((row 3).atom, (row 3).atom)}) = after.eqs
    ext p
    by_cases hp : p = ((row 3).atom, (row 3).atom) <;> simp [hp, hm]
  refine ⟨.single (heq ▸ MergeStep.collide (old := row 7) (new := row 3)
    (by rw [before_entries]; simp) (by rw [before_entries]; simp)
    (by decide) rfl (by simp [before, base, sig, row])
    (.cons (Cong.assert (by simp [before, base, Database.putEntry, Database.addTerm,
      row, Entry.atom, Entry.columns, value, Term.subterms_app])) .nil) hm), ?_⟩
  intro a ha b hb _ _
  rw [remaining, Set.mem_singleton_iff] at ha hb
  exact ha.trans hb.symm

/-- A scalar outlives the function row that used it. -/
theorem superseded_value_remains : value 7 ∈ after.values := by
  refine ⟨Cong.assert ?_, rfl⟩
  simp [after, before, base, Database.eraseEntry, Database.putEntry, Database.addTerm,
    row, Entry.atom, Entry.columns, value, Term.subterms_app]

/-- The retained row matches through the ordinary expression rule. -/
theorem retained_row_matches : Matches after (.expr (atom 3)) [] := by
  have hr : row 3 ∈ after.entries := by rw [remaining]; exact Set.mem_singleton _
  exact .expr (Cong.assert hr.2) (eval_atom 3)
    ((Cong.assert hr.2).mono (Database.Contained.addTerms _ _))

/-- Hypothetical operands cannot supply the original-state witness. -/
theorem stale_row_does_not_match : ¬ Matches after (.expr (atom 7)) [] := by
  intro hm
  cases hm with
  | expr hw he hc =>
    have hrow := eval_atom 7
    obtain rfl := Option.some.inj (hrow.symm.trans he)
    have heq := congOn_eq_of_diag (before_diag.eraseEntry _) hc
    have hp : (row 7).atom ∈ after.terms := heq ▸ hw
    have hnot : (row 7).atom ∉ after.terms := by
      simp [after, before, base, Database.mem_terms_iff, Database.eraseEntry,
        Database.putEntry, Database.addTerm, row, Entry.atom, Entry.columns,
        value, Term.subterms_app, Database.empty]
    exact hnot hp

/-- A row atom cannot become a value through a variable binding. -/
theorem row_binding_rejected :
    (Expr.var "x").eval sig [("x", (row 3).atom)] = none := by
  simp [Expr.eval, Env.lookup, Term.isValue, Entry.atom, Entry.columns,
    row, sig, Signature.IsCtor, decl]

/-- The declaration still checks the complete atom's width. -/
theorem malformed_row_rejected :
    (Expr.app "cost" [.lit (.int 0)]).evalAtom sig [] = none := by
  simp [Expr.evalAtom, sig, decl, FnDecl.entryWidth]

end Egglog.Tests.AtomStore
