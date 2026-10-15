import EgglogSemantics.Proofs.Congruence.LiveNormalization

/-! The checked row view derives generated-row shape directly from declarations. -/

namespace Egglog.Congruence.Live

/-- Every function declaration uses the generated minimum merge; constructors are unrestricted. -/
def GeneratedTables (sig : Signature) : Prop :=
  ∀ f decl, sig f = some decl → decl.merge ≠ none → ∃ k, decl = tableDecl k

theorem State.of_generated {d : Database} (hf : d.FiniteStore)
    (huf : d.sig ufName = some (tableDecl 1)) (hg : GeneratedTables d.sig) : State d := by
  refine ⟨hf, huf, ?_⟩
  intro row hr
  obtain ⟨decl, hd, hm, hk, hv, _⟩ := hr.1
  obtain ⟨k, rfl⟩ := hg row.name decl hd hm
  have hkey : row.key.length = k := hk
  refine ⟨by simpa [hkey] using hd, ?_⟩
  have hlen : row.value.length = 1 := hv
  cases he : row.value with
  | nil => simp [he] at hlen
  | cons v rest =>
    have hrest : rest = [] := by simpa [he] using hlen
    exact ⟨v, by simp [hrest]⟩

theorem State.setEnv {d : Database} (h : State d) (env : Env) :
    State { d with env } := ⟨h.finite.setEnv env, h.uf, h.rows⟩

theorem State.addTerm {d : Database} (h : State d) {t : Term}
    (hv : t.IsValue d.sig) : State (d.addTerm t) := by
  refine ⟨h.finite.addTerm t, h.uf, ?_⟩
  simpa only [Database.addTerm_entries hv, Database.addTerm_sig] using h.rows

theorem State.addEq {d : Database} (h : State d) {a b : Term}
    (ha : a.IsValue d.sig) (hb : b.IsValue d.sig) : State (d.addEq a b) := by
  refine ⟨h.finite.addEq a b, by simpa using h.uf, ?_⟩
  simpa only [Database.addEq_entries ha hb, Database.addEq_sig] using h.rows

theorem State.putEntry {d : Database} (h : State d) {row : Entry}
    (hr : LegalRow d.sig row) (hv : row.Valid d.sig) : State (d.putEntry row) := by
  refine ⟨h.finite.putEntry row, by simpa using h.uf, ?_⟩
  intro e he
  simp only [Database.putEntry_sig]
  simp only [Database.putEntry_entries hv, Set.mem_insert_iff] at he
  rcases he with rfl | he
  · exact hr
  · exact h.rows e he

/-- Successful actions preserve finite generated states; the row view checks widths. -/
theorem State.evalAction {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    {a : Action} (he : evalAction d a = some e) : State e := by
  apply State.of_generated (evalAction_finiteStore h.finite he)
  · simpa only [evalAction_sig he] using h.uf
  · simpa only [evalAction_sig he] using hg

theorem State.evalActions {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    {as : List Action} (he : evalActions d as = some e) : State e := by
  apply State.of_generated (evalActions_finiteStore h.finite he)
  · simpa only [evalActions_sig he] using h.uf
  · simpa only [evalActions_sig he] using hg

theorem State.evalLocalActions {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    {as : List Action} {env : Env} (he : evalLocalActions d as env = some e) : State e := by
  apply State.of_generated (evalLocalActions_finiteStore h.finite he)
  · simpa only [evalLocalActions_sig he] using h.uf
  · simpa only [evalLocalActions_sig he] using hg

theorem State.runRules {d : Database} (h : State d) (hg : GeneratedTables d.sig)
    (R : RulesetName) : State (RunRules R d) :=
  State.of_generated (RunRules.finiteStore h.finite R) h.uf hg

/-- A completed round always exists for a finite generated state. -/
theorem State.runStep_exists {d : Database} (h : State d) (hg : GeneratedTables d.sig)
    (R : RulesetName) : ∃ e, RunStep R d e := normalize_exists (h.runRules hg R)

theorem State.runStep {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    {R : RulesetName} (hs : RunStep R d e) : State e :=
  (state_closure (h.runRules hg R) (outputsIn_self _) hs.1).1

end Egglog.Congruence.Live
