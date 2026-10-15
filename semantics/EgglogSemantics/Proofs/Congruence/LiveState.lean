import EgglogSemantics.Proofs.Congruence.LiveNormalization

/-! Deriving generated-row invariants from declarations, action widths, and actual
executions. These lemmas discharge merge-normalization premises without assuming
source/target correspondence or saturation termination. -/

namespace Egglog.Congruence.Live

/-- Every function declaration uses the generated minimum merge; constructors are unrestricted. -/
def GeneratedTables (sig : Signature) : Prop :=
  ∀ f decl, sig f = some decl → decl.merge ≠ none → ∃ k, decl = tableDecl k

theorem State.setEnv {d : Database} (h : State d) (env : Env) :
    State { d with env } := ⟨h.finite.setEnv env, h.uf, h.rows⟩

theorem State.addTerm {d : Database} (h : State d) (t : Term) : State (d.addTerm t) :=
  ⟨h.finite.addTerm t, h.uf, h.rows⟩

theorem State.addEq {d : Database} (h : State d) (a b : Term) : State (d.addEq a b) := by
  refine ⟨h.finite.addEq a b, ?_, ?_⟩
  · simpa using h.uf
  · simpa using h.rows

theorem State.putEntry {d : Database} (h : State d) {row : Entry}
    (hr : LegalRow d.sig row) : State (d.putEntry row) := by
  refine ⟨h.finite.putEntry row, by simpa using h.uf, ?_⟩
  intro e he
  simp only [Database.putEntry_sig]
  simp only [Database.putEntry_entries, Set.mem_insert_iff] at he
  rcases he with rfl | he
  · exact hr
  · exact h.rows e he

private theorem legal_evaluated_entry {sig : Signature} (hg : GeneratedTables sig)
    {e : Expr} {f : FnName} {keys vals : List Expr} {ks vs : List Term} {env : Env}
    (hw : e.AtomWidthOk sig) (he : e.entry sig = some (f, keys, vals))
    (hk : Expr.evalList sig keys env = some ks)
    (hv : Expr.evalList sig vals env = some vs) : LegalRow sig ⟨f, ks, vs⟩ := by
  obtain ⟨decl, hd, hm, rfl⟩ := Expr.entry_some he
  obtain ⟨k, rfl⟩ := hg f decl hd (by intro hnone; simp [hnone] at hm)
  have hlen : (keys ++ vals).length = k + 1 := by
    simpa [FnDecl.entryWidth, tableDecl] using hw.1 _ hd
  have hparts : (f, (keys ++ vals).take k, (keys ++ vals).drop k) = (f, keys, vals) := by
    simpa [Expr.entry, hd, tableDecl] using he
  have hkl : keys.length = k := by
    have ht := congrArg (fun p : FnName × List Expr × List Expr => p.2.1.length) hparts
    simpa [List.length_take, hlen, Nat.min_eq_left (by omega : k ≤ k + 1)] using ht.symm
  have hvl : vals.length = 1 := by simpa [List.length_append, hkl] using hlen
  have hks := (Expr.evalList_length hk).trans hkl
  have hvs := (Expr.evalList_length hv).trans hvl
  refine ⟨by simpa [hks] using hd, ?_⟩
  cases vs with
  | nil => simp at hvs
  | cons v rest =>
    have hr : rest = [] := by simpa using hvs
    exact ⟨v, by rw [hr]⟩

/-- Width checking supplies the row-shape premise needed by normalization. -/
theorem State.evalAction {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    {a : Action} (hw : a.WidthOk d.sig) (he : evalAction d a = some e) : State e := by
  rcases evalAction_eq_some he with ⟨_, t, rfl, _, rfl⟩ |
    ⟨exp, f, keys, vals, ks, vs, rfl, hentry, hk, hv, rfl⟩ |
    ⟨_, _, a, b, rfl, _, _, _, rfl⟩
  · exact h.addTerm t
  · exact h.putEntry (legal_evaluated_entry hg hw hentry hk hv)
  · exact h.addEq a b

theorem State.evalActions {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    {as : List Action} (hw : Actions.WidthOk as d.sig)
    (he : evalActions d as = some e) : State e := by
  induction as generalizing d with
  | nil => cases he; exact h
  | cons a as ih =>
    obtain ⟨mid, ha, has⟩ := Option.bind_eq_some_iff.mp he
    apply ih (h.evalAction hg hw.1 ha) ?_ ?_ has
    · rw [evalAction_sig ha]
      exact hg
    · rw [evalAction_sig ha]
      exact hw.2

theorem State.evalLocalActions {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    {as : List Action} {env : Env} (hw : Actions.WidthOk as d.sig)
    (he : evalLocalActions d as env = some e) : State e := by
  obtain ⟨mid, hm, rfl⟩ := Option.map_eq_some_iff.mp he
  have hmid := (h.setEnv (env ++ d.env)).evalActions hg hw hm
  exact ⟨⟨hmid.finite.eqs, hmid.finite.entries, h.finite.rules⟩,
    hmid.uf, hmid.rows⟩

/-- All substitutions of all registered rules preserve legal generated rows. -/
theorem State.runRules {d : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hw : ∀ r ∈ d.rules, r.WidthOk d.sig) (R : RulesetName) : State (RunRules R d) := by
  refine ⟨RunRules.finiteStore h.finite R, h.uf, ?_⟩
  have hresult : ∀ post, (∃ r ∈ d.rules, r.ruleset = R ∧ post ∈ RuleResults d r) →
      AllRows (LegalRow d.sig) post := by
    rintro post ⟨r, hr, _, env, _, heval⟩ row hrow
    have hp := h.evalLocalActions hg (hw r hr) heval
    simpa only [evalLocalActions_sig heval] using hp.rows row hrow
  intro row hrow
  change row ∈ (d.entries ∪ ⋃ post ∈ {post | ∃ r ∈ d.rules,
      r.ruleset = R ∧ post ∈ RuleResults d r}, post.entries) at hrow
  rcases hrow with hr | hr
  · exact h.rows row hr
  · obtain ⟨post, hp, hr⟩ := Set.mem_iUnion₂.mp hr
    exact hresult post hp row hr

/-- A completed round always exists for a finite generated state with width-correct rules. -/
theorem State.runStep_exists {d : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hw : ∀ r ∈ d.rules, r.WidthOk d.sig) (R : RulesetName) : ∃ e, RunStep R d e :=
  normalize_exists (h.runRules hg hw R)

theorem State.runStep {d e : Database} (h : State d) (hg : GeneratedTables d.sig)
    (hw : ∀ r ∈ d.rules, r.WidthOk d.sig) {R : RulesetName} (hs : RunStep R d e) :
    State e :=
  (state_closure (h.runRules hg hw R) (outputsIn_self _) hs.1).1

end Egglog.Congruence.Live
