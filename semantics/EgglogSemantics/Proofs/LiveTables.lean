import EgglogSemantics.Spec.Step

/-!
# Current-table normalization

These facts depend only on the mathematical specification. In particular, none of
them assumes that an arbitrary merge program has a terminating normalization.

Current entries are a set: inserting an existing tuple coalesces immediately.
Only distinct current rows can collide. This models the generated idempotent tables;
it does not claim multiplicity fidelity for arbitrary non-idempotent Rust merges.

`SameMeaning` forgets redundant constructor spellings. Since `ordering-min` can
distinguish representatives, one unchanged round is an operational stopping rule,
not a proof of stability under further rounds for the full language. The compiler's
source fragment separately excludes `ordering-min`.
-/

namespace Egglog.LiveTables

/-- A completed merge phase cannot take another collision step. -/
theorem mergeNormal_no_step {d e : Database} (hn : MergeNormal d) :
    ¬ MergeStep d e := by
  intro hs
  cases hs with
  | collide ha hb hne hname _ hkey _ =>
      exact hne (hn _ ha _ hb hname hkey)

/-- A finite merge sequence from a completed state is necessarily empty. -/
theorem mergeClosure_eq_of_normal {d e : Database} (hn : MergeNormal d)
    (hc : MergeClosure d e) : e = d := by
  rcases Relation.ReflTransGen.cases_head hc with he | ⟨m, hm, _⟩
  · exact he.symm
  · exact (mergeNormal_no_step hn hm).elim

/-- Normalization supplies one current row per congruence class of keys. -/
theorem normalize_unique {d e : Database} (hn : MergeNormalize d e)
    {a b : Entry} (ha : a ∈ e.entries) (hb : b ∈ e.entries)
    (hname : a.name = b.name) (hkey : CongList e a.key b.key) : a = b :=
  hn.2 a ha b hb hname hkey

/-- In particular, an exact key with held components has one current output. -/
theorem normalize_exact_key {d e : Database} (hn : MergeNormalize d e)
    {f : FnName} {key old new : List Term}
    (ha : Entry.mk f key old ∈ e.entries)
    (hb : Entry.mk f key new ∈ e.entries) (hk : CongList e key key) : old = new := by
  exact congrArg Entry.value (normalize_unique hn ha hb rfl hk)

/-- A table pattern must read a compatible current row. Historical constructor
existence cannot satisfy it through the value-expression case. -/
theorem table_match_current {d : Database} {e : Expr} {σ : Env}
    {f : FnName} {keys values : List Expr} {ks vs : List Term}
    (he : e.entry d.sig = some (f, keys, values))
    (hv : e.eval d.sig σ = none)
    (hk : Expr.evalList d.sig keys σ = some ks)
    (ho : Expr.evalList d.sig values σ = some vs)
    (hm : Matches d (.expr e) σ) :
    ∃ row ∈ d.entries, row.name = f ∧
      CongList (d.withOperands (ks ++ vs)) (ks ++ vs) row.columns := by
  cases hm with
  | expr _ h _ => simp [hv] at h
  | entry he' hk' ho' hr hn hc =>
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj (he.symm.trans he')
      obtain rfl := Option.some.inj (hk.symm.trans hk')
      obtain rfl := Option.some.inj (ho.symm.trans ho')
      exact ⟨_, hr, hn, hc⟩

/-- Once every current row is incompatible, the replaced output cannot match.
The premise allows congruent outputs, which remain legitimate matches. -/
theorem replaced_output_does_not_match {d : Database} {e : Expr} {σ : Env}
    {f : FnName} {keys values : List Expr} {ks vs : List Term}
    (he : e.entry d.sig = some (f, keys, values))
    (hv : e.eval d.sig σ = none)
    (hk : Expr.evalList d.sig keys σ = some ks)
    (ho : Expr.evalList d.sig values σ = some vs)
    (hgone : ∀ row ∈ d.entries, row.name = f →
      ¬ CongList (d.withOperands (ks ++ vs)) (ks ++ vs) row.columns) :
    ¬ Matches d (.expr e) σ := by
  intro hm
  obtain ⟨row, hr, hn, hc⟩ := table_match_current he hv hk ho hm
  exact hgone row hr hn hc

/-- Repeating an already materialized row insertion is exactly the identity. -/
theorem putEntry_eq_of_mem {d : Database} {row : Entry}
    (hr : row ∈ d.entries) (hcols : d.addTerms row.columns = d) :
    d.putEntry row = d := by
  simp [Database.putEntry, hcols, Set.insert_eq_of_mem hr]

/-- A duplicate insertion into a normal store already has a completed normalization. -/
theorem normalize_existing_putEntry {d : Database} {row : Entry}
    (hn : MergeNormal d) (hr : row ∈ d.entries)
    (hcols : d.addTerms row.columns = d) : MergeNormalize (d.putEntry row) d := by
  rw [putEntry_eq_of_mem hr hcols]
  exact ⟨.refl, hn⟩

/-- Removing colliding rows before the body runs allows it to reinsert either row. -/
theorem reinsert_erased_entry (d : Database) (old new : Entry) :
    old ∈ (((d.eraseEntry old).eraseEntry new).putEntry old).entries := by
  change old ∈ insert old _
  exact Set.mem_insert _ _

/-- Equal output tuples satisfy every unchanged-width policy. -/
theorem self_not_conflict {decl : FnDecl} {body : List Action} {values : List Term}
    {k : Nat} (h : decl.unchangedWidth body = some k) :
    ¬ MergeConflict decl body values values := by
  simp [MergeConflict, h]

private theorem addTerm_eq_of_held {d : Database} (hw : d.WF) {t : Term}
    (ht : t ∈ d.terms) : d.addTerm t = d := by
  have hs : {(s, s) | s ∈ t.subterms} ⊆ d.eqs := by
    rintro p ⟨s, hs, rfl⟩
    exact hw.eqsRefl s (hw.subtermClosed t ht hs)
  unfold Database.addTerm
  rw [Set.union_eq_left.mpr hs]

private theorem addTerms_eq_of_held {d : Database} (hw : d.WF) :
    ∀ {ts : List Term}, (∀ t ∈ ts, t ∈ d.terms) → d.addTerms ts = d
  | [], _ => rfl
  | t :: ts, ht => by
      change (d.addTerm t).addTerms ts = d
      rw [addTerm_eq_of_held hw (ht t (by simp))]
      exact addTerms_eq_of_held hw (fun s hs => ht s (List.mem_cons_of_mem t hs))

/-- Ordinary held-column invariants supply the duplicate insertion's term premise. -/
theorem normalize_existing_putEntry_of_held {d : Database} {row : Entry}
    (hw : d.WF) (hn : MergeNormal d) (hr : row ∈ d.entries)
    (hcols : ∀ t ∈ row.columns, t ∈ d.terms) :
    MergeNormalize (d.putEntry row) d :=
  normalize_existing_putEntry hn hr (addTerms_eq_of_held hw hcols)

theorem sameMeaning_refl (d : Database) : d.SameMeaning d :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => Iff.rfl⟩

/-- A round inserting only a duplicate of an existing row has an
actual finite completion, and `saturate` stops after that completion. -/
theorem saturate_absorbed_write {d : Database} {R : RulesetName} {row : Entry}
    (hround : RunRules R d = d.putEntry row)
    (hn : MergeNormalize (d.putEntry row) d) : SaturateReach R d d := by
  apply SaturateReach.done
  · simpa only [RunStep, hround] using hn
  · exact sameMeaning_refl d

/-- An inactive ruleset really has an identity rule phase. -/
theorem runRules_eq_of_no_rules {d : Database} {R : RulesetName}
    (h : ∀ r ∈ d.rules, r.ruleset ≠ R) : RunRules R d = d := by
  have hempty : {e | ∃ r ∈ d.rules, r.ruleset = R ∧ e ∈ RuleResults d r} =
      (∅ : Set Database) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨r, hr, hR, _⟩
    exact h r hr hR
  simp [RunRules, hempty, Database.sUnion]

/-- The new saturation predicate has actual completed-round witnesses. -/
theorem runSaturated_of_no_rules {d : Database} {R : RulesetName}
    (hn : MergeNormal d) (h : ∀ r ∈ d.rules, r.ruleset ≠ R) :
    RunSaturated R d := by
  refine ⟨hn, d, ?_, sameMeaning_refl d⟩
  rw [RunStep, runRules_eq_of_no_rules h]
  exact ⟨.refl, hn⟩

/-- In particular, saturating the empty database is a finite execution. -/
theorem empty_saturateReach (R : RulesetName) :
    SaturateReach R Database.empty Database.empty := by
  apply SaturateReach.done
  · rw [RunStep, runRules_eq_of_no_rules (by simp [Database.empty])]
    exact ⟨.refl, by simp [MergeNormal, Database.empty]⟩
  · exact sameMeaning_refl _

end Egglog.LiveTables
