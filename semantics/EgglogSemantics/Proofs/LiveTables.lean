import EgglogSemantics.Spec.Step

/-!
# Current-table normalization

These facts depend only on the mathematical specification. In particular, none of
them assumes that an arbitrary merge program has a terminating normalization.

Pending writes are a set: duplicate proposals within a phase coalesce. A pending
tuple remains distinct from an identical resident tuple, so separate completed
phases can observe repeated resets. This models the generated idempotent tables;
it does not claim multiplicity fidelity for arbitrary non-idempotent Rust merges.

`SameMeaning` forgets redundant constructor spellings. Since `ordering-min` can
distinguish representatives, one unchanged round is an operational stopping rule,
not a proof of stability under further rounds for the full language. The compiler's
source fragment separately excludes `ordering-min`.
-/

namespace Egglog.LiveTables

/-- A completed merge phase cannot take another insertion or collision step. -/
theorem mergeSaturated_no_step {d e : Database} (hn : MergeSaturated d) :
    ¬ MergeStep d e := by
  intro hs
  cases hs with
  | insert _ _ hp _ => simp [hn.pending] at hp
  | write hp _ _ _ _ _ => simp [hn.pending] at hp
  | collide ha hb hne hname _ hkey _ =>
      exact hne (hn.unique _ ha _ hb hname hkey)

/-- A finite merge sequence from a completed state is necessarily empty. -/
theorem mergeClosure_eq_of_saturated {d e : Database} (hn : MergeSaturated d)
    (hc : MergeClosure d e) : e = d := by
  rcases Relation.ReflTransGen.cases_head hc with he | ⟨m, hm, _⟩
  · exact he.symm
  · exact (mergeSaturated_no_step hn hm).elim

/-- Normalization supplies one current row per congruence class of keys. -/
theorem normalize_unique {d e : Database} (hn : MergeNormalize d e)
    {a b : Entry} (ha : a ∈ e.entries) (hb : b ∈ e.entries)
    (hname : a.name = b.name) (hkey : CongList e a.key b.key) : a = b :=
  hn.2.unique a ha b hb hname hkey

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

/-- Consuming a pending write first lets the merge body propose the very same
tuple again. It remains pending for a later normalization step. -/
theorem rewritten_consumed_write_pending (d : Database) (row : Entry) :
    row ∈ ((d.consumeWrite row).writeEntry row).pending := by
  simp [Database.writeEntry]

/-- Installing the resolved output preserves all writes emitted by the body. -/
theorem putEntry_preserves_pending (d : Database) (row : Entry) :
    (d.putEntry row).pending = d.pending := by
  simp only [Database.putEntry, Database.addTerms]
  generalize row.columns = cols
  induction cols generalizing d with
  | nil => rfl
  | cons a as ih => exact ih (d.addTerm a)

/-- Removing a resident entry does not discard a pending reset of that tuple. -/
theorem eraseEntry_preserves_pending (d : Database) (row : Entry) :
    (d.eraseEntry row).pending = d.pending := rfl

mutual

private theorem cong_mono {d e : Database} (h : d.eqs ⊆ e.eqs) :
    ∀ {a b}, Cong d a b → Cong e a b
  | _, _, .assert hp => .assert (h hp)
  | _, _, .symm hc => .symm (cong_mono h hc)
  | _, _, .trans ha hb => .trans (cong_mono h ha) (cong_mono h hb)
  | _, _, .congr ha hb hc => .congr (cong_mono h ha) (cong_mono h hb) (congList_mono h hc)

private theorem congList_mono {d e : Database} (h : d.eqs ⊆ e.eqs) :
    ∀ {as bs}, CongList d as bs → CongList e as bs
  | _, _, .nil => .nil
  | _, _, .cons ha hb => .cons (cong_mono h ha) (congList_mono h hb)

end

private theorem addTerms_eraseEntry (d : Database) (row : Entry) (ts : List Term) :
    (d.eraseEntry row).addTerms ts = (d.addTerms ts).eraseEntry row := by
  induction ts generalizing d with
  | nil => rfl
  | cons a as ih => exact ih (d.addTerm a)

/-- A duplicate proposal is still processed, but an unchanged collision consumes
it and restores the resident row in one genuine merge step. -/
theorem absorb_unchanged_write {d : Database} {row : Entry} {decl : FnDecl}
    {oldVars newVars : List Var} {body : List Action} {res : List Expr}
    (hn : MergeSaturated d) (hr : row ∈ d.entries)
    (hcols : d.addTerms row.columns = d)
    (hkey : CongList d row.key row.key)
    (hdecl : d.sig row.name = some decl)
    (hmerge : decl.merge = some (.merge oldVars newVars body res))
    (hunchanged : ¬ MergeConflict decl body row.value row.value) :
    MergeNormalize (d.writeEntry row) d := by
  have hw : d.writeEntry row = {d with pending := insert row d.pending} := by
    simp [Database.writeEntry, hcols]
  have hconsume : (d.writeEntry row).consumeWrite row = d := by
    rw [hw]
    apply Database.ext <;> simp [Database.consumeWrite, hn.pending]
  have hrestore : (d.eraseEntry row).putEntry row = d := by
    unfold Database.putEntry
    rw [addTerms_eraseEntry, hcols]
    have he : insert row (d.entries \ {row}) = d.entries := by
      ext e
      simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | ⟨he, _⟩)
        · exact hr
        · exact he
      · intro he
        by_cases heq : e = row
        · exact Or.inl heq
        · exact Or.inr ⟨he, heq⟩
    simp only [Database.eraseEntry, he]
  have hstep : MergeStep (d.writeEntry row) ((d.eraseEntry row).putEntry row) := by
    apply MergeStep.write (old := row) (new := row) (decl := decl)
      (vs := row.value)
    · rw [hw]
      exact Set.mem_insert _ _
    · simpa only [hw] using hr
    · rfl
    · simpa only [hw] using hdecl
    · apply congList_mono (d := d) _ hkey
      rw [hw]
    · rw [hconsume]
      exact .unchanged hmerge hunchanged
  exact ⟨.single (by simpa only [hrestore] using hstep), hn⟩

/-- Identity columns, including the generated tables' unchanged-width policy,
make a tuple's duplicate write an unchanged collision. -/
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

private theorem congList_self_of_held {d : Database} :
    ∀ {ts : List Term}, (∀ t ∈ ts, t ∈ d.terms) → CongList d ts ts
  | [], _ => .nil
  | t :: ts, ht =>
      .cons (ht t (by simp))
        (congList_self_of_held (fun s hs => ht s (List.mem_cons_of_mem t hs)))

/-- The absorption theorem's term-side premises follow from ordinary held-column
invariants. A declaration with an unchanged width handles identical outputs. -/
theorem absorb_existing_idempotent_write {d : Database} {row : Entry} {decl : FnDecl}
    {oldVars newVars : List Var} {body : List Action} {res : List Expr} {k : Nat}
    (hw : d.WF) (hn : MergeSaturated d) (hr : row ∈ d.entries)
    (hcols : ∀ t ∈ row.columns, t ∈ d.terms)
    (hdecl : d.sig row.name = some decl)
    (hmerge : decl.merge = some (.merge oldVars newVars body res))
    (hwidth : decl.unchangedWidth body = some k) :
    MergeNormalize (d.writeEntry row) d := by
  apply absorb_unchanged_write hn hr (addTerms_eq_of_held hw hcols)
    (congList_self_of_held ?_) hdecl hmerge (self_not_conflict hwidth)
  intro t ht
  exact hcols t (List.mem_append_left _ ht)

theorem sameMeaning_refl (d : Database) : d.SameMeaning d :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => Iff.rfl⟩

/-- A round proposing only one duplicate of an existing idempotent row has an
actual finite completion, and `saturate` stops after that completion. -/
theorem saturate_absorbed_write {d : Database} {R : RulesetName} {row : Entry}
    (hround : RunRules R d = d.writeEntry row)
    (hn : MergeNormalize (d.writeEntry row) d) : SaturateReach R d d := by
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
    (hn : MergeSaturated d) (h : ∀ r ∈ d.rules, r.ruleset ≠ R) :
    RunSaturated R d := by
  refine ⟨hn, d, ?_, sameMeaning_refl d⟩
  rw [RunStep, runRules_eq_of_no_rules h]
  exact ⟨.refl, hn⟩

/-- In particular, saturating the empty database is a finite execution. -/
theorem empty_saturateReach (R : RulesetName) :
    SaturateReach R Database.empty Database.empty := by
  apply SaturateReach.done
  · rw [RunStep, runRules_eq_of_no_rules (by simp [Database.empty])]
    exact ⟨.refl, rfl, by simp [Database.empty]⟩
  · exact sameMeaning_refl _

end Egglog.LiveTables
