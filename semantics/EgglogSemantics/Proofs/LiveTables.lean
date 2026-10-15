import EgglogSemantics.Proofs.Diagonal

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

private theorem table_not_value {sig : Signature} {f : FnName} {decl : FnDecl}
    (hd : sig f = some decl) (hm : decl.merge ≠ none) (cols : List Term) :
    ¬ (Term.app f cols).IsValue sig := by
  intro hv
  obtain ⟨ctor, hc, hnone⟩ := (Term.isValue_app_iff.mp hv).1
  obtain rfl := Option.some.inj (hc.symm.trans hd)
  exact hm hnone

/-- Typed equations preserve the head of a table atom. -/
theorem cong_table_head_iff {d : Database} (hs : d.StoreOk)
    {f : FnName} {decl : FnDecl} (hd : d.sig f = some decl) (hm : decl.merge ≠ none)
    {a b : Term} (hc : Cong d a b) :
    (∃ cols, a = .app f cols) ↔ (∃ cols, b = .app f cols) := by
  induction hc using Cong.rec (motive_2 := fun _ _ _ => True) with
  | assert hp =>
    rcases hs.typed _ hp with ⟨ha, hb⟩ | ⟨row, _, he⟩
    · constructor
      · rintro ⟨cols, rfl⟩
        exact (table_not_value hd hm cols ha).elim
      · rintro ⟨cols, rfl⟩
        exact (table_not_value hd hm cols hb).elim
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr =>
    constructor <;> rintro ⟨cols, he⟩
    · obtain ⟨rfl, _⟩ := Term.app.inj he
      exact ⟨_, rfl⟩
    · obtain ⟨rfl, _⟩ := Term.app.inj he
      exact ⟨_, rfl⟩
  | nil => trivial
  | cons => trivial

/-- A table atom's only nontrivial congruence comes from its columns. -/
theorem cong_table_columns {d : Database} (hs : d.StoreOk)
    {f : FnName} {decl : FnDecl} (hd : d.sig f = some decl) (hm : decl.merge ≠ none)
    {as bs : List Term} (hc : Cong d (.app f as) (.app f bs)) : CongList d as bs := by
  have aux : ∀ {a b : Term}, Cong d a b →
      ∀ {f : FnName} {decl : FnDecl} {as bs : List Term},
      d.sig f = some decl → decl.merge ≠ none →
      a = .app f as → b = .app f bs → CongList d as bs := by
    intro a b hc
    induction hc using Cong.rec (motive_2 := fun _ _ _ => True) with
    | assert hp =>
      intro f decl as bs hd hm ha hb
      cases ha
      cases hb
      rcases hs.typed _ hp with ⟨hv, _⟩ | ⟨row, hr, he⟩
      · exact (table_not_value hd hm as hv).elim
      · obtain ⟨ha, hb⟩ := Prod.mk.inj he
        have hcols := (Term.app.inj ha).2
        have hcols' := (Term.app.inj hb).2
        rw [hcols, hcols']
        apply CongList.refl
        exact hs.columns row ⟨hr, by simpa only [he] using hp⟩
    | symm _ ih =>
      intro f decl as bs hd hm ha hb
      exact (ih hd hm hb ha).symm
    | trans h₁ _ ih₁ ih₂ =>
      intro f decl as bs hd hm ha hb
      obtain ⟨cols, hcols⟩ := (cong_table_head_iff hs hd hm h₁).mp ⟨as, ha⟩
      exact (ih₁ hd hm ha hcols).trans (ih₂ hd hm hcols hb)
    | congr _ _ hcols _ _ _ =>
      intro f decl as bs _ _ ha hb
      obtain ⟨rfl, rfl⟩ := Term.app.inj ha
      obtain ⟨_, rfl⟩ := Term.app.inj hb
      exact hcols
    | nil => trivial
    | cons => trivial
  exact aux hc hd hm rfl rfl

/-- Typed held atoms have their own assertion, so they decode as current rows. -/
theorem entry_of_held_atom {d : Database} (hs : d.StoreOk) {row : Entry}
    (hr : row.Valid d.sig) (ht : row.atom ∈ d.terms) : row ∈ d.entries := by
  refine ⟨hr, ?_⟩
  obtain ⟨u, hp | hp⟩ := Database.mem_terms_iff.mp ht
  · rcases hs.typed _ hp with ⟨hv, _⟩ | ⟨other, ho, he⟩
    · exact (hr.atom_not_value hv).elim
    · have hrow := hr.atom_injective ho (congrArg Prod.fst he)
      subst other
      simpa only [he] using hp
  · rcases hs.typed _ hp with ⟨_, hv⟩ | ⟨other, ho, he⟩
    · exact (hr.atom_not_value hv).elim
    · have hrow := hr.atom_injective ho (congrArg Prod.snd he)
      subst other
      simpa only [he] using hp

/-- Unified atom matching still reads a compatible current function row. -/
theorem table_match_current {d : Database} (hs : d.StoreOk)
    {e : Expr} {σ : Env} {target : Entry} (ht : target.Valid d.sig)
    (he : e.evalAtom d.sig σ = some target.atom) (hm : Matches d (.expr e) σ) :
    ∃ row ∈ d.entries, row.name = target.name ∧
      CongList (d.withOperands [target.atom]) target.columns row.columns := by
  cases hm with
  | expr hw he' hc =>
    obtain rfl := Option.some.inj (he'.symm.trans he)
    have hs' : (d.withOperands [target.atom]).StoreOk :=
      hs.addTerm target.atom (Or.inr ⟨target, ht, rfl⟩)
    rcases hs.term hw with hv | ⟨row, hr, rfl⟩
    · exact (ht.atom_not_value ((hc.isValue_iff hs').mp hv)).elim
    · have hrow := entry_of_held_atom hs hr hw
      obtain ⟨decl, hd, hmerge, _⟩ := ht
      obtain ⟨cols, hcols⟩ := (cong_table_head_iff hs' hd hmerge hc).mpr
        ⟨target.columns, rfl⟩
      have hname : row.name = target.name := (Term.app.inj hcols).1
      refine ⟨row, hrow, hname, ?_⟩
      apply CongList.symm
      apply cong_table_columns hs' hd hmerge
      simpa only [CongOn, Entry.atom, hname] using hc

/-- In a diagonal state, an atom match names an actual stored row exactly. -/
theorem table_match_current_of_diagonal {d : Database} (hd : d.Diag)
    {e : Expr} {σ : Env} {target : Entry} (ht : target.Valid d.sig)
    (he : e.evalAtom d.sig σ = some target.atom) (hm : Matches d (.expr e) σ) :
    target ∈ d.entries := by
  cases hm with
  | expr hw he' hc =>
    obtain rfl := Option.some.inj (he'.symm.trans he)
    obtain rfl := congOn_eq_of_diag hd hc
    refine ⟨ht, ?_⟩
    obtain ⟨u, hp | hp⟩ := Database.mem_terms_iff.mp hw
    · have hu : target.atom = u := hd _ hp
      simpa only [hu] using hp
    · have hu : u = target.atom := hd _ hp
      simpa only [hu] using hp

/-- A compatible current row supplies the witness for unified atom matching. -/
theorem table_match_of_current {d : Database} {e : Expr} {σ : Env} {target row : Entry}
    (he : e.evalAtom d.sig σ = some target.atom) (hr : row ∈ d.entries)
    (hn : row.name = target.name)
    (hc : CongList (d.withOperands [target.atom]) target.columns row.columns) :
    Matches d (.expr e) σ := by
  apply Matches.expr (.assert hr.2) he
  have hrow : Cong (d.withOperands [target.atom]) row.atom row.atom :=
    .assert (Or.inl hr.2)
  have htarget : Cong (d.withOperands [target.atom]) target.atom target.atom :=
    .assert (Or.inr ⟨target.atom, .refl _, rfl⟩)
  change Cong (d.withOperands [target.atom])
    (.app row.name row.columns) (.app target.name target.columns)
  rw [hn]
  exact .congr (by simpa only [Entry.atom, hn] using hrow) htarget hc.symm

/-- Once every current row is incompatible, the replaced output cannot match. -/
theorem replaced_output_does_not_match {d : Database} (hs : d.StoreOk)
    {e : Expr} {σ : Env} {target : Entry} (ht : target.Valid d.sig)
    (he : e.evalAtom d.sig σ = some target.atom)
    (hgone : ∀ row ∈ d.entries, row.name = target.name →
      ¬ CongList (d.withOperands [target.atom]) target.columns row.columns) :
    ¬ Matches d (.expr e) σ := by
  intro hm
  obtain ⟨row, hr, hn, hc⟩ := table_match_current hs ht he hm
  exact hgone row hr hn hc

private theorem addTerm_eq_of_held {d : Database} (hw : d.WF) {t : Term}
    (ht : t ∈ d.terms) : d.addTerm t = d := by
  have hs : {(s, s) | s ∈ t.subterms} ⊆ d.eqs := by
    rintro p ⟨s, hs, rfl⟩
    exact hw.eqsRefl s (hw.subtermClosed t ht hs)
  unfold Database.addTerm
  rw [Set.union_eq_left.mpr hs]

/-- Repeating an already materialized row insertion is exactly the identity. -/
theorem putEntry_eq_of_mem {d : Database} {row : Entry}
    (hw : d.WF) (hr : row ∈ d.entries) : d.putEntry row = d :=
  addTerm_eq_of_held hw (.assert hr.2)

/-- A duplicate insertion into a normal store already has a completed normalization. -/
theorem normalize_existing_putEntry {d : Database} {row : Entry}
    (hw : d.WF) (hn : MergeNormal d) (hr : row ∈ d.entries) :
    MergeNormalize (d.putEntry row) d := by
  rw [putEntry_eq_of_mem hw hr]
  exact ⟨.refl, hn⟩

/-- Removing colliding rows before the body runs allows it to reinsert either row. -/
theorem reinsert_erased_entry (d : Database) (old new : Entry) (ho : old.Valid d.sig) :
    old ∈ (((d.eraseEntry old).eraseEntry new).putEntry old).entries := by
  rw [Database.putEntry_entries (d := (d.eraseEntry old).eraseEntry new) ho]
  exact Set.mem_insert _ _

/-- Equal output tuples satisfy every unchanged-width policy. -/
theorem self_not_conflict {decl : FnDecl} {body : List Action} {values : List Term}
    {k : Nat} (h : decl.unchangedWidth body = some k) :
    ¬ MergeConflict decl body values values := by
  simp [MergeConflict, h]

theorem sameMeaning_refl (d : Database) : d.SameMeaning d :=
  ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl⟩

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
    exact ⟨.refl, by simp [MergeNormal, Database.entries, Database.empty]⟩
  · exact sameMeaning_refl _

end Egglog.LiveTables
