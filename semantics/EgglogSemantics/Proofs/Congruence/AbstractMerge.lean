import EgglogSemantics.Proofs.Congruence.AbstractState
import EgglogSemantics.Proofs.Congruence.IdOrder
import EgglogSemantics.Proofs.Congruence.MetadataSyntax
import EgglogSemantics.Proofs.DiagonalPreservation
import EgglogSemantics.Proofs.StatePreservation
import EgglogSemantics.Proofs.Congruence.LiveNormalization

/-! Generated merges preserve the justification and order of every retained row. -/

namespace Egglog.Congruence.Abstract

/-- The two links written by one generated collision. -/
def mergeLinks (d : Database) (a b : Term) : Database :=
  (d.addTerm (.app ufName [a, lowerId a b])).addTerm (.app ufName [b, lowerId a b])

theorem mem_terms_of_mergeLinks {d : Database} {a b t : Term} (ht : t ∈ d.terms) :
    t ∈ (mergeLinks d a b).terms :=
  (Database.Contained.addTerm _ _).terms ((Database.Contained.addTerm _ _).terms ht)

theorem mergeLinks_wf {d : Database} (hw : d.WF) (a b : Term) :
    (mergeLinks d a b).WF := (hw.addTerm _).addTerm _

theorem SoundTerms.mergeLinks {src d : Database} (hw : d.WF) (h : SoundTerms d src)
    {a b : Term} (ha : a ∈ d.terms) (hb : b ∈ d.terms) (hc : Cong src a b) :
    SoundTerms (mergeLinks d a b) src := by
  have hl : lowerId a b ∈ d.terms := by
    rcases lowerId_eq_or a b with he | he <;> rw [he] <;> assumption
  exact (h.addUF hw ha hl (cong_lowerId_left hc)).addUF (hw.addTerm _)
    ((Database.Contained.addTerm _ _).terms hb)
    ((Database.Contained.addTerm _ _).terms hl) (cong_lowerId_right hc)

theorem Descending.mergeLinks {d : Database} (hw : d.WF) (h : Descending d)
    {a b : Term} (ha : a ∈ d.terms) (hb : b ∈ d.terms) : Descending (mergeLinks d a b) := by
  have hl : lowerId a b ∈ d.terms := by
    rcases lowerId_eq_or a b with he | he <;> rw [he] <;> assumption
  exact (h.addUF hw ha hl (lowerId_le_left a b)).addUF (hw.addTerm _)
    ((Database.Contained.addTerm _ _).terms hb)
    ((Database.Contained.addTerm _ _).terms hl) (lowerId_le_right a b)

/-- A collision deletes both inputs before writing its links and result. -/
theorem mergeStep_form {d e : Database} (hshape : MergeShape d.sig) (hd : d.Diag)
    (huf : d.sig ufName = some (tableDecl 1))
    (hstep : MergeStep d e) :
    ∃ f cs a b,
      Entry.mk f cs [a] ∈ d.entries ∧ Entry.mk f cs [b] ∈ d.entries ∧
      ((f = ufName ∧ cs.length = 1) ∨ ∃ g, f = viewName g) ∧
      e = (mergeLinks ((d.eraseEntry ⟨f, cs, [a]⟩).eraseEntry ⟨f, cs, [b]⟩)
        a b).addTerm (.app f (cs ++ [lowerId a b])) := by
  cases hstep with
  | @collide post old new dc vs ho hn hne hname hsig hkeys hm =>
    have hnot := ho.1.decl_spec hsig
    obtain ⟨ms, hms⟩ := Option.ne_none_iff_exists'.mp hnot.1
    cases ms with
    | merge oldVars newVars body res =>
      obtain ⟨hrole, rfl, rfl, hout, hufarity, hid, rfl, rfl⟩ :=
        hshape old.name dc hsig body res hms
      have hdc : dc = tableDecl dc.arity := by
        cases dc; simp_all [tableDecl]
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hnot.2.2.trans hout)
      have hk := CongList.eq_of_diag hd hkeys
      have hsig' : d.sig new.name = some dc := hname ▸ hsig
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp ((hn.1.decl_spec hsig').2.2.trans hout)
      have hea : old = ⟨old.name, old.key, [a]⟩ := by
        cases old; exact congrArg (Entry.mk _ _) ha
      have heb : new = ⟨old.name, old.key, [b]⟩ := by
        rw [hname, hk]; cases new; exact congrArg (Entry.mk _ _) hb
      have hab : a ≠ b := fun he => hne (hea.trans (he ▸ heb.symm))
      have hva := ho.1.output_values a (by simp [ha])
      have hvb := hn.1.output_values b (by simp [hb])
      have hkind : (old.name = ufName ∧ old.key.length = 1) ∨
          ∃ g, old.name = viewName g :=
        hrole.elim (fun hu => Or.inl ⟨hu, hnot.2.1.trans (hufarity hu)⟩) Or.inr
      rw [hdc, ha, hb] at hm
      cases hm with
      | unchanged hm hconf =>
        simp only [tableDecl, Option.some.injEq, MergeSpec.merge.injEq] at hm
        rcases hm with ⟨rfl, rfl, rfl, rfl⟩
        exact (hab (by simpa [MergeConflict, FnDecl.unchangedWidth, tableDecl, mergeBody]
          using hconf)).elim
      | changed hm _ hbody hres =>
        simp only [tableDecl, Option.some.injEq, MergeSpec.merge.injEq] at hm
        rcases hm with ⟨rfl, rfl, rfl, rfl⟩
        rw [Live.eval_mergeBody (d := (d.eraseEntry old).eraseEntry new)
          huf a b hva hvb] at hbody
        cases hbody
        have hvs : vs = [lowerId a b] := by
          simpa [mergeResult, Expr.evalList, Expr.eval, mergeEnv, Env.lookup,
            Option.filter, hva, hvb, lowerId_eq_least] using hres.symm
        subst vs
        refine ⟨old.name, old.key, a, b, hea ▸ ho, heb ▸ hn, hkind, ?_⟩
        rw [hea, heb]
        rfl

/-- Equal view keys justify congruence of the two retained outputs. -/
theorem entrySound_collide {src : Database} {f : FnName} {cs : List Term} {a b : Term}
    (ha : EntrySound src f cs a) (hb : EntrySound src f cs b) : Cong src a b := by
  obtain ⟨as, ham, hal, hae⟩ := ha
  obtain ⟨bs, hbm, hbl, hbe⟩ := hb
  exact hae.symm.trans ((Cong.congr ham hbm (hal.trans hbl.symm)).trans hbe)

/-- A merge only relates outputs that are already source-congruent. -/
theorem mergeStep_soundTerms {src d e : Database} (hshape : MergeShape d.sig)
    (hd : d.Diag) (hw : d.WF) (hstore : d.StoreOk)
    (huf : d.sig ufName = some (tableDecl 1)) (hs : SoundTerms d src)
    (hstep : MergeStep d e) : SoundTerms e src := by
  obtain ⟨f, cs, a, b, hrowa, hrowb, hkind, rfl⟩ :=
    mergeStep_form hshape hd huf hstep
  have hta : Term.app f (cs ++ [a]) ∈ d.terms := .assert hrowa.2
  have htb : Term.app f (cs ++ [b]) ∈ d.terms := .assert hrowb.2
  let base := (d.eraseEntry ⟨f, cs, [a]⟩).eraseEntry ⟨f, cs, [b]⟩
  have hbase : base.Contained d := (Database.Contained.eraseEntry _ _).trans
    (Database.Contained.eraseEntry _ _)
  have hwbase : base.WF := (hw.eraseEntry hstore _ hrowa.1).eraseEntry
    (hstore.eraseEntry _ hrowa.1) _ hrowb.1
  have kept : ∀ t, t.IsValue d.sig → t ∈ d.terms → t ∈ base.terms := fun t hv ht =>
    Database.mem_terms_eraseEntry_of_value hrowb.1 hv
      (Database.mem_terms_eraseEntry_of_value hrowa.1 hv ht)
  have ha := kept a (hrowa.1.output_values a (by simp))
    (Database.mem_terms_of_arg hw hta (by simp : a ∈ cs ++ [a]))
  have hb := kept b (hrowb.1.output_values b (by simp))
    (Database.mem_terms_of_arg hw htb (by simp : b ∈ cs ++ [b]))
  have hab : Cong src a b := by
    rcases hkind with ⟨rfl, hk⟩ | ⟨g, rfl⟩
    · obtain ⟨key, rfl⟩ := List.length_eq_one_iff.mp hk
      exact (hs.2 key a hta).symm.trans (hs.2 key b htb)
    · exact entrySound_collide (hs.1 g cs a hta) (hs.1 g cs b htb)
  have hsurv : Term.app f (cs ++ [lowerId a b]) ∈ d.terms := by
    rcases lowerId_eq_or a b with he | he <;> rw [he] <;> assumption
  apply ((hs.mono_terms hbase.terms).mergeLinks hwbase ha hb hab).addTerm
  · exact fun g ks v hm => hs.1 g ks v (hw.subtermClosed _ hsurv hm)
  · exact fun x y hm => hs.2 x y (hw.subtermClosed _ hsurv hm)

/-- The minimum links descend, and the surviving table row was already present. -/
theorem mergeStep_descending {d e : Database} (hshape : MergeShape d.sig)
    (hd : d.Diag) (hw : d.WF) (hstore : d.StoreOk)
    (huf : d.sig ufName = some (tableDecl 1)) (hs : Descending d)
    (hstep : MergeStep d e) : Descending e := by
  obtain ⟨f, cs, a, b, hrowa, hrowb, _, rfl⟩ := mergeStep_form hshape hd huf hstep
  have hta : Term.app f (cs ++ [a]) ∈ d.terms := .assert hrowa.2
  have htb : Term.app f (cs ++ [b]) ∈ d.terms := .assert hrowb.2
  let base := (d.eraseEntry ⟨f, cs, [a]⟩).eraseEntry ⟨f, cs, [b]⟩
  have hbase : base.Contained d := (Database.Contained.eraseEntry _ _).trans
    (Database.Contained.eraseEntry _ _)
  have hwbase : base.WF := (hw.eraseEntry hstore _ hrowa.1).eraseEntry
    (hstore.eraseEntry _ hrowa.1) _ hrowb.1
  have kept : ∀ t, t.IsValue d.sig → t ∈ d.terms → t ∈ base.terms := fun t hv ht =>
    Database.mem_terms_eraseEntry_of_value hrowb.1 hv
      (Database.mem_terms_eraseEntry_of_value hrowa.1 hv ht)
  have ha := kept a (hrowa.1.output_values a (by simp))
    (Database.mem_terms_of_arg hw hta (by simp : a ∈ cs ++ [a]))
  have hb := kept b (hrowb.1.output_values b (by simp))
    (Database.mem_terms_of_arg hw htb (by simp : b ∈ cs ++ [b]))
  have hsurv : Term.app f (cs ++ [lowerId a b]) ∈ d.terms := by
    rcases lowerId_eq_or a b with he | he <;> rw [he] <;> assumption
  have hl := (hs.mono_terms hbase.terms).mergeLinks hwbase ha hb
  intro x y hm
  rcases Database.addTerm_terms ▸ hm with hm | hm
  · exact hl x y hm
  · exact hs x y (hw.subtermClosed _ hsurv hm)

/-- Generated merge bodies have legal writes and exactly one result. -/
theorem mergeShape_mergesLegal {sig : Signature} (h : MergeShape sig) :
    sig.MergesLegal := by
  intro f dc oldVars newVars body res hdc hm
  obtain ⟨_, rfl, rfl, ho, _⟩ := h f dc hdc body res hm
  exact ⟨⟨trivial, trivial, trivial⟩, ho.symm⟩

/-- The body writes complete two-column UF entries. -/
theorem mergeShape_mergesWidthOk {sig : Signature} (h : MergeShape sig)
    (hu : sig ufName = some (tableDecl 1)) : sig.MergesWidthOk := by
  intro f dc ms hd hm
  cases ms with
  | merge oldVars newVars body res =>
      obtain ⟨_, rfl, rfl, ho, _⟩ := h f dc hd body res hm
      simp [MergeSpec.WidthOk, mergeResult, mergeBody, ho, Action.WidthOk,
        Expr.AtomWidthOk, Expr.WidthOk, Expr.WidthOkList, hu, tableDecl, FnDecl.entryWidth]

/-- Arbitrary finite choices of generated collisions preserve source justification. -/
theorem mergeClosure_soundTerms {src d e : Database} (hshape : MergeShape d.sig)
    (hd : d.Diag) (hw : d.WF) (hstore : d.StoreOk)
    (huf : d.sig ufName = some (tableDecl 1)) (hs : SoundTerms d src)
    (hcl : MergeClosure d e) : SoundTerms e src := by
  induction hcl with
  | refl => exact hs
  | @tail mid e hcl hstep ih =>
      have hshape' : MergeShape mid.sig := by rw [MergeClosure.sig hcl]; exact hshape
      have huf' : mid.sig ufName = some (tableDecl 1) := by rw [MergeClosure.sig hcl]; exact huf
      exact mergeStep_soundTerms hshape' (MergeClosure.diag hshape.unionFree hd hcl)
        (MergeClosure.wf hw hstore (mergeShape_mergesWidthOk hshape huf) hcl)
        (MergeClosure.storeOk hcl hstore (mergeShape_mergesWidthOk hshape huf)) huf' ih hstep

/-- Merge scheduling cannot create an upward UF link. -/
theorem mergeClosure_descending {d e : Database} (hshape : MergeShape d.sig)
    (hd : d.Diag) (hw : d.WF) (hstore : d.StoreOk)
    (huf : d.sig ufName = some (tableDecl 1)) (hs : Descending d)
    (hcl : MergeClosure d e) : Descending e := by
  induction hcl with
  | refl => exact hs
  | @tail mid e hcl hstep ih =>
      have hshape' : MergeShape mid.sig := by rw [MergeClosure.sig hcl]; exact hshape
      have huf' : mid.sig ufName = some (tableDecl 1) := by rw [MergeClosure.sig hcl]; exact huf
      exact mergeStep_descending hshape' (MergeClosure.diag hshape.unionFree hd hcl)
        (MergeClosure.wf hw hstore (mergeShape_mergesWidthOk hshape huf) hcl)
        (MergeClosure.storeOk hcl hstore (mergeShape_mergesWidthOk hshape huf)) huf' ih hstep

end Egglog.Congruence.Abstract
