import EgglogSemantics.Proofs.Congruence.AbstractState
import EgglogSemantics.Proofs.Congruence.IdOrder
import EgglogSemantics.Proofs.Congruence.MetadataSyntax
import EgglogSemantics.Proofs.DiagonalPreservation
import EgglogSemantics.Proofs.StatePreservation

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

/-- Any mathematical generated-table collision has the concrete two-link form.
The row-width invariant rules out malformed output tuples. -/
theorem mergeStep_form {d e : Database} (hshape : MergeShape d.sig) (hd : d.Diag)
    (hdt : d.DeclaredTerms) (huf : d.sig ufName = some (tableDecl 1))
    (hstep : MergeStep d e) :
    ∃ f cs a b,
      Term.app f (cs ++ [a]) ∈ d.terms ∧ Term.app f (cs ++ [b]) ∈ d.terms ∧
      ((f = ufName ∧ cs.length = 1) ∨ ∃ g, f = viewName g) ∧
      e = (mergeLinks d a b).addTerm (.app f (cs ++ [lowerId a b])) := by
  cases hstep with
  | @collide post f dc cs ds as bs vs oldVars newVars body res
      hsig hm _ hcs _ hrowa hrowb hkeys hbody hres =>
    obtain ⟨hname, rfl, rfl, hout, hufarity, _, rfl, rfl⟩ :=
      hshape f dc hsig body res hm
    have hnot : dc.merge ≠ none := by rw [hm]; simp
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp
      ((outLength_of_declaredTerms hdt hsig hnot hcs hrowa).trans hout)
    have hkeys' : cs = ds := CongList.eq_of_diag hd hkeys
    subst ds
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp
      ((outLength_of_declaredTerms hdt hsig hnot hcs hrowb).trans hout)
    have hbody' : evalActions { d with env := mergeEnv ["old"] ["new"] [a] [b] }
        mergeBody = some (mergeLinks { d with env := mergeEnv ["old"] ["new"] [a] [b] }
          a b) := by
      simp [mergeBody, mergeLinks, mergeEnv_pair, evalActions, evalAction, Expr.evalAtom,
        Expr.evalList, Expr.eval, Env.lookup, huf, lowerId, Term.least]
    obtain rfl := Option.some.inj (hbody'.symm.trans hbody)
    have hvs : vs = [lowerId a b] := by
      simpa [mergeLinks, mergeResult, Expr.evalList, Expr.eval, mergeEnv_pair,
        Env.lookup, lowerId, Term.least] using hres.symm
    subst vs
    refine ⟨f, cs, a, b, hrowa, hrowb, ?_, ?_⟩
    · exact hname.elim (fun hu => Or.inl ⟨hu, hcs.trans (hufarity hu)⟩) Or.inr
    · rfl

/-- Equal view keys justify congruence of the two retained outputs. -/
theorem entrySound_collide {src : Database} {f : FnName} {cs : List Term} {a b : Term}
    (ha : EntrySound src f cs a) (hb : EntrySound src f cs b) : Cong src a b := by
  obtain ⟨as, ham, hal, hae⟩ := ha
  obtain ⟨bs, hbm, hbl, hbe⟩ := hb
  exact hae.symm.trans ((Cong.congr ham hbm (hal.trans hbl.symm)).trans hbe)

/-- A merge only relates outputs that are already source-congruent. -/
theorem mergeStep_soundTerms {src d e : Database} (hshape : MergeShape d.sig)
    (hd : d.Diag) (hw : d.WF) (hdt : d.DeclaredTerms)
    (huf : d.sig ufName = some (tableDecl 1)) (hs : SoundTerms d src)
    (hstep : MergeStep d e) : SoundTerms e src := by
  obtain ⟨f, cs, a, b, hrowa, hrowb, hkind, rfl⟩ :=
    mergeStep_form hshape hd hdt huf hstep
  have ha := Database.mem_terms_of_arg hw hrowa (by simp : a ∈ cs ++ [a])
  have hb := Database.mem_terms_of_arg hw hrowb (by simp : b ∈ cs ++ [b])
  have hab : Cong src a b := by
    rcases hkind with ⟨rfl, hk⟩ | ⟨g, rfl⟩
    · obtain ⟨key, rfl⟩ := List.length_eq_one_iff.mp hk
      exact (hs.2 key a hrowa).symm.trans (hs.2 key b hrowb)
    · exact entrySound_collide (hs.1 g cs a hrowa) (hs.1 g cs b hrowb)
  have hsurv : Term.app f (cs ++ [lowerId a b]) ∈ d.terms := by
    rcases lowerId_eq_or a b with he | he <;> rw [he] <;> assumption
  exact (hs.mergeLinks hw ha hb hab).addTerm_of_mem (mergeLinks_wf hw a b)
    (mem_terms_of_mergeLinks hsurv)

/-- The minimum links descend, and the surviving table row was already present. -/
theorem mergeStep_descending {d e : Database} (hshape : MergeShape d.sig)
    (hd : d.Diag) (hw : d.WF) (hdt : d.DeclaredTerms)
    (huf : d.sig ufName = some (tableDecl 1)) (hs : Descending d)
    (hstep : MergeStep d e) : Descending e := by
  obtain ⟨f, cs, a, b, hrowa, hrowb, _, rfl⟩ := mergeStep_form hshape hd hdt huf hstep
  have ha := Database.mem_terms_of_arg hw hrowa (by simp : a ∈ cs ++ [a])
  have hb := Database.mem_terms_of_arg hw hrowb (by simp : b ∈ cs ++ [b])
  have hsurv : Term.app f (cs ++ [lowerId a b]) ∈ d.terms := by
    rcases lowerId_eq_or a b with he | he <;> rw [he] <;> assumption
  exact (hs.mergeLinks hw ha hb).addTerm_of_mem (mergeLinks_wf hw a b)
    (mem_terms_of_mergeLinks hsurv)

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
    (hd : d.Diag) (hw : d.WF) (hdt : d.DeclaredTerms)
    (huf : d.sig ufName = some (tableDecl 1)) (hs : SoundTerms d src)
    (hcl : MergeClosure d e) : SoundTerms e src := by
  induction hcl with
  | refl => exact hs
  | @tail mid e hcl hstep ih =>
      have hshape' : MergeShape mid.sig := by rw [MergeClosure.sig hcl]; exact hshape
      have huf' : mid.sig ufName = some (tableDecl 1) := by rw [MergeClosure.sig hcl]; exact huf
      exact mergeStep_soundTerms hshape' (MergeClosure.diag hshape.unionFree hd hcl)
        (MergeClosure.wf hw hcl)
        (mergeClosure_declaredTerms hw hdt (mergeShape_mergesLegal hshape)
          (mergeShape_mergesWidthOk hshape huf) hcl) huf' ih hstep

/-- Merge scheduling cannot create an upward UF link. -/
theorem mergeClosure_descending {d e : Database} (hshape : MergeShape d.sig)
    (hd : d.Diag) (hw : d.WF) (hdt : d.DeclaredTerms)
    (huf : d.sig ufName = some (tableDecl 1)) (hs : Descending d)
    (hcl : MergeClosure d e) : Descending e := by
  induction hcl with
  | refl => exact hs
  | @tail mid e hcl hstep ih =>
      have hshape' : MergeShape mid.sig := by rw [MergeClosure.sig hcl]; exact hshape
      have huf' : mid.sig ufName = some (tableDecl 1) := by rw [MergeClosure.sig hcl]; exact huf
      exact mergeStep_descending hshape' (MergeClosure.diag hshape.unionFree hd hcl)
        (MergeClosure.wf hw hcl)
        (mergeClosure_declaredTerms hw hdt (mergeShape_mergesLegal hshape)
          (mergeShape_mergesWidthOk hshape huf) hcl) huf' ih hstep

end Egglog.Congruence.Abstract
