import EgglogSemantics.Provenance.Facts
import EgglogSemantics.Provenance.Extract

namespace Egglog.Provenance

private theorem option_true {b : Option Bool} (h : b.getD false = true) : b = some true := by
  cases b with
  | none => simp at h
  | some b => simpa using h

private theorem lookup_subset {prior : List Term} {ids : List Nat} {ts : List Term}
    (h : ids.mapM (fun i => prior[i]?) = some ts) : ts ⊆ prior := by
  induction ids generalizing ts with
  | nil => cases Option.some.inj h; simp
  | cons i ids ih =>
    rw [List.mapM_cons] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hr, heq⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj heq
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_of_getElem? ht
    · exact ih hr hx

theorem checkNode_sound {P : Program} {C : SourceProof.Context} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF) (hC : C.Sound db)
    (hclosed : ∀ R, RunSaturated R db) {prior : List Term}
    (hp : ∀ t ∈ prior, t ∈ db.terms) {n : Node}
    (h : checkNode P C prior n = true) : n.fact ∈ db.terms := by
  simp only [checkNode, Bool.and_eq_true_iff] at h
  have hr := h.1.2
  cases hn : n.reason with
  | global i =>
    have hg : (⟨n.fact, n.fact⟩ : SourceProof.Claim) ∈ C.globals := by
      simpa only [hn, decide_eq_true_eq] using h.2
    exact hC.globals _ hg
  | rule i σ ids =>
    simp only [checkReason, hn] at hr
    obtain ⟨cmd, hcmd, hr⟩ := Option.bind_eq_some_iff.mp (option_true hr)
    cases cmd with
    | rule r =>
      obtain ⟨ts, hts, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨fs, hfs, hr⟩ := Option.bind_eq_some_iff.mp hr
      have hf : n.fact ∈ fs := by simpa using hr
      rw [hC.sig] at hfs
      exact ruleFacts_sound hs hw hclosed (List.mem_of_getElem? hcmd)
        (fun t ht => hp t (lookup_subset hts ht)) hfs n.fact hf
    | action _ | run _ | saturate _ | decl _ _ => simp at hr
  | merge f i j =>
    simp only [checkReason, hn] at hr
    obtain ⟨old, ho, hr⟩ := Option.bind_eq_some_iff.mp (option_true hr)
    obtain ⟨new, hn, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨fs, hfs, hr⟩ := Option.bind_eq_some_iff.mp hr
    have hf : n.fact ∈ fs.body ∨ n.fact ∈ fs.result.subtermList := by simpa using hr
    rw [hC.sig] at hfs
    exact mergeFacts_sound hw (hclosed "").2
      (hp old (List.mem_of_getElem? ho)) (hp new (List.mem_of_getElem? hn)) hfs n.fact hf
  | subterm i =>
    simp only [checkReason, hn] at hr
    obtain ⟨parent, hm, hr⟩ := Option.bind_eq_some_iff.mp (option_true hr)
    have hf : n.fact ∈ parent.subtermList := by simpa using hr
    exact hw.subtermClosed parent (hp parent (List.mem_of_getElem? hm))
      ((Term.mem_subtermList parent).mp hf)

theorem checkNodes_sound {P : Program} {C : SourceProof.Context} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF) (hC : C.Sound db)
    (hclosed : ∀ R, RunSaturated R db) {prior : List Term}
    (hp : ∀ t ∈ prior, t ∈ db.terms) {ns : List Node} {ts : List Term}
    (h : checkNodes P C prior ns = some ts) : ∀ t ∈ ts, t ∈ db.terms := by
  induction ns generalizing prior with
  | nil => cases Option.some.inj h; exact hp
  | cons n ns ih =>
    simp only [checkNodes] at h
    split at h
    · rename_i hn
      apply ih _ h
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hp t ht
      · simp only [List.mem_singleton] at ht
        subst t
        exact checkNode_sound hs hw hC hclosed hp hn
    · contradiction

/-- Every accepted relational fact exists in the original program's saturated state. -/
theorem check_sound {P : Program} {db : Database} {cert : Certificate} {t : Term}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db) (h : check P cert = some t) : t ∈ db.terms := by
  unfold check at h
  split at h
  · contradiction
  · obtain ⟨C, hC, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ts, hts, ht⟩ := Option.bind_eq_some_iff.mp h
    exact checkNodes_sound hs hw (SourceProof.contextOf_sound hC hs) hclosed
      (by simp) hts t (List.mem_of_getElem? ht)

theorem extractRow_checked {P : Program} {C : SourceProof.Context} {r : Row}
    {d : FnDecl} {fuel : Nat} {cert : Certificate}
    (hC : SourceProof.contextOf P = some C) (hd : C.sig r.fn = some d)
    (h : extractRow P r fuel = some cert) :
    check P cert = some (.app r.fn (r.args ++ r.out.take d.outArity)) := by
  simp only [extractRow, hC, Option.bind_eq_bind, Option.bind_some, hd] at h
  split at h
  · contradiction
  · obtain ⟨pf, _, hpf⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cert', _, hcert⟩ := Option.bind_eq_some_iff.mp hpf
    split at hcert
    · rename_i hcheck
      cases Option.some.inj hcert
      simpa only [beq_iff_eq] using hcheck
    · contradiction

/-- Successful extraction establishes the row's data fact, independently of its metadata. -/
theorem extractRow_sound {P : Program} {C : SourceProof.Context} {db : Database}
    {r : Row} {d : FnDecl} {fuel : Nat} {cert : Certificate}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db)
    (hC : SourceProof.contextOf P = some C) (hd : C.sig r.fn = some d)
    (h : extractRow P r fuel = some cert) :
    Term.app r.fn (r.args ++ r.out.take d.outArity) ∈ db.terms :=
  check_sound hs hw hclosed (extractRow_checked hC hd h)

end Egglog.Provenance
