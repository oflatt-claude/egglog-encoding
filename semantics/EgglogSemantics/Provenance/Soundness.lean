import EgglogSemantics.Provenance.Facts
import EgglogSemantics.Provenance.Extract

namespace Egglog.Provenance

private theorem option_true {b : Option Bool} (h : b.getD false = true) : b = some true := by
  cases b with
  | none => simp at h
  | some b => simpa using h

theorem checkNode_sound {P : Program} {C : SourceProof.Context} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF) (hC : C.Sound db)
    (hclosed : ∀ R, RunSaturated R db) {pf : Proof}
    (hp : ∀ q ∈ pf.subproofs, q.fact ∈ db.terms)
    (h : checkNode P C pf = true) : pf.fact ∈ db.terms := by
  cases pf with
  | global t i =>
    simp only [checkNode, Proof.fact_global, Bool.and_eq_true_iff, decide_eq_true_eq] at h
    exact hC.globals _ h.2
  | rule t i σ ps =>
    simp only [checkNode, checkReason, Proof.fact_rule, Bool.and_eq_true_iff,
      Bool.and_true] at h
    obtain ⟨cmd, hcmd, hr⟩ := Option.bind_eq_some_iff.mp (option_true h.2)
    cases cmd with
    | rule r =>
      obtain ⟨fs, hfs, hr⟩ := Option.bind_eq_some_iff.mp hr
      have hf : t ∈ fs := by simpa using hr
      rw [hC.sig] at hfs
      refine ruleFacts_sound hs hw hclosed (List.mem_of_getElem? hcmd) ?_ hfs t hf
      intro u hu
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      exact hp q hq
    | action _ | run _ | saturate _ | decl _ _ => simp at hr
  | merge t f old new =>
    simp only [checkNode, checkReason, Proof.fact_merge, Bool.and_eq_true_iff,
      Bool.and_true] at h
    obtain ⟨fs, hfs, hr⟩ := Option.bind_eq_some_iff.mp (option_true h.2)
    have hf : t ∈ fs.body ∨ t ∈ fs.result.subtermList := by simpa using hr
    rw [hC.sig] at hfs
    exact mergeFacts_sound hw (hclosed "").2 (hp old (by simp [Proof.subproofs]))
      (hp new (by simp [Proof.subproofs])) hfs t hf
  | subterm t parent =>
    simp only [checkNode, checkReason, Proof.fact_subterm, Bool.and_eq_true_iff,
      Bool.and_true, decide_eq_true_eq] at h
    exact hw.subtermClosed parent.fact (hp parent (by simp [Proof.subproofs]))
      ((Term.mem_subtermList _).mp h.2)

mutual

theorem valid_sound {P : Program} {C : SourceProof.Context} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF) (hC : C.Sound db)
    (hclosed : ∀ R, RunSaturated R db) :
    (pf : Proof) → valid P C pf = true → pf.fact ∈ db.terms
  | .global t i, h => by
      simp only [valid] at h
      exact checkNode_sound hs hw hC hclosed (by simp [Proof.subproofs]) h
  | .rule t i σ ps, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      exact checkNode_sound hs hw hC hclosed (allValid_sound hs hw hC hclosed ps h.1) h.2
  | .merge t f p q, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      have ihp := valid_sound hs hw hC hclosed p h.1.1
      have ihq := valid_sound hs hw hC hclosed q h.1.2
      refine checkNode_sound hs hw hC hclosed ?_ h.2
      intro r hr
      simp only [Proof.subproofs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ihp
      · exact ihq
  | .subterm t p, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      have ih := valid_sound hs hw hC hclosed p h.1
      refine checkNode_sound hs hw hC hclosed ?_ h.2
      intro q hq
      simp only [Proof.subproofs, List.mem_singleton] at hq
      subst hq
      exact ih
termination_by structural pf => pf

theorem allValid_sound {P : Program} {C : SourceProof.Context} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF) (hC : C.Sound db)
    (hclosed : ∀ R, RunSaturated R db) :
    (ps : List Proof) → allValid P C ps = true → ∀ q ∈ ps, q.fact ∈ db.terms
  | [], _, _, hq => by simp at hq
  | p :: ps, h, q, hq => by
      simp only [allValid, Bool.and_eq_true_iff] at h
      rcases List.mem_cons.mp hq with hqp | hq
      · rw [hqp]
        exact valid_sound hs hw hC hclosed p h.1
      · exact allValid_sound hs hw hC hclosed ps h.2 q hq
termination_by structural ps => ps

end

/-- Every accepted relational fact exists in the original program's saturated state. -/
theorem check_sound {P : Program} {db : Database} {pf : Proof} {t : Term}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db) (h : check P pf = some t) : t ∈ db.terms := by
  unfold check at h
  split at h
  · contradiction
  · obtain ⟨C, hC, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hv
      cases Option.some.inj h
      exact valid_sound hs hw (SourceProof.contextOf_sound hC hs) hclosed pf hv
    · contradiction

theorem extractRow_checked {P : Program} {C : SourceProof.Context} {r : Row}
    {d : FnDecl} {pf : Proof}
    (hC : SourceProof.contextOf P = some C) (hd : C.sig r.fn = some d)
    (h : extractRow P r = some pf) :
    check P pf = some (.app r.fn (r.args ++ r.out.take d.outArity)) := by
  simp only [extractRow, hC, Option.bind_eq_bind, Option.bind_some, hd] at h
  split at h
  · contradiction
  · obtain ⟨t, _, ht⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨p, _, hp⟩ := Option.bind_eq_some_iff.mp ht
    split at hp
    · rename_i hcheck
      cases Option.some.inj hp
      simpa only [beq_iff_eq] using hcheck
    · contradiction

/-- Successful extraction establishes the row's data fact, independently of its metadata. -/
theorem extractRow_sound {P : Program} {C : SourceProof.Context} {db : Database}
    {r : Row} {d : FnDecl} {pf : Proof}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db)
    (hC : SourceProof.contextOf P = some C) (hd : C.sig r.fn = some d)
    (h : extractRow P r = some pf) :
    Term.app r.fn (r.args ++ r.out.take d.outArity) ∈ db.terms :=
  check_sound hs hw hclosed (extractRow_checked hC hd h)

end Egglog.Provenance
