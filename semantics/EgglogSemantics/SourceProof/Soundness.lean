import EgglogSemantics.SourceProof.Rules

namespace Egglog.SourceProof

private theorem option_true {b : Option Bool} (h : b.getD false = true) : b = some true := by
  cases b with
  | none => simp at h
  | some b => simpa using h

private theorem lookupClaims_subset {prior : List Claim} {ids : List Nat} {cs : List Claim}
    (h : ids.mapM (fun i => prior[i]?) = some cs) : cs ⊆ prior := by
  induction ids generalizing cs with
  | nil => cases Option.some.inj h; simp
  | cons i ids ih =>
      rw [List.mapM_cons] at h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hr, heq⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj heq
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_of_getElem? hc
      · exact ih hr hx

theorem checkReason_supported {P : Program} {C : Context} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF) (hC : C.Sound db)
    (hclosed : ∀ R, RunSaturated R db) (hok : sourceOk P = true)
    {prior : List Claim} (hp : ∀ c ∈ prior, c.Supported db) {n : Node}
    (h : checkReason P C prior n = true) : n.claim.Supported db := by
  cases hn : n.reason with
  | fiat =>
      simp only [checkReason, hn, Option.getD_some, decide_eq_true_eq] at h
      exact (hC.globals n.claim h).supported hw
  | symm i =>
      simp only [checkReason, hn] at h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp (option_true h)
      simp only [Option.some.injEq, beq_iff_eq] at h
      rw [h]
      exact (hp c (List.mem_of_getElem? hc)).symm
  | trans i j =>
      simp only [checkReason, hn] at h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp (option_true h)
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Bool.and_eq_true_iff, beq_iff_eq] at h
      rw [h.2]
      apply (hp a (List.mem_of_getElem? ha)).trans
      simpa only [h.1] using hp b (List.mem_of_getElem? hb)
  | congr i k j =>
      simp only [checkReason, hn] at h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp (option_true h)
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      cases he : a.rhs with
      | lit l => simp [he] at h
      | app f args =>
          simp only [he] at h
          obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.some.injEq, Bool.and_eq_true_iff, beq_iff_eq] at h
          have hbase : Claim.Supported db ⟨a.lhs, .app f args⟩ := by
            rw [← he]; exact hp a (List.mem_of_getElem? ha)
          rw [h.2]
          exact hbase.congr (hp b (List.mem_of_getElem? hb)) (by rw [ht, h.1.1.1])
  | rule i σ ids =>
      simp only [checkReason, hn] at h
      obtain ⟨cmd, hcmd, h⟩ := Option.bind_eq_some_iff.mp (option_true h)
      cases cmd with
      | rule r =>
          obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨fs, hfs, h⟩ := Option.bind_eq_some_iff.mp h
          have hc : n.claim ∈ fs := by simpa using h
          have hr : Cmd.rule r ∈ P := List.mem_of_getElem? hcmd
          exact ruleFacts_supported hs hw hC hclosed hr (sourceOk_rule hok hr)
            (fun c hc => hp c (lookupClaims_subset hcs hc)) hfs n.claim hc
      | action _ | run _ | saturate _ | decl _ _ => simp at h

theorem checkNodes_supported {P : Program} {C : Context} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF) (hC : C.Sound db)
    (hclosed : ∀ R, RunSaturated R db) (hok : sourceOk P = true)
    {prior : List Claim} (hp : ∀ c ∈ prior, c.Supported db) {ns : List Node}
    {cs : List Claim} (h : checkNodes P C prior ns = some cs) :
    ∀ c ∈ cs, c.Supported db := by
  induction ns generalizing prior with
  | nil => cases Option.some.inj h; exact hp
  | cons n ns ih =>
      simp only [checkNodes] at h
      split at h
      · rename_i hn
        simp only [checkNode, Bool.and_eq_true_iff] at hn
        apply ih _ h
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hp c hc
        · simp only [List.mem_singleton] at hc
          subst c
          exact checkReason_supported hs hw hC hclosed hok hp hn.2
      · contradiction

/-- Accepted claims retain source existence witnesses, including intermediate terms. -/
theorem check_supported {P : Program} {db : Database} {cert : Certificate} {c : Claim}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db) (h : check P cert = some c) : c.Supported db := by
  unfold check at h
  split at h
  · contradiction
  · rename_i hok
    have hok' : sourceOk P = true := by simpa using hok
    obtain ⟨C, hC, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs, hcs, hc⟩ := Option.bind_eq_some_iff.mp h
    exact checkNodes_supported hs hw (contextOf_sound hC hs) hclosed hok'
      (by simp) hcs c (List.mem_of_getElem? hc)

/-- On endpoints held by the source, checking implies its original congruence relation. -/
theorem check_sound {P : Program} {db : Database} {cert : Certificate} {c : Claim}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db) (h : check P cert = some c)
    (hl : c.lhs ∈ db.terms) (hr : c.rhs ∈ db.terms) : Cong db c.lhs c.rhs :=
  (check_supported hs hw hclosed h).holds hw hl hr

end Egglog.SourceProof
