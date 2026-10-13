import EgglogSemantics.Proofs.Congruence.Properties

/-! Declaration invariants for the generated single-output tables. -/

namespace Egglog.Congruence

/-- A merging declaration has the generated body, one output, and no special identity
columns. Only UF and constructor views merge; UF has one key. -/
def DeclShape (f : FnName) (dc : FnDecl) : Prop :=
  ∀ body res, dc.merge = some (.merge body res) →
    (f = ufName ∨ ∃ g, f = viewName g) ∧ body = mergeBody ∧ res = mergeResult ∧
      dc.outArity = 1 ∧ (f = ufName → dc.arity = 1) ∧ dc.identityVals = none

def MergeShape (sig : Signature) : Prop :=
  ∀ f dc, sig f = some dc → DeclShape f dc

def CommandShape : Cmd → Prop
  | .decl f dc => DeclShape f dc
  | _ => True

theorem MergeShape.empty : MergeShape (fun _ => none) := by
  intro f dc h
  contradiction

theorem MergeShape.update {sig : Signature} (h : MergeShape sig) {f : FnName}
    {dc : FnDecl} (hc : DeclShape f dc) :
    MergeShape (Function.update sig f (some dc)) := by
  intro g dcg hg
  rw [Function.update_apply] at hg
  by_cases hgf : g = f
  · subst g
    obtain rfl : dcg = dc := by simpa [eq_comm] using hg
    exact hc
  · rw [if_neg hgf] at hg
    exact h g dcg hg

theorem execCmd_mergeShape {d e : FDatabase} {c : Cmd} (hc : CommandShape c)
    (h : MergeShape d.sig) (hs : d.execCmdM c = some e) : MergeShape e.sig := by
  rw [FDatabase.execCmdM_sig hs]
  cases c with
  | decl f dc => exact h.update hc
  | _ => exact h

theorem execProgram_mergeShape {p : Program} (hp : ∀ c ∈ p, CommandShape c) :
    ∀ {d e : FDatabase}, MergeShape d.sig → d.execProgramM p = some e → MergeShape e.sig := by
  induction p with
  | nil =>
      intro d e h he
      obtain rfl := Option.some.inj he
      exact h
  | cons c cs ih =>
      intro d e h he
      obtain ⟨m, hm, hrest⟩ := Option.bind_eq_some_iff.mp he
      exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc'))
        (execCmd_mergeShape (hp c List.mem_cons_self) h hm) hrest

private theorem maintenance_shape (P : Program) :
    ∀ c ∈ maintenanceRules P, CommandShape c.command := by
  intro c hc
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · trivial
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩ <;> trivial

private theorem allMaintenance_shape (P : Program) :
    ∀ c ∈ allMaintenanceRules P, CommandShape c.command := by
  intro c hc
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenance_shape P c hc
  · have h := maintenance_shape P c hc
    unfold inRuleset
    split <;> simp_all only [CommandShape]

private theorem prelude_shape (P : Program) :
    ∀ c ∈ encodePrelude P, CommandShape c.command := by
  intro c hc
  simp only [encodePrelude, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | ⟨⟨f, k⟩, _, hc⟩) | hc
  · intro body res he
    obtain ⟨rfl, rfl⟩ : mergeBody = body ∧ mergeResult = res := by
      simpa [tableDecl] using he
    exact ⟨Or.inl rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
  · rcases hc with rfl | rfl
    · intro body res he
      simp [skolemDecl] at he
    · intro body res he
      obtain ⟨rfl, rfl⟩ : mergeBody = body ∧ mergeResult = res := by
        simpa [tableDecl] using he
      exact ⟨Or.inr ⟨f, rfl⟩, rfl, rfl, rfl,
        fun hu => False.elim (viewName_ne_ufName hu), rfl⟩
  · exact allMaintenance_shape P c hc

private theorem cmd_shape (i : Nat) (c : Cmd) :
    ∀ d ∈ encodeCmd i c, CommandShape d.command := by
  intro d hd
  cases c with
  | decl _ _ => simp [encodeCmd] at hd
  | rule r =>
      simp only [encodeCmd, List.mem_singleton] at hd
      subst d
      trivial
  | action a =>
      simp only [encodeCmd, List.mem_append, List.mem_map, List.mem_singleton] at hd
      rcases hd with ⟨a', _, rfl⟩ | rfl <;> trivial
  | run R | saturate R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> trivial

private theorem cmds_shape (P : Program) (i : Nat) :
    ∀ c ∈ encodeCmds P i, CommandShape c.command := by
  induction P generalizing i with
  | nil => simp [encodeCmds]
  | cons c cs ih =>
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact cmd_shape i c d hd
      · exact ih (i + 1) d hd

theorem encode_commandShape (P : Program) : ∀ c ∈ encode P, CommandShape c := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hd with hd | hd
  · exact prelude_shape P d hd
  · exact cmds_shape P 0 d hd

theorem execM_encode_mergeShape {P : Program} {tgt : FDatabase}
    (h : execM (encode P) = some tgt) : MergeShape tgt.sig :=
  execProgram_mergeShape (encode_commandShape P) MergeShape.empty h

/-- Complete atoms make body writes legal independently of the signature; the declared
output count also agrees with the merge result. -/
theorem MergeShape.mergesLegal {sig : Signature} (h : MergeShape sig) :
    Signature.MergesLegal sig := by
  intro f dc body res hdc hm
  obtain ⟨-, rfl, rfl, ho, -, -⟩ := h f dc hdc body res hm
  exact ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, ho.symm⟩

/-- Every generated merge body records a UF entry without asserting a built-in union. -/
theorem MergeShape.unionFree {sig : Signature} (h : MergeShape sig) : sig.UnionFree := by
  intro f dc hd ms hm
  cases ms with
  | noMerge => trivial
  | merge body res =>
      have hb := (h f dc hd body res hm).2.1
      rw [hb]
      exact ⟨trivial, trivial⟩

end Egglog.Congruence
