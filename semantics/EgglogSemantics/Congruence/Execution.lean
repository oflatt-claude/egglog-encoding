import EgglogSemantics.Congruence.Signature

/-! Basic execution invariants. Declarations occur before any data is written, and
all later merge results have the declared width. -/

namespace Egglog.Congruence

theorem actions_writeLegal (as : List Action) (sig : Signature) :
    Actions.WriteLegal as sig := by
  induction as with
  | nil => exact ⟨trivial, trivial⟩
  | cons a as ih => exact ⟨⟨by cases a <;> trivial, ih.1⟩, ⟨trivial, ih.2⟩⟩

private theorem cmd_writeLegal (c : Cmd) (sig : Signature) : c.WriteLegal sig := by
  cases c with
  | action a => exact ⟨by cases a <;> trivial, trivial⟩
  | rule r => exact actions_writeLegal r.actions sig
  | _ => trivial

private theorem maintenance_setup (P : Program) :
    ∀ c ∈ maintenanceRules P, c.command.DeclOrRule := by
  intro c hc
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · trivial
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩ <;> trivial

private theorem allMaintenance_setup (P : Program) :
    ∀ c ∈ allMaintenanceRules P, c.command.DeclOrRule := by
  intro c hc
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenance_setup P c hc
  · have h := maintenance_setup P c hc
    unfold inRuleset
    split <;> simp_all only [Cmd.DeclOrRule]

theorem prelude_setup (P : Program) :
    ∀ c ∈ (encodePrelude P).map Command.command, c.DeclOrRule := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simp only [encodePrelude, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false] at hd
  rcases hd with (rfl | ⟨⟨f, k⟩, _, hd⟩) | hd
  · trivial
  · rcases hd with rfl | rfl <;> trivial
  · exact allMaintenance_setup P d hd

def NoDecl : Cmd → Prop
  | .decl _ _ => False
  | _ => True

private theorem cmd_noDecl (i : Nat) (c : Cmd) :
    ∀ d ∈ encodeCmd i c, NoDecl d.command := by
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

theorem cmds_noDecl (P : Program) (i : Nat) :
    ∀ c ∈ (encodeCmds P i).map Command.command, NoDecl c := by
  have hall : ∀ d ∈ encodeCmds P i, NoDecl d.command := by
    induction P generalizing i with
    | nil => simp [encodeCmds]
    | cons c cs ih =>
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact cmd_noDecl i c d hd
        · exact ih (i + 1) d hd
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact hall d hd

theorem execCmd_inv {d e : FDatabase} {c : Cmd} (hc : NoDecl c)
    (hi : d.Inv) (hs : MergeShape d.sig) (h : d.execCmdM c = some e) : e.Inv :=
  hi.execCmdM (cmd_writeLegal c d.sig) hs.mergesLegal
    (by cases c <;> trivial) (fun r _ => actions_writeLegal r.actions d.sig) h

theorem execProgram_inv {p : Program} (hp : ∀ c ∈ p, NoDecl c) :
    ∀ {d e : FDatabase}, d.Inv → MergeShape d.sig → d.execProgramM p = some e → e.Inv := by
  induction p with
  | nil =>
      intro d e hi _ h
      obtain rfl := Option.some.inj h
      exact hi
  | cons c cs ih =>
      intro d e hi hs h
      obtain ⟨m, hm, hrest⟩ := Option.bind_eq_some_iff.mp h
      have hc := hp c List.mem_cons_self
      exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc'))
        (execCmd_inv hc hi hs hm)
        (execCmd_mergeShape (by cases c <;> trivial) hs hm) hrest

/-- Every successful compiled execution has a well-formed denotation and a sound,
correctly sized live row index. No source-fragment assumptions are needed here. -/
theorem execM_encode_inv {P : Program} {tgt : FDatabase}
    (h : execM (encode P) = some tgt) : tgt.Inv := by
  change FDatabase.empty.execProgramM _ = some tgt at h
  rw [encode, compile, List.map_append] at h
  obtain ⟨d, hpre, hrest⟩ := FDatabase.execProgramM_append h
  obtain ⟨ht, hr, he, hv⟩ := execProgramM_data_of_declOrRule (prelude_setup P) hpre
  have hs : MergeShape d.sig := execProgram_mergeShape
    (fun c hc => encode_commandShape P c (by
      simp only [encode, compile, List.map_append, List.mem_append]
      exact Or.inl hc)) MergeShape.empty hpre
  exact execProgram_inv (cmds_noDecl P 0) (FDatabase.Inv.of_empty_data ht hr he hv) hs hrest

end Egglog.Congruence
