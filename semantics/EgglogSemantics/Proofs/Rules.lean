import EgglogSemantics.Proofs.Merge

/-! Exactly which rules a command or program registers. -/

namespace Egglog.FDatabase

/-- Only a rule command extends the rule store; evaluation never changes the rule itself. -/
theorem execCmdM_mem_rules_iff {d e : FDatabase} {c : Cmd}
    (h : d.execCmdM c = some e) (r : Rule) :
    r ∈ e.rules ↔ r ∈ d.rules ∨ c = .rule r := by
  cases c with
  | decl f dc =>
      obtain rfl := Option.some.inj h
      simp
  | rule s =>
      obtain rfl := Option.some.inj h
      simp [List.mem_cons, or_comm, eq_comm]
  | action a =>
      obtain ⟨m, ha, hm⟩ := Option.bind_eq_some_iff.mp h
      rw [(mergeSaturateF_fields hm).2.2, execAction_rules ha]
      simp
  | run R => rw [(runRoundM_fields h).2.2]; simp
  | saturate R => rw [(runSaturateM_fields runFuel h).2.2]; simp

/-- A program's final rule store consists of its initial rules and all rule commands. -/
theorem execProgramM_mem_rules_iff {p : Program} :
    ∀ {d e : FDatabase}, d.execProgramM p = some e → ∀ r : Rule,
      r ∈ e.rules ↔ r ∈ d.rules ∨ Cmd.rule r ∈ p := by
  induction p with
  | nil =>
      intro d e h r
      obtain rfl := Option.some.inj h
      simp
  | cons c cs ih =>
      intro d e h r
      obtain ⟨m, hc, hm⟩ := Option.bind_eq_some_iff.mp h
      rw [ih hm r, execCmdM_mem_rules_iff hc r]
      simp [List.mem_cons, eq_comm, or_assoc]

/-- Registered rules persist through every command. -/
theorem execCmdM_rules_mono {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d') :
    ∀ r ∈ d.rules, r ∈ d'.rules :=
  fun r hr => (execCmdM_mem_rules_iff hs r).mpr (Or.inl hr)

/-- Registered rules persist through every program block. -/
theorem execProgramM_rules_mono {p : Program} {d D : FDatabase}
    (hs : d.execProgramM p = some D) : ∀ r ∈ d.rules, r ∈ D.rules :=
  fun r hr => (execProgramM_mem_rules_iff hs r).mpr (Or.inl hr)

end Egglog.FDatabase
