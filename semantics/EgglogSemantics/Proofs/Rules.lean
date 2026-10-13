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

namespace Egglog

/-- A round leaves the **ruleset** alone too: `RunRules` is a `sUnion`, which takes `rules` from
the pre-state, and so is every merge step. This is what carries `UnionsInv.rules` across a
firing command, where the source's rules are the ones the target already holds encodings of. -/
theorem runStep_rules {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.rules = db.rules := (MergeClosure.envRules h).2

@[inherit_doc runStep_rules]
theorem runReach_rules {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : d.rules = db.rules := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [runStep_rules hstep, ih]

theorem cmdStep_rules_of_run {sd sd' : Database} {R : RulesetName}
    (h : CmdStep sd (.run R) sd') : sd'.rules = sd.rules := by
  obtain ⟨d, hreach, hcl⟩ := h
  have hd : some (RunRules R sd) = some d := hreach
  rw [(MergeClosure.envRules hcl).2, ← Option.some.inj hd]
  rfl

theorem cmdStep_rules_of_saturate {sd sd' : Database} {R : RulesetName}
    (h : CmdStep sd (.saturate R) sd') : sd'.rules = sd.rules :=
  runReach_rules (cmdStep_saturate_iff.mp h).1

/-- A source command changes rule membership only when it registers a rule. -/
theorem CmdStep.mem_rules_iff {src post : Database} {c : Cmd} (h : CmdStep src c post)
    (r : Rule) : r ∈ post.rules ↔ r ∈ src.rules ∨ c = .rule r := by
  obtain ⟨mid, hm, hcl⟩ := h
  rw [hcl.envRules.2]
  cases c with
  | action a => rw [evalAction_rules hm]; simp
  | rule s =>
      obtain rfl := Option.some.inj hm
      simp [eq_comm, or_comm]
  | decl f dc =>
      obtain rfl := Option.some.inj hm
      simp
  | run R =>
      obtain rfl := Option.some.inj hm
      simp [RunRules, Database.sUnion_rules]
  | saturate R =>
      rw [runReach_rules (show SaturateReach R src mid from hm).1]
      simp

/-- A source prefix retains its initial rules and exactly the rules it registered. -/
theorem ProgramStep.mem_rules_iff {pre : Program} {src post : Database}
    (h : ProgramStep src pre post) (r : Rule) :
    r ∈ post.rules ↔ r ∈ src.rules ∨ Cmd.rule r ∈ pre := by
  induction h with
  | nil => simp
  | cons hc hp ih =>
      rw [ih, hc.mem_rules_iff]
      simp [List.mem_cons, eq_comm, or_assoc]

end Egglog
