import EgglogSemantics.Proofs.Step

/-! Exact rule stores in mathematical command executions. -/

namespace Egglog

/-- A round leaves the **ruleset** alone too: `RunRules` is a `sUnion`, which takes `rules` from
the pre-state, and so is every merge step. This is what carries `UnionsInv.rules` across a
firing command, where the source's rules are the ones the target already holds encodings of. -/
theorem runStep_rules {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.rules = db.rules := (MergeClosure.envRules h.1).2

@[inherit_doc runStep_rules]
theorem runReach_rules {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : d.rules = db.rules := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [runStep_rules hstep, ih]

theorem cmdStep_rules_of_run {sd sd' : Database} {R : RulesetName}
    (h : CmdStep sd (.run R) sd') : sd'.rules = sd.rules := by
  obtain ⟨d, hreach, hcl⟩ := h.reach
  rw [(MergeClosure.envRules hcl).2, show d = RunRules R sd from hreach]
  rfl

theorem cmdStep_rules_of_saturate {sd sd' : Database} {R : RulesetName}
    (h : CmdStep sd (.saturate R) sd') : sd'.rules = sd.rules :=
  runReach_rules (cmdStep_saturate_iff.mp h).reach

/-- A source command changes rule membership only when it registers a rule. -/
theorem CmdStep.mem_rules_iff {src post : Database} {c : Cmd} (h : CmdStep src c post)
    (r : Rule) : r ∈ post.rules ↔ r ∈ src.rules ∨ c = .rule r := by
  obtain ⟨mid, hm, hcl⟩ := h.reach
  rw [hcl.envRules.2]
  cases c with
  | rule s =>
      subst hm
      simp [eq_comm, or_comm]
  | decl f dc =>
      subst hm
      simp
  | run R =>
      subst hm
      simp [RunRules, Database.sUnion_rules]
  | saturate R =>
      rw [runReach_rules (show SaturateReach R src mid from hm).reach]
      simp
  | check q => rw [(show QueryHolds src q ∧ mid = src from hm).2]; simp

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
