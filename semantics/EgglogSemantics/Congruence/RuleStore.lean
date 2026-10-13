import EgglogSemantics.Congruence.Tables
import EgglogSemantics.Encoding.SourceExecution

/-! Exact rule-store correspondence and rebuilding copies within source saturation rulesets. -/

namespace Egglog.Congruence

/-- Only source rule commands emit compiled source rules. -/
theorem rule_mem_encodeCmd (i : Nat) (c : Cmd) (r : Rule) :
    Cmd.rule r ∈ (encodeCmd i c).map Command.command ↔
      ∃ s, c = .rule s ∧ r = encodeRule s := by
  cases c <;> simp [encodeCmd, taggedRule, Function.comp_def, eq_comm]

/-- The compiler's command counter does not change which rules a prefix registers. -/
theorem rule_mem_encodeCmds (pre : Program) (i : Nat) (r : Rule) :
    Cmd.rule r ∈ (encodeCmds pre i).map Command.command ↔
      ∃ s, Cmd.rule s ∈ pre ∧ r = encodeRule s := by
  induction pre generalizing i with
  | nil => simp [encodeCmds]
  | cons c cs ih =>
      rw [encodeCmds, List.map_append, List.mem_append, rule_mem_encodeCmd, ih]
      constructor
      · rintro (⟨s, hs, hr⟩ | ⟨s, hs, hr⟩)
        · exact ⟨s, List.mem_cons.mpr (Or.inl hs.symm), hr⟩
        · exact ⟨s, List.mem_cons_of_mem _ hs, hr⟩
      · rintro ⟨s, hs, hr⟩
        rcases List.mem_cons.mp hs with hs | hs
        · exact Or.inl ⟨s, hs.symm, hr⟩
        · exact Or.inr ⟨s, hs, hr⟩

/-- Every rule in the prelude is tagged maintenance. -/
theorem rule_mem_prelude (P : Program) (r : Rule) :
    Cmd.rule r ∈ (encodePrelude P).map Command.command ↔
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
  simp only [encodePrelude, List.map_append, List.map_cons, List.mem_append,
    List.mem_cons, List.mem_map]
  constructor
  · rintro ((h | ⟨c, hc, hr⟩) | h)
    · cases h
    · obtain ⟨⟨f, k⟩, _, hc⟩ := List.mem_flatMap.mp hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> cases hr
    · exact h
  · exact Or.inr

/-- Rule-store correspondence at an aligned source and target state. -/
def RulesEncoded (P : Program) (src : Database) (d : FDatabase) : Prop :=
  ∀ r, r ∈ d.rules ↔ (∃ c ∈ allMaintenanceRules P, c.command = .rule r) ∨
    ∃ s ∈ src.rules, r = encodeRule s

/-- Actual execution of the prelude and compiled prefix establishes rule-store correspondence. -/
theorem rulesEncoded_of_prefix {P pre : Program} {src : Database} {d e : FDatabase}
    (hsrc : ProgramStep Database.empty pre src)
    (hpre : FDatabase.empty.execProgramM ((encodePrelude P).map Command.command) = some d)
    {i : Nat} (run : d.execProgramM ((encodeCmds pre i).map Command.command) = some e) :
    RulesEncoded P src e := by
  intro r
  rw [Egglog.FDatabase.execProgramM_mem_rules_iff run,
    Egglog.FDatabase.execProgramM_mem_rules_iff hpre, rule_mem_prelude, rule_mem_encodeCmds]
  have hmem : ∀ s, s ∈ src.rules ↔ Cmd.rule s ∈ pre := by
    intro s
    simpa [Database.empty] using hsrc.mem_rules_iff s
  simp only [FDatabase.empty, List.not_mem_nil, false_or, hmem]

/-- Every rule selected by a dedicated rebuilding phase comes from maintenance. -/
theorem RulesEncoded.rebuild_only {P pre : Program} {src : Database} {d : FDatabase}
    (h : RulesEncoded P src d) (hdom : P.EncodeDomain)
    (hpre : ProgramStep Database.empty pre src) (hsub : ∀ c ∈ pre, c ∈ P) :
    ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
  intro r hr hR
  rcases (h r).mp hr with hm | ⟨s, hs, rfl⟩
  · exact hm
  · have hmem : Cmd.rule s ∈ pre := by simpa [Database.empty] using (hpre.mem_rules_iff s).mp hs
    exact (ruleset_ne_rebuild hdom (hsub _ hmem) hR).elim

/-- Any generated maintenance rule has an identical copy in each source saturation ruleset. -/
theorem maintenance_copy {P : Program} {c : Command} (hc : c ∈ allMaintenanceRules P)
    {r : Rule} (hr : c.command = .rule r) {R : RulesetName} (hR : R ∈ P.saturateRulesets) :
    ∃ c' ∈ allMaintenanceRules P, c'.command = .rule { r with ruleset := R } := by
  have hbase : ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r →
      ∃ c' ∈ allMaintenanceRules P, c'.command = .rule { r with ruleset := R } := by
    intro c hc r hr
    refine ⟨inRuleset R c, List.mem_append_right _ ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨R, hR, List.mem_map.mpr ⟨c, hc, rfl⟩⟩
    · simp [inRuleset, hr]
  rcases List.mem_append.mp hc with hc | hc
  · exact hbase c hc r hr
  · obtain ⟨S, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hcbase, rfl⟩ := List.mem_map.mp hc
    unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl := Cmd.rule.inj hr
      exact hbase c hcbase s hs
    next hn => exact hbase c hcbase r hr

/-- Being closed under a saturation ruleset also closes the dedicated rebuilding rules,
because the prelude registered copies with the same queries and heads. -/
theorem RulesEncoded.rebuild_closed {P pre : Program} {src : Database} {d : FDatabase}
    (h : RulesEncoded P src d) (hdom : P.EncodeDomain)
    (hpre : ProgramStep Database.empty pre src) (hsub : ∀ c ∈ pre, c ∈ P)
    {R : RulesetName} (hR : R ∈ P.saturateRulesets) (hclosed : d.RoundClosed R) :
    d.RoundClosed rebuildRuleset := by
  intro t ht
  rcases mem_terms_execRunRules.mp ht with ht |
      ⟨r, hr, hrr, σ, hσ, e, hf, ht⟩
  · exact ht
  · obtain ⟨c, hc, hcr⟩ := h.rebuild_only hdom hpre hsub r hr hrr
    obtain ⟨c', hc', hcr'⟩ := maintenance_copy hc hcr hR
    have hmem : { r with ruleset := R } ∈ d.rules := (h _).mpr (Or.inl ⟨c', hc', hcr'⟩)
    exact hclosed.fired hmem rfl hσ hf ht

private theorem maintenanceRules_query_ne_nil (P : Program) :
    ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r → r.query ≠ [] := by
  intro c hc r hr
  rcases List.mem_cons.mp hc with rfl | hc
  · obtain rfl := Cmd.rule.inj hr
    simp [pathCompressRule]
  · obtain ⟨⟨f, k⟩, _, hc⟩ := List.mem_flatMap.mp hc
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain rfl := Cmd.rule.inj hr
      simp [eclassRule]
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      obtain rfl := Cmd.rule.inj hr
      simp [childRule]

/-- Every maintenance query has live-row premises, so none can fire from empty data. -/
theorem maintenance_query_ne_nil {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) : r.query ≠ [] := by
  rcases List.mem_append.mp hc with hc | hc
  · exact maintenanceRules_query_ne_nil P c hc r hr
  · obtain ⟨R, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hcbase, rfl⟩ := List.mem_map.mp hc
    unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl := Cmd.rule.inj hr
      exact maintenanceRules_query_ne_nil P c hcbase s hs
    next => exact maintenanceRules_query_ne_nil P c hcbase r hr

end Egglog.Congruence
