import EgglogSemantics.Proofs.Merge
import EgglogSemantics.Proofs.RuleStore

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
  | check q => rw [FDatabase.execCheck_eq h]; simp

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
/-- Action evaluation does not inspect the registered rules. -/
theorem execAction_setRules (d : FDatabase) (rs : List Rule) (a : Action) :
    execAction { d with rules := rs } a = (execAction d a).map (fun e => { e with rules := rs }) := by
  cases a with
  | expr e =>
      simp only [execAction]
      cases e.evalAtom d.sig d.env <;> rfl
  | union e f =>
      simp only [execAction]
      cases e.eval d.sig d.env <;> cases f.eval d.sig d.env <;> simp
      split <;> rfl

theorem execActions_setRules (d : FDatabase) (rs : List Rule) (as : List Action) :
    execActions { d with rules := rs } as =
      (execActions d as).map (fun e => { e with rules := rs }) := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih =>
      simp only [execActions, execAction_setRules]
      cases execAction d a with
      | none => rfl
      | some e => simpa only [Option.map_some, Option.bind_some] using ih e

theorem mergeOneOriented_setRules (cl : Finset (Term × Term)) (d : FDatabase)
    (rs : List Rule) (r₁ r₂ : Row) :
    mergeOneOriented cl { d with rules := rs } r₁ r₂ =
      (mergeOneOriented cl d r₁ r₂).map (fun e => { e with rules := rs }) := by
  simp only [mergeOneOriented]
  cases hm : d.sig.mergeOf r₁.fn with
  | none => rfl
  | some ms =>
      cases ms with
      | merge oldVars newVars body res =>
          dsimp only
          split
          · split
            · rfl
            · rw [execActions_setRules { d with env := mergeEnv oldVars newVars r₂.out r₁.out } rs body]
              cases execActions { d with env := mergeEnv oldVars newVars r₂.out r₁.out } body with
              | none => rfl
              | some e =>
                  simp only [Option.map_some, Option.bind_some]
                  cases Expr.evalList e.sig res e.env <;> rfl
          · rfl

theorem mergeOneWith_setRules (cl : Finset (Term × Term)) (d : FDatabase)
    (rs : List Rule) (r₁ r₂ : Row) :
    mergeOneWith cl { d with rules := rs } r₁ r₂ =
      (mergeOneWith cl d r₁ r₂).map (fun e => { e with rules := rs }) := by
  simp only [mergeOneWith, show swapForCanon cl { d with rules := rs } r₁ r₂ =
    swapForCanon cl d r₁ r₂ from rfl]
  split <;> exact mergeOneOriented_setRules cl d rs _ _


/-- Replacing registered rules commutes with a fold whose steps do not inspect them. -/
theorem foldl_setRules {α : Type} (f : FDatabase → α → FDatabase)
    (rs : List Rule)
    (hf : ∀ d a, f { d with rules := rs } a = { f d a with rules := rs })
    (xs : List α) (d : FDatabase) :
    xs.foldl f { d with rules := rs } = { xs.foldl f d with rules := rs } := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, hf] using ih (f d x)

theorem mergeRound_setRules (d : FDatabase) (rs : List Rule) :
    mergeRound { d with rules := rs } = { d.mergeRound with rules := rs } := by
  have hc : ({ d with rules := rs } : FDatabase).closureF = d.closureF := rfl
  have hb : rebuild d.closureF { d with rules := rs } =
      { rebuild d.closureF d with rules := rs } := rfl
  simp only [mergeRound, show ({ d with rules := rs } : FDatabase).hasMergeRow =
    d.hasMergeRow from rfl, hc]
  split
  · rfl
  · rw [hb]
    apply foldl_setRules
    intro acc r₁
    apply foldl_setRules
    intro acc' r₂
    split
    · rfl
    · rw [mergeOneWith_setRules]
      cases mergeOneWith d.closureF acc' r₁ r₂ <;> rfl

theorem settled_setRules (d : FDatabase) (rs : List Rule) :
    ({ d with rules := rs } : FDatabase).settled = d.settled := by
  simp only [settled, mergeRound_setRules, sameData]


theorem addTerms_setRules (d : FDatabase) (rs : List Rule) (ts : List Term) :
    ({ d with rules := rs } : FDatabase).addTerms ts = { d.addTerms ts with rules := rs } :=
  foldl_setRules (fun e t => e.addTerm t) rs (fun _ _ => rfl) ts d

theorem patternHolds_setRules (d : FDatabase) (rs : List Rule) (p : Pattern) (σ : Env) :
    patternHolds { d with rules := rs } p σ = patternHolds d p σ := by
  cases p with
  | expr e =>
      simp only [patternHolds]
      cases e.entry d.sig with
      | none => rfl
      | some ent =>
          obtain ⟨f, keys, vals⟩ := ent
          dsimp only
          cases Expr.evalList d.sig vals σ <;> cases Expr.evalList d.sig keys σ
          all_goals first | rfl | simp only [addTerms_setRules, closureF, eqsF, termsF]
  | eq a b => rfl

theorem matchQuery_setRules (d : FDatabase) (rs : List Rule) (q : Query) :
    matchQuery { d with rules := rs } q = matchQuery d q := by
  simp only [matchQuery,
    show ({ d with rules := rs } : FDatabase).valueTerms = d.valueTerms from rfl,
    patternHolds_setRules]

theorem execLocalActions_setRules (d : FDatabase) (rs : List Rule) (as : List Action) (σ : Env) :
    execLocalActions { d with rules := rs } as σ =
      (execLocalActions d as σ).map (fun e => { e with rules := rs }) := by
  simp only [execLocalActions]
  rw [execActions_setRules { d with env := σ ++ d.env } rs as]
  cases execActions { d with env := σ ++ d.env } as <;> rfl

/-- Adding rules outside a ruleset preserves that ruleset's closure. -/
theorem RoundClosed.setRules {d : FDatabase} {R : RulesetName} (h : d.RoundClosed R)
    (rs : List Rule) (hrules : ∀ r ∈ rs, r.ruleset = R → r ∈ d.rules) :
    ({ d with rules := rs } : FDatabase).RoundClosed R := by
  intro t ht
  rcases mem_terms_execRunRules.mp ht with ht | ⟨r, hr, hR, σ, hm, e, hf, ht⟩
  · exact ht
  · rw [matchQuery_setRules] at hm
    change execLocalActions { d with rules := rs } r.actions σ = some e at hf
    rw [execLocalActions_setRules] at hf
    obtain ⟨e', he', heq⟩ := Option.map_eq_some_iff.mp hf
    exact h.fired (hrules r hr hR) hR hm he' (by simpa only [← heq] using ht)

end Egglog.FDatabase
