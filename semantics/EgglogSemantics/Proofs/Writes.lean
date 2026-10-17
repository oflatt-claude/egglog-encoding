import EgglogSemantics.Proofs.Query

/-!
# Writes and their sequential readings

`Spec/Step.lean` states rounds and merges with `Action.writes`. Many proofs instead run
actions one at a time (`evalActions`), read a round as a union of rule results
(`RuleResults`), or a merge as a body execution (`MergeValues`). This file proves each
reading equal to its definition.
-/

namespace Egglog

@[simp] theorem Database.addEqs_sig {db : Database} {ps : Set (Term × Term)} :
    (db.addEqs ps).sig = db.sig := rfl

@[simp] theorem Database.addEqs_env {db : Database} {ps : Set (Term × Term)} :
    (db.addEqs ps).env = db.env := rfl

@[simp] theorem Database.addEqs_rules {db : Database} {ps : Set (Term × Term)} :
    (db.addEqs ps).rules = db.rules := rfl

@[simp] theorem Database.addEqs_eqs {db : Database} {ps : Set (Term × Term)} :
    (db.addEqs ps).eqs = db.eqs ∪ ps := rfl

/-! ### Actions -/

/-- Running one action inserts the equation it writes. -/
theorem evalAction_eq_write (db : Database) (a : Action) :
    evalAction db a = (a.write db.sig db.env).map fun p => { db with eqs := insert p db.eqs } := by
  cases a with
  | expr e =>
    simp only [evalAction, Action.write, Option.map_map]
    rfl
  | union e₁ e₂ =>
    simp only [evalAction, Action.write]
    cases e₁.eval db.sig db.env <;> cases e₂.eval db.sig db.env <;>
      simp only [Option.bind_none, Option.bind_some, Option.map_none]
    split <;> rfl

/-- Running actions in order adds exactly the equations the head writes. -/
theorem evalActions_eq_writes (db : Database) (as : List Action) :
    evalActions db as = (Action.writes db.sig db.env as).map db.addEqs := by
  induction as generalizing db with
  | nil =>
    simp only [evalActions, Action.writes, Option.map_some, Option.some.injEq]
    cases db
    simp [Database.addEqs]
  | cons a as ih =>
    rw [evalActions, evalAction_eq_write]
    cases hw : a.write db.sig db.env with
    | none => simp [Action.writes, hw]
    | some p =>
      simp only [Option.map_some, Option.bind_some, Action.writes, hw, ih, Option.map_map]
      congr 1
      funext W
      simp only [Function.comp, Database.addEqs, Set.insert_union, Set.union_insert]

/-- A rule firing adds the equations its head writes under the substitution. -/
theorem evalLocalActions_eq_writes (db : Database) (as : List Action) (σ : Env) :
    evalLocalActions db as σ = (Action.writes db.sig σ as).map db.addEqs := by
  simp only [evalLocalActions, evalActions_eq_writes, Option.map_map]
  rfl

/-! ### Rounds -/

theorem mem_ruleResults_iff_writes {db d : Database} {r : Rule} :
    d ∈ RuleResults db r ↔ ∃ σ W, QueryMatches db r.query σ ∧
      Action.writes db.sig σ r.actions = some W ∧ d = db.addEqs W := by
  rw [mem_ruleResults_iff_queryMatches]
  simp only [evalLocalActions_eq_writes, Option.map_eq_some_iff]
  constructor
  · rintro ⟨σ, hq, W, hW, rfl⟩
    exact ⟨σ, W, hq, hW, rfl⟩
  · rintro ⟨σ, W, hq, hW, rfl⟩
    exact ⟨σ, hq, W, hW, rfl⟩

/-- A round is the union of its rule firings' results. -/
theorem RunRules.eq_sUnion (R : RulesetName) (db : Database) :
    RunRules R db = db.sUnion {d | ∃ r ∈ db.rules, r.ruleset = R ∧ d ∈ RuleResults db r} := by
  simp only [RunRules, Database.addEqs, Database.sUnion]
  congr 1
  ext p
  simp only [Set.mem_union, Set.mem_sUnion, Set.mem_iUnion, Set.mem_setOf_eq,
    mem_ruleResults_iff_writes, exists_prop]
  constructor
  · rintro (hp | ⟨W, ⟨r, hr, hR, σ, hq, hW⟩, hpW⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨db.addEqs W, ⟨r, hr, hR, σ, W, hq, hW, rfl⟩, Or.inr hpW⟩
  · rintro (hp | ⟨d, ⟨r, hr, hR, σ, W, hq, hW, rfl⟩, hp⟩)
    · exact Or.inl hp
    · rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr ⟨W, ⟨r, hr, hR, σ, hq, hW⟩, hp⟩

@[simp] theorem RunRules.sig {R : RulesetName} {db : Database} :
    (RunRules R db).sig = db.sig := rfl

@[simp] theorem RunRules.env {R : RulesetName} {db : Database} :
    (RunRules R db).env = db.env := rfl

@[simp] theorem RunRules.rules {R : RulesetName} {db : Database} :
    (RunRules R db).rules = db.rules := rfl

/-! ### Merging -/

theorem mergeValues_iff {db d : Database} {decl : FnDecl} {old new vs : List Term} :
    MergeValues db decl old new d vs ↔
      ∃ oldVars newVars body res W, decl.merge = some (.merge oldVars newVars body res) ∧
        Action.writes db.sig (mergeEnv oldVars newVars old new) body = some W ∧
        Expr.evalList db.sig res (mergeEnv oldVars newVars old new) = some vs ∧
        d = db.addEqs W := by
  constructor
  · rintro ⟨hm, he⟩
    simp only [evalMerge, evalActions_eq_writes, Option.map_eq_some_iff,
      Option.bind_eq_some_iff] at he
    obtain ⟨_, ⟨W, hW, rfl⟩, _, hres, hpair⟩ := he
    cases hpair
    exact ⟨_, _, _, _, W, hm, hW, hres, rfl⟩
  · rintro ⟨oldVars, newVars, body, res, W, hm, hW, hres, rfl⟩
    have he : evalMerge { db with env := mergeEnv oldVars newVars old new } body res =
        some ({ db with env := mergeEnv oldVars newVars old new }.addEqs W, vs) := by
      simp only [evalMerge, evalActions_eq_writes]
      simp only [hW, Option.map_some, Option.bind_some, Database.addEqs_sig,
        Database.addEqs_env, hres]
    exact MergeValues.eval hm he

/-- `MergeStep` in the shape of its sequential reading. -/
theorem mergeStep_iff {db db' : Database} :
    MergeStep db db' ↔ ∃ (old new : Entry) (decl : FnDecl) (d : Database) (vs : List Term),
      old ∈ db.entries ∧ new ∈ db.entries ∧ old ≠ new ∧ old.name = new.name ∧
      db.sig old.name = some decl ∧ CongList db old.key new.key ∧
      MergeValues ((db.eraseEntry old).eraseEntry new) decl old.value new.value d vs ∧
      db' = d.putEntry ⟨old.name, old.key, vs⟩ := by
  constructor
  · rintro ⟨⟨ho, hn, hne, hname, hk⟩, hm, hW, hres⟩
    obtain ⟨decl, hd, hdm⟩ := Option.bind_eq_some_iff.mp hm
    exact ⟨_, _, decl, _, _, ho, hn, hne, hname, hd, hk,
      mergeValues_iff.mpr ⟨_, _, _, _, _, hdm, by simpa using hW, by simpa using hres, rfl⟩, rfl⟩
  · rintro ⟨old, new, decl, d, vs, ho, hn, hne, hname, hd, hk, hv, rfl⟩
    obtain ⟨oldVars, newVars, body, res, W, hdm, hW, hres, rfl⟩ := mergeValues_iff.mp hv
    have hm : db.sig.mergeOf old.name = some (.merge oldVars newVars body res) := by
      simp [Signature.mergeOf, hd, hdm]
    exact MergeStep.collide ⟨ho, hn, hne, hname, hk⟩ hm (by simpa using hW)
      (by simpa using hres)

/-- The sequential form of a collision. -/
theorem MergeStep.collide' {db d : Database} {old new : Entry} {decl : FnDecl}
    {vs : List Term} (ho : old ∈ db.entries) (hn : new ∈ db.entries) (hne : old ≠ new)
    (hname : old.name = new.name) (hd : db.sig old.name = some decl)
    (hk : CongList db old.key new.key)
    (hv : MergeValues ((db.eraseEntry old).eraseEntry new) decl old.value new.value d vs) :
    MergeStep db (d.putEntry ⟨old.name, old.key, vs⟩) :=
  mergeStep_iff.mpr ⟨old, new, decl, d, vs, ho, hn, hne, hname, hd, hk, hv, rfl⟩

theorem MergeStep.sig {d₁ d₂ : Database} (h : MergeStep d₁ d₂) : d₂.sig = d₁.sig := by
  cases h; rfl

theorem MergeClosure.sig {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.sig = d₁.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [hstep.sig, ih]

/-- A merge changes only the store. -/
theorem MergeStep.envRules {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  cases h; exact ⟨rfl, rfl⟩

theorem MergeClosure.envRules {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.envRules.1.trans ih.1, hstep.envRules.2.trans ih.2⟩

/-! ### Normal states -/

theorem Database.conflicts_eq_empty_iff {db : Database} :
    db.conflicts = ∅ ↔ MergeNormal db := by
  constructor
  · intro h a ha b hb hname hk
    by_contra hne
    have hc : (a, b) ∈ db.conflicts := ⟨ha, hb, hne, hname, hk⟩
    rw [h] at hc
    exact hc
  · intro h
    ext ⟨a, b⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨ha, hb, hne, hname, hk⟩
    exact hne (h a ha b hb hname hk)

theorem MergeNormalize.normal {db db' : Database} (h : MergeNormalize db db') :
    MergeNormal db' :=
  Database.conflicts_eq_empty_iff.mp h.2

theorem MergeNormalize.of_normal {db db' : Database} (hc : MergeClosure db db')
    (hn : MergeNormal db') : MergeNormalize db db' :=
  ⟨hc, Database.conflicts_eq_empty_iff.mpr hn⟩

/-! ### Rounds and saturation -/

theorem RunStep.normal {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    MergeNormal db' :=
  Database.conflicts_eq_empty_iff.mp h.2

theorem RunStep.of_normal {R : RulesetName} {db db' : Database}
    (hc : MergeClosure (RunRules R db) db') (hn : MergeNormal db') : RunStep R db db' :=
  ⟨hc, Database.conflicts_eq_empty_iff.mpr hn⟩

theorem RunStep.sig {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.sig = db.sig :=
  (MergeClosure.sig h.1).trans RunRules.sig

theorem RunStep.envRules {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.env = db.env ∧ db'.rules = db.rules :=
  MergeClosure.envRules (d₁ := RunRules R db) h.1

/-- Within a round, meaning is congruence: the signature, environment and rules stay. -/
theorem RunStep.sameMeaning_iff {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db.SameMeaning db' ↔ Cong db = Cong db' := by
  constructor
  · intro hm
    funext a b
    exact propext (hm.congr a b)
  · intro hc
    exact ⟨h.sig.symm, h.envRules.1.symm, h.envRules.2.symm, fun a b => by rw [hc]⟩

/-- A round that preserves meaning ends saturation. -/
theorem SaturateReach.done {R : RulesetName} {db d : Database} (hs : RunStep R db d)
    (hm : db.SameMeaning d) : SaturateReach R db d :=
  .fixpoint hs (hs.sameMeaning_iff.mp hm)

/-- A round that changes meaning continues saturation. -/
theorem SaturateReach.step {R : RulesetName} {db mid d : Database} (hs : RunStep R db mid)
    (hne : ¬ db.SameMeaning mid) (ht : SaturateReach R mid d) : SaturateReach R db d :=
  .again hs (fun hc => hne (hs.sameMeaning_iff.mpr hc)) ht

/-- Induction over the rounds of a saturation, reading each round's test as `SameMeaning`. -/
@[elab_as_elim]
theorem SaturateReach.induction {R : RulesetName}
    {motive : (db d : Database) → SaturateReach R db d → Prop}
    (done : ∀ {db d : Database} (hs : RunStep R db d) (hm : db.SameMeaning d),
      motive db d (.done hs hm))
    (step : ∀ {db mid d : Database} (hs : RunStep R db mid) (hne : ¬ db.SameMeaning mid)
      (ht : SaturateReach R mid d), motive mid d ht → motive db d (.step hs hne ht))
    {db d : Database} (h : SaturateReach R db d) : motive db d h := by
  induction h with
  | fixpoint hs hc => exact done hs (hs.sameMeaning_iff.mpr hc)
  | again hs hne ht ih => exact step hs (fun hm => hne (hs.sameMeaning_iff.mp hm)) ht ih

theorem SaturateReach.cases_iff {R : RulesetName} {db d : Database} :
    SaturateReach R db d ↔ (RunStep R db d ∧ db.SameMeaning d) ∨
      ∃ mid, RunStep R db mid ∧ ¬ db.SameMeaning mid ∧ SaturateReach R mid d := by
  constructor
  · intro h
    induction h using SaturateReach.induction with
    | done hs hm => exact Or.inl ⟨hs, hm⟩
    | step hs hne ht _ => exact Or.inr ⟨_, hs, hne, ht⟩
  · rintro (⟨hs, hm⟩ | ⟨mid, hs, hne, ht⟩)
    · exact .done hs hm
    · exact .step hs hne ht

end Egglog
