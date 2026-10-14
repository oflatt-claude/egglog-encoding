import EgglogSemantics.Proofs.Congruence.Read

/-! Structural properties of the congruence compiler, independent of provenance. -/

namespace Egglog.Congruence

private theorem actions_unionFree_append {as bs : List Action}
    (ha : Actions.UnionFree as) (hb : Actions.UnionFree bs) :
    Actions.UnionFree (as ++ bs) := by
  induction as with
  | nil => exact hb
  | cons a as ih => exact ⟨ha.1, ih ha.2⟩

mutual

/-- Compiled constructions write entries and never assert a built-in union. -/
theorem encodeBuild_unionFree : ∀ e : Expr, Actions.UnionFree (encodeBuild e)
  | .lit _ | .var _ => trivial
  | .min a b => actions_unionFree_append (encodeBuild_unionFree a) (encodeBuild_unionFree b)
  | .app _ es => actions_unionFree_append (encodeBuildArgs_unionFree es) ⟨trivial, trivial⟩

theorem encodeBuildArgs_unionFree : ∀ es : List Expr, Actions.UnionFree (encodeBuildArgs es)
  | [] => trivial
  | e :: es => actions_unionFree_append (encodeBuild_unionFree e) (encodeBuildArgs_unionFree es)

end

/-- This includes compilation of a source union. -/
theorem encodeAction_unionFree (a : Action) : Actions.UnionFree (encodeAction a) := by
  cases a with
  | expr e => exact encodeBuild_unionFree e
  | union a b =>
    exact actions_unionFree_append
      (actions_unionFree_append (encodeBuild_unionFree a) (encodeBuild_unionFree b))
      ⟨trivial, trivial, trivial⟩

theorem encodeActions_unionFree (as : List Action) : Actions.UnionFree (encodeActions as) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact actions_unionFree_append (encodeAction_unionFree a) ih

private theorem mem_actions_unionFree {as : List Action} (h : Actions.UnionFree as) :
    ∀ a ∈ as, a.UnionFree := by
  induction as with
  | nil => simp
  | cons a as ih =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h.1
      · exact ih h.2 b hb

private theorem maintenance_unionFree (P : Program) :
    ∀ c ∈ maintenanceRules P, c.command.UnionFree := by
  intro c hc
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · exact ⟨trivial, trivial⟩
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩ <;> exact ⟨trivial, trivial⟩

private theorem inRuleset_unionFree (R : RulesetName) (c : Command)
    (hc : c.command.UnionFree) : (inRuleset R c).command.UnionFree := by
  unfold inRuleset
  split <;> simp_all only [Cmd.UnionFree, Rule.UnionFree]

private theorem allMaintenance_unionFree (P : Program) :
    ∀ c ∈ allMaintenanceRules P, c.command.UnionFree := by
  intro c hc
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenance_unionFree P c hc
  · exact inRuleset_unionFree R c (maintenance_unionFree P c hc)

private theorem tableDecl_unionFree (arity : Nat) : (tableDecl arity).UnionFree := by
  simp [FnDecl.UnionFree, tableDecl, mergeBody, Action.UnionFree]

private theorem prelude_unionFree (P : Program) :
    ∀ c ∈ encodePrelude P, c.command.UnionFree := by
  intro c hc
  simp only [encodePrelude, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | ⟨⟨f, k⟩, _, hc⟩) | hc
  · exact tableDecl_unionFree 1
  · rcases hc with rfl | rfl
    · simp [Cmd.UnionFree, FnDecl.UnionFree, ctorDecl]
    · exact tableDecl_unionFree k
  · exact allMaintenance_unionFree P c hc

private theorem cmd_unionFree (i : Nat) (c : Cmd) :
    ∀ d ∈ encodeCmd i c, d.command.UnionFree := by
  intro d hd
  cases c with
  | decl f decl => simp [encodeCmd] at hd
  | rule r =>
      simp only [encodeCmd, List.mem_singleton] at hd
      subst d
      exact encodeActions_unionFree r.actions
  | action a =>
      simp only [encodeCmd, List.mem_append, List.mem_map, List.mem_singleton] at hd
      rcases hd with ⟨a', ha, rfl⟩ | rfl
      · exact mem_actions_unionFree (encodeAction_unionFree a) a' ha
      · trivial
  | run R | saturate R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> trivial

private theorem cmds_unionFree (P : Program) (i : Nat) :
    ∀ c ∈ encodeCmds P i, c.command.UnionFree := by
  induction P generalizing i with
  | nil => simp [encodeCmds]
  | cons c cs ih =>
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact cmd_unionFree i c d hd
      · exact ih (i + 1) d hd

/-- No source union survives in a command, rule head, or merge body. -/
theorem encode_unionFree (P : Program) : Program.UnionFree (encode P) := by
  have hall : ∀ c ∈ encode P, c.UnionFree := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_append.mp hd with hd | hd
    · exact prelude_unionFree P d hd
    · exact cmds_unionFree P 0 d hd
  generalize encode P = q at *
  induction q with
  | nil => trivial
  | cons c cs ih => exact ⟨hall c (by simp), ih fun d hd => hall d (by simp [hd])⟩

/-- The target's built-in equality remains diagonal; equality is represented by tables. -/
theorem execM_encode_eqsRefl {P : Program} {tgt : FDatabase}
    (h : execM (encode P) = some tgt) : tgt.EqsRefl := by
  intro p hp
  rw [(execM_noUnions (encode_unionFree P) h).eqs] at hp
  simp at hp

/-- Every self-collision is ignored using the single id output, without proof-specific
identity-column configuration. -/
theorem tableDecl_no_self_conflict (arity : Nat) (values : List Term) :
    ¬ MergeConflict (tableDecl arity) mergeBody values values := by
  simp [MergeConflict, FnDecl.unchangedWidth, tableDecl, mergeBody]

end Egglog.Congruence
