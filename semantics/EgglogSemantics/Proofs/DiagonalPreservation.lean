import EgglogSemantics.Proofs.Diagonal

/-! Union-free mathematical executions preserve diagonal congruence. -/

namespace Egglog

/-- Every action but `union` writes through `addTerm`. -/
theorem evalAction_diag {db db' : Database} {a : Action} (hu : a.UnionFree)
    (hd : db.Diag) (h : evalAction db a = some db') : db'.Diag := by
  cases a with
  | expr e =>
    rw [evalAction, Option.map_eq_some_iff] at h
    obtain ⟨t, -, rfl⟩ := h
    exact hd.addTerm t
  | union e₁ e₂ => exact absurd hu id

theorem evalActions_diag {db db' : Database} {as : List Action} (hu : Actions.UnionFree as)
    (hd : db.Diag) (h : evalActions db as = some db') : db'.Diag := by
  induction as generalizing db with
  | nil => rw [evalActions_nil, Option.some.injEq] at h; exact h ▸ hd
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      rw [evalActions_cons, hv, Option.bind_some] at h
      exact ih hu.2 (evalAction_diag hu.1 hd hv) h

theorem evalLocalActions_diag {db db' : Database} {as : List Action} {σ : Env}
    (hu : Actions.UnionFree as) (hd : db.Diag) (h : evalLocalActions db as σ = some db') :
    db'.Diag := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  exact evalActions_diag (db := { db with env := σ ++ db.env }) (db' := d) hu hd hv

/-- A merge phase runs the body the *signature* names, so this is where
`Signature.UnionFree` is spent. -/
theorem MergeStep.diag {d₁ d₂ : Database} (hs : Signature.UnionFree d₁.sig)
    (hd : d₁.Diag) (h : MergeStep d₁ d₂) : d₂.Diag := by
  cases h with
  | @collide d f dc as bs a b vs oldVars newVars body res hdc hmg _ _ _ _ _ _ hbody _ =>
    exact (evalActions_diag (db := { d₁ with env := mergeEnv oldVars newVars a b })
      (hs f dc hdc _ hmg) hd hbody).addTerm _

theorem MergeClosure.diag {d₁ d₂ : Database} (hs : Signature.UnionFree d₁.sig)
    (hd : d₁.Diag) (h : MergeClosure d₁ d₂) : d₂.Diag := by
  induction h with
  | refl => exact hd
  | @tail b c hcl hstep ih =>
    exact hstep.diag (by rw [MergeClosure.sig hcl]; exact hs) ih

/-- A round's rule phase runs every rule the state carries, so this is where the `rules`
clause is spent. -/
theorem RunRules.diag {R : RulesetName} {db : Database} (hn : db.NoUnions) :
    (RunRules R db).Diag := by
  rintro p (hp | hp)
  · exact hn.diag p hp
  · obtain ⟨d, ⟨r, hr, -, σ, -, hσ⟩, hp'⟩ := Set.mem_iUnion₂.mp hp
    exact evalLocalActions_diag (hn.rules r hr) hn.diag hσ p hp'

/-- **A round preserves union-freedom.** Its rule phase is the `.run` case of
`CmdStep.noUnions` and its merge phase is `MergeClosure.diag`, so a saturating run only has
to iterate it. -/
theorem RunStep.noUnions {R : RulesetName} {A B : Database} (h : RunStep R A B)
    (hn : A.NoUnions) : B.NoUnions :=
  ⟨MergeClosure.diag (by rw [RunRules.sig]; exact hn.sig) (RunRules.diag hn) h,
    by rw [MergeClosure.sig h, RunRules.sig]; exact hn.sig,
    by rw [(MergeClosure.envRules h).2]
       simpa only [RunRules, Database.sUnion_rules] using hn.rules⟩

/-- **One command preserves union-freedom, all three clauses.** `.decl` is the only case
that moves `sig` and `.rule` the only one that moves `rules`, which is why `Cmd.UnionFree`
constrains exactly those two alongside a top-level action; the merge phase every command
ends with moves neither, and `MergeClosure.diag` is what keeps the state diagonal across
it. -/
theorem CmdStep.noUnions {A B : Database} (hn : A.NoUnions) {c : Cmd} (hu : c.UnionFree)
    (h : CmdStep A c B) : B.NoUnions := by
  obtain ⟨e, hreach, hcl⟩ := h.reach
  have hE : e.NoUnions := by
    cases c with
    | saturate R =>
      exact RunReach.induction (P := Database.NoUnions)
        (fun _ _ hp hs => RunStep.noUnions hs hp)
        (show SaturateReach R A e from hreach).1 hn
    | action a =>
      replace heff : evalAction A a = some e := hreach
      exact ⟨evalAction_diag hu hn.diag heff, by rw [evalAction_sig heff]; exact hn.sig,
        by rw [evalAction_rules heff]; exact hn.rules⟩
    | rule r =>
      subst hreach
      refine ⟨hn.diag, hn.sig, fun r' hr' => ?_⟩
      rcases hr' with rfl | hr'
      exacts [hu, hn.rules r' hr']
    | run R =>
      subst hreach
      exact ⟨RunRules.diag hn, hn.sig, hn.rules⟩
    | decl f dc =>
      subst hreach
      refine ⟨hn.diag, fun g dc' hg => ?_, hn.rules⟩
      have hg' : Function.update A.sig f (some dc) g = some dc' := hg
      by_cases hgf : g = f
      · rw [hgf, Function.update_self, Option.some.injEq] at hg'
        exact hg' ▸ hu
      · rw [Function.update_of_ne hgf] at hg'
        exact hn.sig g dc' hg'
    | check q => rw [hreach.2]; exact hn
  exact ⟨MergeClosure.diag hE.sig hE.diag hcl,
    by rw [MergeClosure.sig hcl]; exact hE.sig,
    by rw [(MergeClosure.envRules hcl).2]; exact hE.rules⟩


theorem Database.NoUnions.empty : Database.empty.NoUnions := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Database.Diag, Database.empty]
  · simp [Signature.UnionFree, Database.empty]
  · simp [Database.empty]

/-- No finite mathematical execution of union-free syntax asserts a nontrivial union. -/
theorem ProgramStep.noUnions {d e : Database} {p : Program} (h : ProgramStep d p e)
    (hn : d.NoUnions) (hu : p.UnionFree) : e.NoUnions := by
  induction h with
  | nil => exact hn
  | cons hc _ ih => exact ih (hc.noUnions hn hu.1) hu.2

end Egglog
