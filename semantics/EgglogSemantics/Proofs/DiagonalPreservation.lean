import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.Step

/-! Union-free mathematical executions preserve diagonal congruence. -/

namespace Egglog

/-- Value construction and function writes add only reflexive equations. -/
theorem evalAction_diag {db db' : Database} {a : Action} (hu : a.UnionFree)
    (hd : db.Diag) (h : evalAction db a = some db') : db'.Diag := by
  rcases evalAction_eq_some h with ⟨_, t, _, _, rfl⟩ | ⟨_, _, _, _, rfl, _⟩
  · exact hd.addTerm t
  · exact absurd hu id

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

theorem MergeValues.diag {d e : Database} {decl : FnDecl} {old new vs : List Term}
    (hu : decl.UnionFree) (hd : d.Diag) (h : MergeValues d decl old new e vs) :
    e.Diag := by
  cases h with
  | @eval e vs oldVars newVars body res hmerge hblock =>
    obtain ⟨hbody, _⟩ := evalMerge_eq_some.mp hblock
    exact evalActions_diag (db := { d with env := mergeEnv oldVars newVars old new })
      (db' := e) (hu _ hmerge) hd hbody

/-- Merging removes reflexive row assertions and adds only reflexive assertions. -/
theorem MergeStep.diag {d₁ d₂ : Database} (hs : Signature.UnionFree d₁.sig)
    (hd : d₁.Diag) (h : MergeStep d₁ d₂) : d₂.Diag := by
  cases h with
  | collide _ _ _ _ hdecl _ hbody =>
    exact (hbody.diag (hs _ _ hdecl) ((hd.eraseEntry _).eraseEntry _)).putEntry _

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
  ⟨MergeClosure.diag (by rw [RunRules.sig]; exact hn.sig) (RunRules.diag hn) h.1,
    by rw [MergeClosure.sig h.1, RunRules.sig]; exact hn.sig,
    by rw [(MergeClosure.envRules h.1).2]
       simpa only [RunRules, Database.sUnion_rules] using hn.rules⟩

/-- **One command preserves union-freedom, all three clauses.** `.decl` is the only case
that moves `sig` and `.rule` the only one that moves `rules`, which is why `Cmd.UnionFree`
constrains exactly those two; the merge phase every command
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
        (show SaturateReach R A e from hreach).reach hn
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
