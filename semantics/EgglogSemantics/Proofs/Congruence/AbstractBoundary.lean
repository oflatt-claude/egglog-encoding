import EgglogSemantics.Proofs.MatchMonotone
import EgglogSemantics.Proofs.Congruence.AbstractSoundRounds

/-! Data invariants at boundaries between original source commands. -/

namespace Egglog.Congruence.Abstract

/-- The data relation maintained between corresponding successful command prefixes. -/
structure Boundary (src d : Database) : Prop where
  sound : SoundTerms d src
  descend : Descending d
  reads : SourceReads d src
  saturated : RunSaturated rebuildRuleset d

/-- Rebuilding metadata and finiteness come from the actual compiled prefix. -/
theorem Boundary.rebuilt {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src d : Database}
    (hs : ProgramStep Database.empty pre src)
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) : Rebuilt d :=
  prefix_rebuilt_of_saturated hp hsub hs ht
    (h.sound.viewsSound (prefix_noUnions ht).diag) h.saturated
    (fun _ _ ho => h.descend.out (prefix_noUnions ht).diag ho)

theorem prelude_boundary {P : Program} {d : Database}
    (ht : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) :
    Boundary Database.empty d := by
  obtain ⟨_, hterms, _⟩ := prelude_empty ht
  refine ⟨?_, ?_, ?_, prelude_saturated ht _⟩
  · constructor <;> intros <;> simp_all
  · intro a b hm
    simp [hterms] at hm
  · constructor
    · intro t ht
      simp at ht
    · intro a b hab _
      cases hab

private theorem evalLocalActions_setRules (d : Database) (rules : Set Rule)
    (as : List Action) (σ : Env) :
    evalLocalActions {d with rules := rules} as σ =
      (evalLocalActions d as σ).map (fun post => {post with rules := rules}) := by
  unfold evalLocalActions
  rw [show ({d with rules := rules, env := σ ++ d.env} : Database) =
    {{d with env := σ ++ d.env} with rules := rules} from rfl, evalActions_setRules]
  simp only [Option.map_map, Function.comp_def]

/-- Registering a rule outside a saturated ruleset leaves that fixed point intact. -/
theorem runSaturated_addRule {d : Database} {R : RulesetName} (h : RunSaturated R d)
    {r : Rule} (hr : r.ruleset ≠ R) : RunSaturated R {d with rules := insert r d.rules} := by
  constructor
  · apply (runRules_eq_self_iff R _).mpr
    intro s hs hR post hpost
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact (hr hR).elim
    · obtain ⟨σ, hσ, hf⟩ := hpost
      have hσ' : ValidQuerySubst d s.query σ := by
        exact ValidQuerySubst.mono (d₁ := {d with rules := insert r d.rules})
          (d₂ := d) ⟨Set.Subset.refl _⟩ rfl rfl hσ
      rw [evalLocalActions_setRules] at hf
      obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hf
      exact ⟨((runRules_eq_self_iff R d).mp h.1 s hs hR out ⟨σ, hσ', hout⟩).eqs⟩
  · intro post hm
    obtain ⟨out, hout, heq⟩ := mergeClosure_setRules.mp (Relation.ReflTransGen.single hm)
    rw [hout.eq_of_mergeNormal h.2] at heq
    exact heq

end Egglog.Congruence.Abstract
