import EgglogSemantics.Proofs.SourceProof.Soundness

/-! An accepted rule certificate is sound in an explicitly reached source fixed point. -/

namespace Egglog.Tests.SourceProofCorrectness

open SourceProof

private def ctor : FnDecl := ⟨0, 1, none, none⟩
def premise : Term := .app "A" []
def conclusion : Term := .app "B" []
def derive : Rule :=
  ⟨[.expr (.app "A" [])], [.expr (.app "B" [])], "R"⟩
def program : Program :=
  [.decl "A" ctor, .decl "B" ctor, .action (.expr (.app "A" [])), .rule derive, .run "R"]
def certificate : Proof :=
  .rule ⟨conclusion, conclusion⟩ 3 [] [.fiat ⟨premise, premise⟩]

private def declaredA : Database :=
  { Database.empty with sig := Function.update Database.empty.sig "A" (some ctor) }
private def declared : Database :=
  { declaredA with sig := Function.update declaredA.sig "B" (some ctor) }
private def built : Database := declared.addTerm premise
private def registered : Database := { built with rules := insert derive ∅ }
def reached : Database := RunRules "R" registered

private theorem constructors : declared.sig.AllConstructors := by
  intro f
  by_cases hb : f = "B"
  · subst f; rfl
  · by_cases ha : f = "A"
    · subst f; rfl
    · simp [declared, declaredA, Database.empty, Signature.mergeOf, hb, ha]

private theorem normal {d : Database} (hc : d.sig.AllConstructors) : MergeNormal d := by
  intro row hr
  obtain ⟨dc, hd, hm, _⟩ := hr.1
  exact (hm (by simpa [Signature.mergeOf, hd] using hc row.name)).elim

private theorem empty_normal {d : Database} (he : d.eqs = ∅) : MergeNormal d := by
  intro row hr
  exact (he ▸ hr.2).elim

theorem source_reached : ProgramStep Database.empty program reached := by
  exact .cons (.of_reach rfl (empty_normal rfl))
    (.cons (.of_reach rfl (empty_normal rfl))
      (.cons (.of_reach rfl (normal constructors))
        (.cons (.of_reach rfl (normal constructors))
          (.cons (.of_reach rfl (normal constructors)) .nil))))

private theorem source_fragment : program.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide⟩
  intro n hn
  have hnames : ∀ n ∈ program.names, ¬ "@".isPrefixOf n := by
    simp only [String.isPrefixOf, String.startsWith_string_iff]
    decide
  exact hnames n hn

theorem certificate_accepted :
    check program certificate = some ⟨conclusion, conclusion⟩ := by
  have hok : sourceOk program = true := by
    exact decide_eq_true source_fragment
  simp only [check, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  decide

private theorem initial_match : ValidQuerySubst registered derive.query [] := by
  have ha : premise ∈ registered.terms := by
    simpa only [registered, Database.terms_setRules, built] using
      Database.mem_addTerm premise declared
  refine ⟨[[]], .cons ⟨⟨List.Perm.refl [], by simp⟩, ?_⟩ .nil, .single []⟩
  exact .expr ha rfl (ha.mono (Database.Contained.addTerms _ _))

theorem premise_exists : premise ∈ reached.terms :=
  (Database.Contained.sUnion registered _).terms (by
    simpa only [registered, Database.terms_setRules, built] using
      Database.mem_addTerm premise declared)

theorem conclusion_exists : conclusion ∈ reached.terms := by
  have hf : evalLocalActions registered derive.actions [] =
      some (registered.addTerm conclusion) := rfl
  have hc : (registered.addTerm conclusion).Contained reached :=
    Database.Contained.mem_sUnion ⟨derive, by simp [registered], rfl,
      [], initial_match, hf⟩
  exact hc.terms (Database.mem_addTerm _ _)

theorem conclusion_not_global :
    check program (.fiat ⟨conclusion, conclusion⟩) = none := by
  have hok : sourceOk program = true := decide_eq_true source_fragment
  simp only [check, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  decide

theorem missing_premise_rejected :
    check program (.rule ⟨conclusion, conclusion⟩ 3 [] []) = none := by
  have hok : sourceOk program = true := decide_eq_true source_fragment
  simp only [check, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  decide

private theorem reached_wf : reached.WF :=
  (source_reached.ctorState Database.CtorState.empty source_fragment.ctorsOnly).wf

theorem source_saturated (R : RulesetName) : RunSaturated R reached := by
  have hfixed : RunRules R reached = reached := by
    apply (runRules_eq_self_iff R reached).mpr
    intro r hr _ out hout
    have hr' : r = derive := by
      change r ∈ insert derive (∅ : Set Rule) at hr
      simpa using hr
    subst r
    obtain ⟨σ, _, hf⟩ := hout
    have he : evalLocalActions reached derive.actions σ =
        some (reached.addTerm conclusion) := rfl
    rw [he] at hf
    obtain rfl := Option.some.inj hf
    constructor
    rintro p (hp | ⟨t, ht, rfl⟩)
    · exact hp
    · exact reached_wf.eqsRefl t (reached_wf.subtermClosed _ conclusion_exists ht)
  have hn : MergeNormal reached := normal constructors
  refine ⟨hn, reached, ?_, Database.SameMeaning.refl _⟩
  change MergeNormalize (RunRules R reached) reached
  rw [hfixed]
  exact ⟨.refl, hn⟩

/-- The checker theorem is instantiated with a real premise and a non-global conclusion. -/
theorem accepted_rule_is_supported : Claim.Supported reached ⟨conclusion, conclusion⟩ :=
  check_supported source_reached reached_wf source_saturated certificate_accepted

theorem accepted_rule_is_sound : Cong reached conclusion conclusion :=
  check_sound source_reached reached_wf source_saturated certificate_accepted
    conclusion_exists conclusion_exists

end Egglog.Tests.SourceProofCorrectness
