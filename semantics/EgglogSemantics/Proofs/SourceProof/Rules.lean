import EgglogSemantics.Proofs.SourceProof.Matching
import EgglogSemantics.Proofs.RuleStore
import EgglogSemantics.Proofs.SourceModel
import EgglogSemantics.Proofs.Congruence.SourceState

namespace Egglog.SourceProof

/-- `sourceOk` is `Program.Fragment`, decided. -/
theorem sourceOk_fragment {P : Program} (h : sourceOk P = true) : P.Fragment :=
  of_decide_eq_true h

/-- `Program.OrderingFree` at a member command. -/
private theorem orderingFree_of_mem : ∀ {P : Program}, Program.OrderingFree P →
    ∀ {c : Cmd}, c ∈ P → c.OrderingFree
  | [], _, _, hc => absurd hc (by simp)
  | _ :: _, h, _, hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact orderingFree_of_mem h.2 hc

/-- The fragment computes with no `min`, so neither does any of its rules. -/
theorem sourceOk_rule {P : Program} (h : sourceOk P = true) {r : Rule}
    (hr : Cmd.rule r ∈ P) : r.OrderingFree :=
  orderingFree_of_mem (sourceOk_fragment h).noMin hr

theorem sourceOk_ctors {P : Program} (h : sourceOk P = true) : P.CtorDecls :=
  (sourceOk_fragment h).ctorsOnly

/-- A checked head fact follows from a valid source rule firing, up to supported terms. -/
theorem ruleFacts_supported {P : Program} {C : Context} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF) (hC : C.Sound db)
    (hclosed : ∀ R, RunSaturated R db) (hok : sourceOk P = true) {r : Rule} (hr : Cmd.rule r ∈ P)
    {σ : Env} {premises fs : List Claim}
    (hp : ∀ c ∈ premises, c.Supported db) (hf : ruleFacts C r σ premises = some fs) :
    ∀ c ∈ fs, c.Supported db := by
  unfold ruleFacts at hf
  split at hf
  · rename_i hchecks
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true] at hchecks
    have hctors := sourceOk_ctors hok
    have hcs := hs.ctorState Database.CtorState.empty hctors
    have hb := Congruence.termsBuild_of_programStep hctors hs
    have hvalue : ∀ t ∈ db.terms, t.IsValue db.sig := by
      intro t ht
      induction t using Term.recTerm with
      | lit l => exact .lit _ _
      | app f as ih =>
          exact .app (hb f as ht) fun a ha => ih a ha
            (hw.subtermClosed _ ht (Term.arg_subterms ha (Term.self_mem_subterms _)))
    have hnone : ∀ row, row ∉ db.entries := by
      intro row hr
      obtain ⟨decl, hd, hm, _⟩ := hr.1
      exact hm (by simpa [Signature.mergeOf, hd] using hcs.sig row.name)
    have hstore : db.StoreOk :=
      ⟨fun row hr => (hnone row hr).elim, fun row hr => (hnone row hr).elim,
        fun p hp => Or.inl ⟨hvalue _ (Cong.direct hp).mem_left,
          hvalue _ (Cong.direct hp).mem_right⟩,
        fun b hb => hvalue _ (hw.envInTerms b hb)⟩
    have hmodel : ∀ R, RunRules R db.completion = db.completion := by
      intro R
      apply SourceMeaning.completion_closed_of_saturated hw hstore hcs.sig hs.env
        (fun r hr _ => sourceOk_rule hok ?_) (hclosed R)
      simpa [Database.empty] using (hs.mem_rules_iff r).mp hr
    have hh : ∀ c ∈ premises, c.Holds db.completion :=
      fun c hc => (hp c hc).completion hw
    have hval : ∀ b ∈ σ, b.2 ∈ db.completion.values := by
      intro b hb
      exact ⟨supportedValue_sound hw.completion hh (hchecks.1.2 b hb).2,
        hC.sig ▸ valueOk_isValue (hchecks.1.2 b hb).1⟩
    obtain ⟨τ, hτ, hag⟩ := querySubst_of_matches hchecks.1.1 hval
      (premisesMatch_sound hh (by
        change premisesMatch db.sig σ r.query premises = true
        rw [← hC.sig]; exact hchecks.2))
    have hfs : actionsFacts db.completion.sig σ r.actions = some fs := by
      change actionsFacts db.sig σ r.actions = some fs
      rw [← hC.sig]; exact hf
    obtain ⟨d, hd, hfacts⟩ := actionsFacts_sound
      (db := { db.completion with env := σ }) hfs
    let post : Database := { d with env := db.env, rules := db.rules }
    have hlocal : evalLocalActions db.completion r.actions σ = some post := by
      have henv : db.completion.env = [] := hs.env
      simp only [evalLocalActions, henv, List.append_nil, hd, Option.map_some]
      simp only [post, show db.env = [] from hs.env]
      rfl
    have hresult : post ∈ RuleResults db.completion r :=
      ⟨τ, hτ, by rw [evalLocalActions_agree _ hag]; exact hlocal⟩
    have hpost : post.Contained db.completion :=
      (runRules_eq_self_iff r.ruleset db.completion).mp (hmodel r.ruleset)
        r ((hs.mem_rules_iff r).mpr (Or.inr hr)) rfl post hresult
    have hdpost : d.Contained post := ⟨fun _ h => h⟩
    exact fun c hc => Claim.Supported.of_completion hw
      (((hfacts c hc).mono hdpost).mono hpost)
  · contradiction

end Egglog.SourceProof
