import EgglogSemantics.Proofs.SourceProof.Matching
import EgglogSemantics.Proofs.Rules

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
    (hclosed : ∀ R, RunSaturated R db) {r : Rule} (hr : Cmd.rule r ∈ P)
    (hof : r.OrderingFree) {σ : Env} {premises fs : List Claim}
    (hp : ∀ c ∈ premises, c.Supported db) (hf : ruleFacts C r σ premises = some fs) :
    ∀ c ∈ fs, c.Supported db := by
  unfold ruleFacts at hf
  split at hf
  · rename_i hchecks
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true] at hchecks
    let A := ledger C.sig premises
    have hA : A.WF := ledger_wf hw C.sig hp
    have hrec : A.Recorded db := ledger_recorded hw C.sig hp
    have hsiga : A.sig = C.sig := ledger_sig _ _
    have henv : A.env = [] := ledger_env _ _
    have hh : ∀ c ∈ premises, c.Holds A := fun _ h => ledger_holds h
    have hval : ∀ b ∈ σ, b.2 ∈ A.terms := fun b hb =>
      supportedValue_sound hA hh (hchecks.1.2 b hb).2
    obtain ⟨τ, hτ, hag⟩ := querySubst_of_matches hchecks.1.1 hval
      (premisesMatch_sound hh (by rw [hsiga]; exact hchecks.2))
    have hfs : actionsFacts ({ A with env := σ } : Database).sig σ r.actions = some fs := by
      rw [hsiga]; exact hf
    obtain ⟨d, hd, hfacts⟩ := actionsFacts_sound hfs
    let post : Database := { d with env := A.env, rules := A.rules }
    have hlocal : evalLocalActions A r.actions σ = some post := by
      simp only [evalLocalActions, henv, List.append_nil, hd, Option.map_some]
      simp only [post, henv]
    have hresult : post ∈ RuleResults A r :=
      ⟨τ, hτ, by rw [evalLocalActions_agree _ hag]; exact hlocal⟩
    obtain ⟨D, hD, hrD, -⟩ := RuleResults.mono_owes hrec hA hw
      (hsiga.trans hC.sig) (henv.trans hs.env.symm) hof hresult
    have hDsub : D.Contained db := (runRules_eq_self_iff r.ruleset db).mp
      (hclosed r.ruleset).1 r ((hs.mem_rules_iff r).mpr (Or.inr hr)) rfl D hD
    have hdpost : d.Contained post := ⟨fun _ h => h⟩
    intro c hc
    exact Claim.Supported.of_recorded (hrD.trans_contained hDsub)
      (evalLocalActions_wf hA hval hlocal) hw
      ((hfacts c hc).mono hdpost)
  · contradiction

end Egglog.SourceProof
