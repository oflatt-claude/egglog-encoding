import EgglogSemantics.Proofs.Congruence.AbstractComplete

/-! Non-vacuity checks for the mathematical compiler theorem. These witnesses use
`Database`, `CmdStep`, and `Eval` directly; no interpreter correctness bridge is used. -/

namespace Egglog.Tests.CongruenceCorrectness

open Congruence

def ctorTerm : Term := .app "C" []
def constructorExpr : Expr := .app "C" []
def constructorQuery : Query := [.expr constructorExpr]
def view : Term := .app (viewName "C") [ctorTerm]
def viewQuery : Query := [.expr (.app (viewName "C") [.var (freshVar 0)])]

/-- The successful check observes a term built by the preceding action. -/
def successProgram : Program :=
  [.decl "C" (ctorDecl 0), .action (.expr constructorExpr), .check constructorQuery]

/-- Declaration alone does not build an instance, so this check fails dynamically. -/
def failureProgram : Program :=
  [.decl "C" (ctorDecl 0), .check constructorQuery]

private theorem safe_name : ¬ "@".isPrefixOf "C" := by
  rw [String.isPrefixOf, String.startsWith_string_iff]
  decide

theorem success_wellFormed : successProgram.WellFormed := by decide
theorem success_fragment : successProgram.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide⟩
  intro n hn
  change n ∈ ["C"] at hn
  obtain rfl := List.mem_singleton.mp hn
  exact safe_name

theorem failure_wellFormed : failureProgram.WellFormed := by decide
theorem failure_fragment : failureProgram.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide⟩
  intro n hn
  change n ∈ ["C"] at hn
  obtain rfl := List.mem_singleton.mp hn
  exact safe_name

def sourceDeclared : Database :=
  { Database.empty with sig := Function.update Database.empty.sig "C" (some (ctorDecl 0)) }
def sourceBuilt : Database := sourceDeclared.addTerm ctorTerm

private theorem no_query_of_empty {d : Database} (hd : d.eqs = ∅) {q : Query}
    (hq : q ≠ []) : ¬ QueryHolds d q := by
  rintro ⟨σ, σs, hσs, _⟩
  cases q with
  | nil => exact hq rfl
  | cons p ps =>
      cases hσs with
      | cons hp _ =>
          cases hp.2 with
          | expr hw _ _ => simp [Database.terms_empty_of_eqs_empty hd] at hw
          | eq hw _ _ _ _ => simp [Database.terms_empty_of_eqs_empty hd] at hw

private theorem source_check : QueryHolds sourceBuilt constructorQuery := by
  obtain ⟨σ, hσ, _⟩ := Abstract.validQuerySubst_of_flatReads
    (d := sourceBuilt) (ρ := []) (q := constructorQuery)
    (by simp [Env.lookup]) (by
      intro p hp
      obtain rfl := List.mem_singleton.mp hp
      exact .entry (by rfl) rfl (Database.mem_addTerm _ _))
  exact ⟨σ, hσ⟩

theorem source_success : Eval Database.empty successProgram (.ok sourceBuilt) := by
  exact .cons (.ok (.of_reach rfl))
    (.cons (.ok (.of_reach rfl)) (.cons (.ok ⟨source_check, rfl⟩) .nil))

theorem source_failure : Eval Database.empty failureProgram .checkFailed := by
  exact .cons (.ok (.of_reach rfl))
    (.fail (.checkFailed (no_query_of_empty (d := sourceDeclared) rfl (by decide))))

def targetSetup : Program :=
  [.decl ufName (tableDecl 1), .decl "C" (ctorDecl 0),
   .decl (viewName "C") (tableDecl 0),
   .rule pathCompressRule, .rule (eclassRule "C" 0)]

def targetDeclared : Database :=
  { sig := Function.update
      (Function.update (Function.update Database.empty.sig ufName (some (tableDecl 1)))
        "C" (some (ctorDecl 0))) (viewName "C") (some (tableDecl 0)),
    eqs := ∅, env := [], rules := insert (eclassRule "C" 0) (insert pathCompressRule ∅) }

def targetBuilt : Database := targetDeclared.addTerm view

private theorem target_setup : ProgramStep Database.empty targetSetup targetDeclared := by
  exact .cons (.of_reach rfl) (.cons (.of_reach rfl) (.cons (.of_reach rfl)
    (.cons (.of_reach rfl) (.cons (.of_reach rfl) .nil))))

private theorem success_encoding : encode successProgram = targetSetup ++
    [.action (.expr (.app (viewName "C") [constructorExpr])),
     .saturate rebuildRuleset, .check viewQuery] := by rfl

private theorem failure_encoding : encode failureProgram = targetSetup ++ [.check viewQuery] :=
  by rfl

private theorem target_terms : targetBuilt.terms = {view, ctorTerm} := by
  have he : targetDeclared.terms = ∅ := Database.terms_empty_of_eqs_empty rfl
  simp [targetBuilt, Database.addTerm_terms, he, view, ctorTerm]

private theorem target_diagonal : targetBuilt.Diag :=
  (show targetDeclared.Diag from fun _ h => h.elim).addTerm view

private theorem target_noUF (cols : List Term) :
    Term.app ufName cols ∉ targetBuilt.terms := by
  rw [target_terms]
  simp [view, ctorTerm, ufName, viewName]

private theorem target_noUF_match (es : List Expr) (σ : Env) :
    ¬ Matches targetBuilt (.expr (.app ufName es)) σ := by
  intro h
  cases h with
  | expr hw he hc =>
      obtain ⟨cols, _, rfl⟩ := Expr.evalAtom_app_inv he
      exact target_noUF cols ((congOn_eq_of_diag target_diagonal hc) ▸ hw)

private theorem target_noUF_query {q : Query} {σ : Env} {es : List Expr}
    (hp : Pattern.expr (.app ufName es) ∈ q) : ¬ ValidQuerySubst targetBuilt q σ := by
  rintro ⟨σs, hσs, _⟩
  obtain ⟨ρ, _, hρ⟩ := hσs.flip.exists_left hp
  exact target_noUF_match es ρ hρ.2

private theorem target_merges_saturated : MergeNormal targetBuilt := by
  intro d h
  cases h with
  | @collide post f decl as bs a b vs oldVars newVars body res
      hf hm hconf _ _ hleft hright hk _ _ =>
      have hab : as = bs := CongList.eq_of_diag target_diagonal hk
      subst bs
      rw [target_terms] at hleft hright
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, view, ctorTerm,
        Term.app.injEq] at hleft hright
      rcases hleft with ⟨rfl, hcols⟩ | ⟨rfl, _⟩
      · have hdecl : decl = tableDecl 0 := by simpa [targetBuilt, targetDeclared] using hf.symm
        subst decl
        have hm' := Option.some.inj hm
        injection hm' with _ _ hbody _
        subst body
        rcases hright with ⟨_, hcols'⟩ | ⟨hbad, _⟩
        · have hab : a = b := List.append_cancel_left (hcols.trans hcols'.symm)
          subst b
          exact (tableDecl_no_self_conflict 0 a hconf).elim
        · simp [viewName] at hbad
      · have hdecl : decl = ctorDecl 0 := by
          simpa [targetBuilt, targetDeclared, viewName, ufName] using hf.symm
        subst decl
        simp [ctorDecl] at hm

private theorem target_saturated : RunSaturated rebuildRuleset targetBuilt := by
  refine ⟨(runRules_eq_self_iff _ _).mpr ?_, target_merges_saturated⟩
  intro r hr _ d hd
  obtain ⟨σ, hσ, _⟩ := hd
  have hr' : r = eclassRule "C" 0 ∨ r = pathCompressRule := by
    simpa [targetBuilt, targetDeclared] using hr
  rcases hr' with rfl | rfl
  · exact (target_noUF_query (es := [.var "@e", .var "@x"])
      (by simp [eclassRule]) hσ).elim
  · exact (target_noUF_query (es := [.var "@a", .var "@b"])
      (by simp [pathCompressRule]) hσ).elim

private theorem target_check : QueryHolds targetBuilt viewQuery := by
  have hc : ctorTerm ∈ targetBuilt.terms := by rw [target_terms]; simp
  obtain ⟨σ, hσ, _⟩ := Abstract.validQuerySubst_of_flatReads
    (d := targetBuilt) (ρ := [(freshVar 0, ctorTerm)]) (q := viewQuery)
    (by
      intro v i hi
      simp only [Env.lookup] at hi
      split at hi
      · exact Option.some.inj hi ▸ hc
      · simp at hi)
    (by
      intro p hp
      obtain rfl := List.mem_singleton.mp hp
      exact .entry (by rfl) (by rfl) (Database.mem_addTerm _ _))
  exact ⟨σ, hσ⟩

theorem target_success : Eval Database.empty (encode successProgram) (.ok targetBuilt) := by
  rw [success_encoding]
  apply Eval.append_of_ok target_setup
  exact .cons (.ok (.of_reach rfl))
    (.cons (.ok (.of_reach ⟨.refl, target_saturated⟩))
      (.cons (.ok ⟨target_check, rfl⟩) .nil))

theorem target_failure : Eval Database.empty (encode failureProgram) .checkFailed := by
  rw [failure_encoding]
  apply Eval.append_of_ok target_setup
  exact .fail (.checkFailed (no_query_of_empty (d := targetDeclared) rfl (by decide)))

/-- Both premises of the correctness theorem are inhabited for a successful check. -/
theorem successful_instance :
    successProgram.WellFormed ∧ successProgram.Fragment ∧
    ∃ source target, Eval Database.empty successProgram source ∧
      Eval Database.empty (encode successProgram) target ∧
      source.succeeded = true ∧ target.succeeded = true := by
  refine ⟨success_wellFormed, success_fragment, .ok sourceBuilt, .ok targetBuilt,
    source_success, target_success, rfl, ?_⟩
  exact (preservesObservations successProgram success_wellFormed success_fragment _ _
    source_success target_success).symm

/-- Both premises are also inhabited for genuine dynamic check failure. -/
theorem failing_instance :
    failureProgram.WellFormed ∧ failureProgram.Fragment ∧
    ∃ source target, Eval Database.empty failureProgram source ∧
      Eval Database.empty (encode failureProgram) target ∧
      source.succeeded = false ∧ target.succeeded = false := by
  refine ⟨failure_wellFormed, failure_fragment, .checkFailed, .checkFailed,
    source_failure, target_failure, rfl, ?_⟩
  exact (preservesObservations failureProgram failure_wellFormed failure_fragment _ _
    source_failure target_failure).symm

/-- The finite-outcome contract rejects a compiler that simply erases every program. -/
theorem rejects_empty_compiler : ¬ (∀ P : Program, P.WellFormed → P.Fragment →
    ∀ source target : Result, Eval Database.empty P source →
      Eval Database.empty ([] : Program) target → source.succeeded = target.succeeded) := by
  intro h
  have heq := h failureProgram failure_wellFormed failure_fragment .checkFailed
    (.ok Database.empty) source_failure .nil
  contradiction

end Egglog.Tests.CongruenceCorrectness
