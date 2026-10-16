import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finite.Prod
import EgglogSemantics.Proofs.Match
import EgglogSemantics.Spec.Step

/-! Finite mathematical executions have finite stores. No executable representation is
needed: rule matching ranges over finitely many substitutions at each finite state.
Current entries are also tracked explicitly by `Database.FiniteStore`. -/

namespace Egglog

/-- Lists of a fixed length over a finite set form a finite set. -/
theorem finite_lists {α : Type*} {S : Set α} (hS : S.Finite) (n : Nat) :
    {xs : List α | xs.length = n ∧ ∀ x ∈ xs, x ∈ S}.Finite := by
  induction n with
  | zero =>
      apply (Set.finite_singleton []).subset
      intro xs hx
      simpa only [List.length_eq_zero_iff, Set.mem_singleton_iff] using hx.1
  | succ n ih =>
      apply (hS.image2 List.cons ih).subset
      intro xs hx
      cases xs with
      | nil => simp at hx
      | cons x xs =>
          exact ⟨x, hx.2 x (by simp), xs,
            ⟨by simpa using hx.1, fun y hy => hx.2 y (by simp [hy])⟩, rfl⟩

theorem ValidEnv.finite {db : Database} (ht : db.terms.Finite) (vs : List Var) :
    {σ | ValidEnv vs db σ}.Finite := by
  apply (finite_lists ((List.finite_toSet vs).prod ht) vs.length).subset
  intro σ hσ
  refine ⟨by simpa [Env.dom] using hσ.1.length_eq, ?_⟩
  intro b hb
  exact ⟨hσ.1.subset (List.mem_map.mpr ⟨b, hb, rfl⟩), (hσ.2 b hb).1⟩

theorem ValidSubst.finite {db : Database} (ht : db.terms.Finite) (p : Pattern) :
    {σ | ValidSubst db p σ}.Finite :=
  (ValidEnv.finite ht (p.freeVars [])).subset fun _ h => h.1

theorem Env.UnionAll.eq_flatten {σs : List Env} {σ : Env} (h : Env.UnionAll σs σ) :
    σ = σs.flatten := by
  induction h with
  | nil => rfl
  | single => simp
  | step hu _ ih => simpa [hu.2, List.append_assoc] using ih

theorem ValidQuerySubst.finite {db : Database} (ht : db.terms.Finite) (q : Query) :
    {σ | ValidQuerySubst db q σ}.Finite := by
  have hseq : {σs | List.Forall₂ (ValidSubst db) q σs}.Finite := by
    induction q with
    | nil =>
        apply (Set.finite_singleton []).subset
        intro σs h; cases h; rfl
    | cons p ps ih =>
        apply ((ValidSubst.finite ht p).image2 List.cons ih).subset
        intro σs h
        cases h with
        | cons hp hps => exact ⟨_, hp, _, hps, rfl⟩
  apply (hseq.image List.flatten).subset
  rintro σ ⟨σs, hs, hu⟩
  exact ⟨σs, hs, hu.eq_flatten.symm⟩

theorem Term.finite_subterms (t : Term) : t.subterms.Finite := by
  apply (List.finite_toSet t.subtermList).subset
  intro s hs
  exact (Term.mem_subtermList t).mpr hs

/-- A finite assertion set has finitely many subterms. -/
theorem Database.finite_terms {db : Database} (h : db.eqs.Finite) : db.terms.Finite := by
  apply (h.biUnion (fun p _ => p.1.finite_subterms.union p.2.finite_subterms)).subset
  intro t ht
  obtain ⟨p, hp, ht⟩ := Database.mem_terms_iff.mp ht
  exact Set.mem_iUnion₂.mpr ⟨p, hp, ht⟩

theorem Database.finite_addTerm {db : Database} (h : db.eqs.Finite) (t : Term) :
    (db.addTerm t).eqs.Finite := h.insert _

theorem Database.finite_addTerms {db : Database} (h : db.eqs.Finite) (ts : List Term) :
    (db.addTerms ts).eqs.Finite := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (Database.finite_addTerm h t)

theorem Database.finite_addEq {db : Database} (h : db.eqs.Finite) (a b : Term) :
    (db.addEq a b).eqs.Finite :=
  h.insert _

theorem Database.finite_eraseEntry {db : Database} (h : db.eqs.Finite) (row : Entry) :
    (db.eraseEntry row).eqs.Finite := by
  apply (h.subset Set.sdiff_subset).union
  simpa only [Set.image, Set.mem_setOf_eq, eq_comm] using
    (List.finite_toSet row.columns).image (fun t => (t, t))

theorem evalAction_finite {db d : Database} {a : Action} (h : db.eqs.Finite)
    (he : evalAction db a = some d) : d.eqs.Finite := by
  cases a with
  | expr e =>
      obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp he
      exact Database.finite_addTerm h t
  | union a b =>
      rw [evalAction] at he
      obtain ⟨ta, _, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨tb, _, he⟩ := Option.bind_eq_some_iff.mp he
      split at he
      · simp at he
      · cases he; exact Database.finite_addEq h ta tb

theorem evalActions_finite {as : List Action} {db d : Database} (h : db.eqs.Finite)
    (he : evalActions db as = some d) : d.eqs.Finite := by
  induction as generalizing db with
  | nil => cases he; exact h
  | cons a as ih =>
      obtain ⟨mid, hm, hd⟩ := Option.bind_eq_some_iff.mp he
      exact ih (evalAction_finite h hm) hd

theorem evalLocalActions_finite {as : List Action} {db d : Database} {σ : Env}
    (h : db.eqs.Finite) (he : evalLocalActions db as σ = some d) : d.eqs.Finite := by
  obtain ⟨mid, hm, rfl⟩ := Option.map_eq_some_iff.mp he
  exact evalActions_finite (db := { db with env := σ ++ db.env }) (d := mid) h hm

theorem RuleResults.finite {db : Database} (ht : db.terms.Finite) (r : Rule) :
    (RuleResults db r).Finite := by
  classical
  apply ((ValidQuerySubst.finite ht r.query).image
    (fun σ => (evalLocalActions db r.actions σ).getD db)).subset
  rintro d ⟨σ, hσ, hd⟩
  exact ⟨σ, hσ, by simp [hd]⟩

private theorem finite_rule_results {db : Database}
    (he : db.eqs.Finite) (hr : db.rules.Finite) (R : RulesetName) :
    {d | ∃ r ∈ db.rules, r.ruleset = R ∧ d ∈ RuleResults db r}.Finite := by
  apply (hr.biUnion fun r _ => RuleResults.finite (Database.finite_terms he) r).subset
  rintro d ⟨r, hr, _, hd⟩
  exact Set.mem_iUnion₂.mpr ⟨r, hr, hd⟩

theorem RunRules.finite_eqs {db : Database} (he : db.eqs.Finite) (hr : db.rules.Finite)
    (R : RulesetName) : (RunRules R db).eqs.Finite := by
  apply he.union ((finite_rule_results he hr R).biUnion ?_)
  rintro d ⟨r, _, _, σ, _, hd⟩
  exact evalLocalActions_finite he hd

theorem MergeValues.finite_eqs {db d : Database} {decl : FnDecl}
    {old new vs : List Term} (h : MergeValues db decl old new d vs)
    (he : db.eqs.Finite) : d.eqs.Finite := by
  cases h with
  | unchanged => exact he
  | changed _ _ hbody _ =>
      have hf := evalActions_finite (db := { db with env := mergeEnv _ _ old new })
        (d := _) he hbody
      exact hf

theorem MergeValues.finite_rules {db d : Database} {decl : FnDecl}
    {old new vs : List Term} (h : MergeValues db decl old new d vs)
    (hr : db.rules.Finite) : d.rules.Finite := by
  cases h <;> exact hr

theorem MergeStep.finite_eqs {db d : Database} (h : MergeStep db d)
    (he : db.eqs.Finite) : d.eqs.Finite := by
  cases h with
  | collide _ _ _ _ _ _ hv =>
      exact Database.finite_addTerm
        (hv.finite_eqs (Database.finite_eraseEntry (Database.finite_eraseEntry he _) _)) _

theorem MergeStep.finite_rules {db d : Database} (h : MergeStep db d)
    (hr : db.rules.Finite) : d.rules.Finite := by
  cases h with
  | collide _ _ _ _ _ _ hv => simpa using hv.finite_rules hr

theorem MergeClosure.finite_eqs {db d : Database} (h : MergeClosure db d)
    (he : db.eqs.Finite) : d.eqs.Finite := by
  induction h with
  | refl => exact he
  | tail _ hs ih => exact hs.finite_eqs ih

theorem MergeClosure.finite_rules {db d : Database} (h : MergeClosure db d)
    (hr : db.rules.Finite) : d.rules.Finite := by
  induction h with
  | refl => exact hr
  | tail _ hs ih => exact hs.finite_rules ih

theorem RunStep.finite {R : RulesetName} {db d : Database} (h : RunStep R db d)
    (he : db.eqs.Finite) (hr : db.rules.Finite) : d.eqs.Finite ∧ d.rules.Finite :=
  ⟨h.1.finite_eqs (RunRules.finite_eqs he hr R), h.1.finite_rules hr⟩

theorem SaturateReach.finite {R : RulesetName} {db d : Database}
    (h : SaturateReach R db d) (he : db.eqs.Finite) (hr : db.rules.Finite) :
    d.eqs.Finite ∧ d.rules.Finite := by
  induction h with
  | done hs _ => exact hs.finite he hr
  | step hs _ _ ih =>
      obtain ⟨he, hr⟩ := hs.finite he hr
      exact ih he hr

/-- Finiteness is preserved by mathematical commands, including a terminating saturation. -/
theorem CmdStep.finite {db d : Database} {c : Cmd} (h : CmdStep db c d)
    (he : db.eqs.Finite) (hr : db.rules.Finite) : d.eqs.Finite ∧ d.rules.Finite := by
  obtain ⟨mid, hm, hc⟩ := h.reach
  suffices hmfin : mid.eqs.Finite ∧ mid.rules.Finite from
    ⟨hc.finite_eqs hmfin.1, hc.finite_rules hmfin.2⟩
  cases c with
  | action a => exact ⟨evalAction_finite he hm, (evalAction_rules hm) ▸ hr⟩
  | decl f dc => cases hm; exact ⟨he, hr⟩
  | rule r => cases hm; exact ⟨he, hr.insert r⟩
  | check q => obtain ⟨_, rfl⟩ := hm; exact ⟨he, hr⟩
  | run R => cases hm; exact ⟨RunRules.finite_eqs he hr R, hr⟩
  | saturate R => exact (show SaturateReach R db mid from hm).finite he hr

theorem ProgramStep.finite {db d : Database} {P : Program} (h : ProgramStep db P d)
    (he : db.eqs.Finite) (hr : db.rules.Finite) : d.eqs.Finite ∧ d.rules.Finite := by
  induction h with
  | nil => exact ⟨he, hr⟩
  | cons hc _ ih =>
      obtain ⟨he, hr⟩ := hc.finite he hr
      exact ih he hr

theorem ProgramStep.finite_from_empty {d : Database} {P : Program}
    (h : ProgramStep Database.empty P d) : d.eqs.Finite ∧ d.rules.Finite :=
  h.finite Set.finite_empty Set.finite_empty

/-- All dynamically growing stores are finite. The signature and environment need no
extra premise: the signature is metadata and every environment is already a list. -/
structure Database.FiniteStore (db : Database) : Prop where
  eqs : db.eqs.Finite
  entries : db.entries.Finite
  rules : db.rules.Finite

namespace Database.FiniteStore

theorem of_eqs_rules {db : Database} (he : db.eqs.Finite) (hr : db.rules.Finite) :
    db.FiniteStore := ⟨he, Database.finite_entries he, hr⟩

theorem setEnv {db : Database} (h : db.FiniteStore) (env : Env) :
    ({ db with env } : Database).FiniteStore := ⟨h.eqs, h.entries, h.rules⟩

theorem setSig {db : Database} (h : db.FiniteStore) (sig : Signature) :
    ({ db with sig } : Database).FiniteStore := of_eqs_rules h.eqs h.rules

theorem empty : Database.empty.FiniteStore :=
  of_eqs_rules Set.finite_empty Set.finite_empty

theorem addTerm {db : Database} (h : db.FiniteStore) (t : Term) :
    (db.addTerm t).FiniteStore :=
  of_eqs_rules (Database.finite_addTerm h.eqs t) h.rules

theorem addTerms {db : Database} (h : db.FiniteStore) (ts : List Term) :
    (db.addTerms ts).FiniteStore := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem addEq {db : Database} (h : db.FiniteStore) (a b : Term) :
    (db.addEq a b).FiniteStore :=
  of_eqs_rules (Database.finite_addEq h.eqs a b) h.rules

theorem putEntry {db : Database} (h : db.FiniteStore) (e : Entry) :
    (db.putEntry e).FiniteStore := h.addTerm e.atom

theorem eraseEntry {db : Database} (h : db.FiniteStore) (e : Entry) :
    (db.eraseEntry e).FiniteStore :=
  of_eqs_rules (Database.finite_eraseEntry h.eqs e) (by simpa using h.rules)

end Database.FiniteStore

theorem evalAction_finiteStore {db d : Database} {a : Action} (h : db.FiniteStore)
    (he : evalAction db a = some d) : d.FiniteStore := by
  cases a with
  | expr e =>
      obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp he
      exact h.addTerm t
  | union a b =>
      rw [evalAction] at he
      obtain ⟨ta, _, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨tb, _, he⟩ := Option.bind_eq_some_iff.mp he
      split at he
      · simp at he
      · cases he; exact h.addEq ta tb

theorem evalActions_finiteStore {as : List Action} {db d : Database}
    (h : db.FiniteStore) (he : evalActions db as = some d) : d.FiniteStore := by
  induction as generalizing db with
  | nil => cases he; exact h
  | cons a as ih =>
      obtain ⟨mid, hm, hd⟩ := Option.bind_eq_some_iff.mp he
      exact ih (evalAction_finiteStore h hm) hd

theorem evalLocalActions_finiteStore {as : List Action} {db d : Database} {σ : Env}
    (h : db.FiniteStore) (he : evalLocalActions db as σ = some d) : d.FiniteStore := by
  obtain ⟨mid, hm, rfl⟩ := Option.map_eq_some_iff.mp he
  have hmfin := evalActions_finiteStore (h.setEnv (σ ++ db.env)) hm
  exact ⟨hmfin.eqs, hmfin.entries, h.rules⟩

theorem RunRules.finiteStore {db : Database} (h : db.FiniteStore) (R : RulesetName) :
    (RunRules R db).FiniteStore :=
  Database.FiniteStore.of_eqs_rules (RunRules.finite_eqs h.eqs h.rules R) h.rules

theorem MergeValues.finiteStore {db d : Database} {decl : FnDecl}
    {old new vs : List Term} (h : MergeValues db decl old new d vs)
    (hf : db.FiniteStore) : d.FiniteStore := by
  cases h with
  | unchanged => exact hf
  | changed _ _ hbody _ =>
      have h' := evalActions_finiteStore (hf.setEnv (mergeEnv _ _ old new)) hbody
      exact ⟨h'.eqs, h'.entries, hf.rules⟩

theorem MergeStep.finiteStore {db d : Database} (h : MergeStep db d)
    (hf : db.FiniteStore) : d.FiniteStore := by
  cases h with
  | collide _ _ _ _ _ _ hv =>
      exact (hv.finiteStore ((hf.eraseEntry _).eraseEntry _)).putEntry _

theorem MergeClosure.finiteStore {db d : Database} (h : MergeClosure db d)
    (hf : db.FiniteStore) : d.FiniteStore := by
  induction h with
  | refl => exact hf
  | tail _ hs ih => exact hs.finiteStore ih

theorem RunStep.finiteStore {R : RulesetName} {db d : Database}
    (h : RunStep R db d) (hf : db.FiniteStore) : d.FiniteStore :=
  h.1.finiteStore (RunRules.finiteStore hf R)

theorem SaturateReach.finiteStore {R : RulesetName} {db d : Database}
    (h : SaturateReach R db d) (hf : db.FiniteStore) : d.FiniteStore := by
  induction h with
  | done hs _ => exact hs.finiteStore hf
  | step hs _ _ ih => exact ih (hs.finiteStore hf)

theorem CmdStep.finiteStore {db d : Database} {c : Cmd}
    (h : CmdStep db c d) (hf : db.FiniteStore) : d.FiniteStore := by
  obtain ⟨mid, hm, hc⟩ := h.reach
  apply hc.finiteStore
  cases c with
  | action a => exact evalAction_finiteStore hf hm
  | decl f dc => cases hm; exact hf.setSig _
  | rule r => cases hm; exact ⟨hf.eqs, hf.entries, hf.rules.insert r⟩
  | check q => obtain ⟨_, rfl⟩ := hm; exact hf
  | run R => cases hm; exact RunRules.finiteStore hf R
  | saturate R => exact (show SaturateReach R db mid from hm).finiteStore hf

theorem ProgramStep.finiteStore {db d : Database} {P : Program}
    (h : ProgramStep db P d) (hf : db.FiniteStore) : d.FiniteStore := by
  induction h with
  | nil => exact hf
  | cons hc _ ih => exact ih (hc.finiteStore hf)

/-- Actual finite mathematical executions from the empty database have finite current
entries, equalities, and registered rules. -/
theorem ProgramStep.finiteStore_from_empty {d : Database} {P : Program}
    (h : ProgramStep Database.empty P d) : d.FiniteStore :=
  h.finiteStore Database.FiniteStore.empty

end Egglog
