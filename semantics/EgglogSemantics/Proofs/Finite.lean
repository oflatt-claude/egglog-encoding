import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finite.Prod
import EgglogSemantics.Proofs.Step

/-! Finite mathematical executions have finite stores. No executable representation is
needed: rule matching ranges over finitely many substitutions at each finite state. -/

namespace Egglog

private theorem finite_lists {α : Type*} {S : Set α} (hS : S.Finite) (n : Nat) :
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
  exact ⟨hσ.1.subset (List.mem_map.mpr ⟨b, hb, rfl⟩), hσ.2 b hb⟩

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

/-- Only asserted endpoints can be present, even after closing under congruence. -/
theorem Database.finite_terms {db : Database} (h : db.eqs.Finite) : db.terms.Finite := by
  apply ((h.image Prod.fst).union (h.image Prod.snd)).subset
  intro t ht
  obtain ⟨u, htu | hut⟩ := Database.mem_terms_iff.mp ht
  · exact Or.inl ⟨(t, u), htu, rfl⟩
  · exact Or.inr ⟨(u, t), hut, rfl⟩

theorem Database.finite_addTerm {db : Database} (h : db.eqs.Finite) (t : Term) :
    (db.addTerm t).eqs.Finite :=
  h.union ((t.finite_subterms.image fun s => (s, s)))

theorem Database.finite_addEq {db : Database} (h : db.eqs.Finite) (a b : Term) :
    (db.addEq a b).eqs.Finite :=
  (Database.finite_addTerm (Database.finite_addTerm h a) b).insert _

theorem evalAction_finite {db d : Database} {a : Action} (h : db.eqs.Finite)
    (he : evalAction db a = some d) : d.eqs.Finite := by
  cases a with
  | expr e =>
      obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp he
      exact Database.finite_addTerm h t
  | union a b =>
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

theorem RunRules.finite_eqs {db : Database} (he : db.eqs.Finite) (hr : db.rules.Finite)
    (R : RulesetName) : (RunRules R db).eqs.Finite := by
  have hresults : {d | ∃ r ∈ db.rules, r.ruleset = R ∧ d ∈ RuleResults db r}.Finite := by
    apply (hr.biUnion fun r _ => RuleResults.finite (Database.finite_terms he) r).subset
    rintro d ⟨r, hr, _, hd⟩
    exact Set.mem_iUnion₂.mpr ⟨r, hr, hd⟩
  apply he.union (hresults.biUnion ?_)
  rintro d ⟨r, _, _, σ, _, hd⟩
  exact evalLocalActions_finite he hd

theorem MergeStep.finite_eqs {db d : Database} (h : MergeStep db d)
    (he : db.eqs.Finite) : d.eqs.Finite := by
  cases h with
  | @collide d f decl as bs a b vs oldVars newVars body res _ _ _ _ _ _ _ _ hbody _ =>
      have hd := evalActions_finite
        (db := { db with env := mergeEnv oldVars newVars a b }) (d := d) he hbody
      exact Database.finite_addTerm hd _

theorem MergeClosure.finite_eqs {db d : Database} (h : MergeClosure db d)
    (he : db.eqs.Finite) : d.eqs.Finite := by
  induction h with
  | refl => exact he
  | tail _ hs ih => exact hs.finite_eqs ih

/-- Finiteness is preserved by mathematical commands, including a terminating saturation. -/
theorem CmdStep.finite {db d : Database} {c : Cmd} (h : CmdStep db c d)
    (he : db.eqs.Finite) (hr : db.rules.Finite) : d.eqs.Finite ∧ d.rules.Finite := by
  obtain ⟨mid, hm, hc⟩ := h.reach
  suffices hmfin : mid.eqs.Finite ∧ mid.rules.Finite from
    ⟨hc.finite_eqs hmfin.1, hc.envRules.2 ▸ hmfin.2⟩
  cases c with
  | action a => exact ⟨evalAction_finite he hm, (evalAction_rules hm) ▸ hr⟩
  | decl f dc => cases hm; exact ⟨he, hr⟩
  | rule r => cases hm; exact ⟨he, hr.insert r⟩
  | check q => obtain ⟨_, rfl⟩ := hm; exact ⟨he, hr⟩
  | run R => cases hm; exact ⟨RunRules.finite_eqs he hr R, hr⟩
  | saturate R =>
      obtain ⟨hreach, hsat⟩ := hm
      clear hc hsat h
      induction hreach with
      | refl => exact ⟨he, hr⟩
      | tail _ hs ih =>
          exact ⟨hs.finite_eqs (RunRules.finite_eqs ih.1 ih.2 R),
            hs.envRules.2 ▸ ih.2⟩

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

end Egglog
