import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finite.Prod
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.Representatives

/-! Finite mathematical executions have finite stores. No executable representation is
needed: rule matching ranges over finitely many substitutions at each finite state. -/

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
  exact ⟨hσ.1.subset (List.mem_map.mpr ⟨b, hb, rfl⟩), hσ.mem_terms b hb⟩

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

theorem Database.hasReps_of_finite {db : Database} (h : db.eqs.Finite) : db.HasReps :=
  Database.hasReps_of_finite_terms (Database.finite_terms h)

theorem QueryMatches.finite {db : Database} (ht : db.terms.Finite) (q : Query) :
    {σ | QueryMatches db q σ}.Finite :=
  (ValidEnv.finite ht q.vars).subset fun _ h => h.1

theorem Action.write_finite {σ : Env} {a : Action} {W : Set (Term × Term)}
    (h : a.write σ = some W) : W.Finite := by
  cases a with
  | expr e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Set.finite_singleton _
  | union a b =>
    obtain ⟨t, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp at h
    · cases Option.some.inj h; exact Set.finite_singleton _
  | subsume e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Set.finite_singleton _

theorem Action.writes_finite {σ : Env} {as : List Action} {W : Set (Term × Term)}
    (h : Action.writes σ as = some W) : W.Finite := by
  induction as generalizing W with
  | nil => cases Option.some.inj h; exact Set.finite_empty
  | cons a as ih =>
    obtain ⟨V, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨U, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (Action.write_finite ha).union (ih ht)

theorem RunWrites.finite {db : Database} (he : db.eqs.Finite)
    (R : List Rule) : (RunWrites R db).Finite := by
  have hfin : (⋃ r ∈ {r | r ∈ R}, ⋃ σ ∈ {σ | QueryMatches db r.query σ},
      (Action.writes σ r.actions).getD ∅).Finite :=
    (List.finite_toSet R).biUnion fun r _ =>
      (QueryMatches.finite (Database.finite_terms he) r.query).biUnion
      fun σ _ => by
        cases hw : Action.writes σ r.actions with
        | none => exact Set.finite_empty
        | some W => exact Action.writes_finite hw
  apply hfin.subset
  rintro p ⟨W, ⟨r, hr, σ, hσ, hw⟩, hp⟩
  exact Set.mem_iUnion₂.mpr ⟨r, hr, Set.mem_iUnion₂.mpr ⟨σ, hσ, by simpa [hw] using hp⟩⟩

theorem RunRules.finite_eqs {db : Database} (he : db.eqs.Finite)
    (R : List Rule) : (RunRules R db).eqs.Finite := by
  rw [RunRules.eq_pair]
  exact he.union (RunWrites.finite he R)

theorem Reach.finite {S : Schedule} {db d : Database}
    (h : Reach db S d) (he : db.eqs.Finite) : d.eqs.Finite := by
  induction h with
  | run => exact RunRules.finite_eqs he _
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ he)
  | fixpoint _ _ ih => exact ih he
  | again _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ he)

theorem Reach.finite_from_empty {d : Database} {S : Schedule}
    (h : Reach Database.empty S d) : d.eqs.Finite :=
  h.finite Set.finite_empty

end Egglog
