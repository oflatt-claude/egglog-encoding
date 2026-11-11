import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.MatchValues

namespace Egglog

/-- A term property, closed under subterms, can be checked on asserted endpoints. -/
theorem Database.terms_preserved {db : Database} {P : Term → Prop}
    (hsub : ∀ t, P t → ∀ s ∈ t.subterms, P s)
    (h : ∀ p ∈ db.eqs, P p.1 ∧ P p.2) : ∀ t ∈ db.terms, P t := by
  rintro t ⟨p, hp, ht | ht⟩
  · exact hsub _ (h p hp).1 t ht
  · exact hsub _ (h p hp).2 t ht

/-- Every written endpoint comes from a single successful action. -/
theorem Action.mem_writes {σ : Env} {as : List Action} {W : Set (Term × Term)}
    (h : Action.writes σ as = some W) {p : Term × Term} (hp : p ∈ W) :
    ∃ a ∈ as, ∃ V, a.write σ = some V ∧ p ∈ V := by
  induction as generalizing W with
  | nil => cases Option.some.inj h; exact hp.elim
  | cons a as ih =>
    obtain ⟨V, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨U, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases hp with hp | hp
    · exact ⟨a, by simp, V, ha, hp⟩
    · obtain ⟨b, hb, V, hv, hp⟩ := ih ht hp
      exact ⟨b, by simp [hb], V, hv, hp⟩

/-- All results evaluated by an action satisfy a term property. -/
def Action.EvalTerms (σ : Env) (P : Term → Prop) : Action → Prop
  | .expr e => ∀ t, e.eval σ = some t → P t
  | .subsume f es => ∀ t, (Expr.app f es).eval σ = some t → P t
  | .union a b => (∀ t, a.eval σ = some t → P t) ∧ (∀ t, b.eval σ = some t → P t)

theorem Action.write_satisfies {σ : Env} {P : Term → Prop} {a : Action}
    (h : a.EvalTerms σ P) {W : Set (Term × Term)} (hw : a.write σ = some W) :
    ∀ p ∈ W, P p.1 ∧ P p.2 := by
  cases a with
  | expr e =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hw
    rintro p rfl
    exact ⟨h t ht, h t ht⟩
  | union a b =>
    obtain ⟨t, ht, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨u, hu, hw⟩ := Option.bind_eq_some_iff.mp hw
    split at hw
    · simp at hw
    · cases Option.some.inj hw
      rintro p rfl
      exact ⟨h.1 t ht, h.2 u hu⟩
  | subsume f es =>
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hw
    rintro p rfl
    have ht := h (.app f ts) (by simp [Expr.eval, hts])
    exact ⟨ht, ht⟩

/-- A round preserves any subterm-closed property shared by the existing terms and
the endpoints written by its actions. -/
theorem RunRules.preserves {P : Term → Prop} {db : Database} {R : List Rule}
    (hsub : ∀ t, P t → ∀ s ∈ t.subterms, P s) (hd : ∀ t ∈ db.terms, P t)
    (hw : ∀ r ∈ R, ∀ σ, QueryMatches db r.query σ →
      ∀ a ∈ r.actions, ∀ W, a.write σ = some W → ∀ p ∈ W, P p.1 ∧ P p.2) :
    ∀ t ∈ (RunRules R db).terms, P t := by
  rw [RunRules.eq_pair]
  apply Database.terms_preserved hsub
  intro p hp
  rcases hp with hp | hp
  · exact ⟨hd _ ⟨p, hp, Or.inl (.refl _)⟩, hd _ ⟨p, hp, Or.inr (.refl _)⟩⟩
  · obtain ⟨W, ⟨r, hr, σ, hσ, hW⟩, hp⟩ := hp
    obtain ⟨a, ha, V, hv, hp⟩ := Action.mem_writes hW hp
    exact hw r hr σ hσ a ha V hv p hp

theorem RunRules.preserves_evalTerms {P : Term → Prop} {db : Database} {R : List Rule}
    (hsub : ∀ t, P t → ∀ s ∈ t.subterms, P s) (hd : ∀ t ∈ db.terms, P t)
    (hf : ∀ r ∈ R, ∀ σ, QueryMatches db r.query σ →
      ∀ a ∈ r.actions, a.EvalTerms σ P) : ∀ t ∈ (RunRules R db).terms, P t :=
  RunRules.preserves hsub hd
    fun r hr σ hσ a ha W hw => Action.write_satisfies (hf r hr σ hσ a ha) hw

end Egglog
