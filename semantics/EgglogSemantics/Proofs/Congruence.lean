import EgglogSemantics.Spec.Congruence
import EgglogSemantics.Proofs.Database

namespace Egglog

namespace StoredCongList
variable {db : Database}

/-- Pointwise self-congruence. There is no reflexivity rule, so this is exactly the
hypothesis that the database holds every element: membership in `terms` *is* the
self-congruence the `cons` wants. -/
theorem refl {as : List Term} (h : ∀ a ∈ as, a ∈ db.terms) : StoredCongList db as as := by
  induction as with
  | nil => exact .nil
  | cons a as ih => exact .cons (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

end StoredCongList

mutual

/-- Adding equalities only adds derivations. `StoredCong` reads `eqs` and nothing else, so
`Contained`'s one clause is the whole hypothesis. -/
theorem StoredCong.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {a b : Term}
    (hc : StoredCong d₁ a b) : StoredCong d₂ a b := by
  match hc with
  | .direct hm => exact .direct (h.eqs hm)
  | .subterm hc hs => exact .subterm (StoredCong.mono h hc) hs
  | .symm hc => exact .symm (StoredCong.mono h hc)
  | .trans h₁ h₂ => exact .trans (StoredCong.mono h h₁) (StoredCong.mono h h₂)
  | .congr hm₁ hm₂ hl =>
    exact .congr (StoredCong.mono h hm₁) (StoredCong.mono h hm₂) (StoredCongList.mono h hl)

theorem StoredCongList.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {as bs : List Term}
    (hc : StoredCongList d₁ as bs) : StoredCongList d₂ as bs := by
  match hc with
  | .nil => exact .nil
  | .cons hc hl => exact .cons (StoredCong.mono h hc) (StoredCongList.mono h hl)

end

mutual

/-- Derivable assertions suffice to transport a congruence derivation. -/
theorem StoredCong.of_assertions {d e : Database}
    (h : ∀ p ∈ d.eqs, StoredCong e p.1 p.2) {a b : Term}
    (hc : StoredCong d a b) : StoredCong e a b := by
  match hc with
  | .direct hp => exact h _ hp
  | .subterm ht hs => exact .subterm (StoredCong.of_assertions h ht) hs
  | .symm hc => exact .symm (StoredCong.of_assertions h hc)
  | .trans hl hr => exact .trans (StoredCong.of_assertions h hl) (StoredCong.of_assertions h hr)
  | .congr hl hr hs =>
    exact .congr (StoredCong.of_assertions h hl)
      (StoredCong.of_assertions h hr) (StoredCongList.of_assertions h hs)

theorem StoredCongList.of_assertions {d e : Database}
    (h : ∀ p ∈ d.eqs, StoredCong e p.1 p.2) {as bs : List Term}
    (hc : StoredCongList d as bs) : StoredCongList e as bs := by
  match hc with
  | .nil => exact .nil
  | .cons ht hs => exact .cons (StoredCong.of_assertions h ht) (StoredCongList.of_assertions h hs)

end

/-- The terms come along. `Contained` is stated on `eqs` alone, and this is the clause it
used to carry: a term is present when it is self-equal, and that derivation transports. -/
theorem Database.Contained.terms {d₁ d₂ : Database} (h : d₁.Contained d₂) :
    d₁.terms ⊆ d₂.terms := fun _ ht => (StoredCong.mono h (Database.toStored ht)).toHeld

/-- Every term a derivation mentions is one the database holds, so `StoredCong db` is an
equivalence relation on `db.terms` and relates nothing outside it. Free now that existence
is itself an equation. -/
theorem StoredCong.mem_of {db : Database} {a b : Term} (hc : StoredCong db a b) :
    a ∈ db.terms ∧ b ∈ db.terms := eqsInTerms_free hc

mutual

/-- The least relation closed under assertions, subterm existence, and congruence. -/
theorem StoredCong.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hcongr : ∀ f as bs, Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms →
      List.Forall₂ R as bs → R (.app f as) (.app f bs))
    (hsubterm : ∀ t s, R t t → s ∈ t.subterms → R s s)
    {a b : Term} (h : StoredCong db a b) : R a b := by
  match h with
  | .direct hm => exact hassert _ _ hm
  | .subterm ht hs =>
    exact hsubterm _ _
      (StoredCong.le hassert hsymm htrans hcongr hsubterm ht) hs
  | .symm h => exact hsymm _ _ (StoredCong.le hassert hsymm htrans hcongr hsubterm h)
  | .trans h₁ h₂ =>
    exact htrans _ _ _ (StoredCong.le hassert hsymm htrans hcongr hsubterm h₁)
      (StoredCong.le hassert hsymm htrans hcongr hsubterm h₂)
  | .congr hm₁ hm₂ hl =>
    exact hcongr _ _ _ hm₁ hm₂ (StoredCongList.le hassert hsymm htrans hcongr hsubterm hl)

theorem StoredCongList.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hcongr : ∀ f as bs, Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms →
      List.Forall₂ R as bs → R (.app f as) (.app f bs))
    (hsubterm : ∀ t s, R t t → s ∈ t.subterms → R s s)
    {as bs : List Term} (h : StoredCongList db as bs) : List.Forall₂ R as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (StoredCong.le hassert hsymm htrans hcongr hsubterm hab)
      (StoredCongList.le hassert hsymm htrans hcongr hsubterm hl)

end

/-! ### A literal's class is a singleton

`Database.LitsIsolated` constrains the *asserted* equations. That the derived ones are
constrained too is one induction: `congr` relates applications, so it cannot reach a
literal at all, and `symm`/`trans` carry the literal along. `evalAction`'s `union` check is
what establishes the hypothesis. -/

/-- **A literal is congruent to nothing but itself.** -/
theorem StoredCong.eq_of_isLit {db : Database} (hl : db.LitsIsolated) {a b : Term}
    (hc : StoredCong db a b) : a.isLit ∨ b.isLit → a = b := by
  induction hc using StoredCong.rec (motive_2 := fun _ _ _ => True) with
  | direct hab => exact hl _ hab
  | subterm => exact fun _ => rfl
  | symm _ ih => exact fun h => (ih h.symm).symm
  | trans _ _ ih₁ ih₂ =>
    rintro (h | h)
    · have h₁ := ih₁ (Or.inl h)
      rw [h₁] at h
      exact h₁.trans (ih₂ (Or.inl h))
    · have h₂ := ih₂ (Or.inr h)
      rw [← h₂] at h
      exact (ih₁ (Or.inr h)).trans h₂
  | congr => simp [Term.isLit]
  | nil => trivial
  | cons => trivial

namespace StoredCong
variable {db : Database}

theorem mem_left {a b : Term} (hc : StoredCong db a b) : a ∈ db.terms := hc.mem_of.1

theorem mem_right {a b : Term} (hc : StoredCong db a b) : b ∈ db.terms := hc.mem_of.2

end StoredCong

end Egglog
