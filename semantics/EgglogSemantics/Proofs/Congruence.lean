import EgglogSemantics.Spec.Congruence
import EgglogSemantics.Proofs.Database

namespace Egglog
/-- **Every equation `d₁` records `d₂` records up to congruence.** The witness `q` is one
of `d₂`'s own equations, or the clause says nothing: `withOperands` alone makes `p` hold. -/
structure Database.Recorded (d₁ d₂ : Database) : Prop where
  eqs : ∀ p ∈ d₁.eqs, ∃ q ∈ d₂.eqs,
    CongOn d₂ [p.1, p.2] p.1 q.1 ∧ CongOn d₂ [p.1, p.2] p.2 q.2

/-- `CongList` is `List.Forall₂ (Cong db)`. Recursion over a mutual inductive has
to go through `match`; the `induction` tactic does not support it. -/
theorem CongList.toForall₂ {db : Database} {as bs : List Term} (h : CongList db as bs) :
    List.Forall₂ (Cong db) as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons hab (CongList.toForall₂ hl)

theorem CongList.ofForall₂ {db : Database} {as bs : List Term}
    (h : List.Forall₂ (Cong db) as bs) : CongList db as bs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

namespace CongList
variable {db : Database}

theorem forall₂ {as bs : List Term} : CongList db as bs ↔ List.Forall₂ (Cong db) as bs :=
  ⟨toForall₂, ofForall₂⟩

theorem length_eq {as bs : List Term} (h : CongList db as bs) : as.length = bs.length :=
  h.toForall₂.length_eq

/-- Pointwise self-congruence. There is no reflexivity rule, so this is exactly the
hypothesis that the database holds every element: membership in `terms` *is* the
self-congruence the `cons` wants. -/
theorem refl {as : List Term} (h : ∀ a ∈ as, a ∈ db.terms) : CongList db as as := by
  induction as with
  | nil => exact .nil
  | cons a as ih => exact .cons (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- Symmetry, pointwise. -/
theorem symm {as bs : List Term} (h : CongList db as bs) : CongList db bs as := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons hab.symm (CongList.symm hl)

/-- Transitivity, pointwise. -/
theorem trans {as bs cs : List Term} (h₁ : CongList db as bs) (h₂ : CongList db bs cs) :
    CongList db as cs := by
  match h₁, h₂ with
  | .nil, .nil => exact .nil
  | .cons hab hl₁, .cons hbc hl₂ => exact .cons (hab.trans hbc) (CongList.trans hl₁ hl₂)

end CongList
/-- `Cong.congr` stated over `List.Forall₂`. -/
theorem Cong.congr' {db : Database} {f : FnName} {as bs : List Term}
    (ha : Term.app f as ∈ db.terms) (hb : Term.app f bs ∈ db.terms)
    (h : List.Forall₂ (Cong db) as bs) : Cong db (.app f as) (.app f bs) :=
  .congr ha hb (CongList.forall₂.mpr h)

mutual

/-- Adding equalities only adds derivations. `Cong` reads `eqs` and nothing else, so
`Contained`'s one clause is the whole hypothesis. -/
theorem Cong.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {a b : Term}
    (hc : Cong d₁ a b) : Cong d₂ a b := by
  match hc with
  | .assert hm => exact .assert (h.eqs hm)
  | .subterm hc hs => exact .subterm (Cong.mono h hc) hs
  | .symm hc => exact .symm (Cong.mono h hc)
  | .trans h₁ h₂ => exact .trans (Cong.mono h h₁) (Cong.mono h h₂)
  | .congr hm₁ hm₂ hl =>
    exact .congr (Cong.mono h hm₁) (Cong.mono h hm₂) (CongList.mono h hl)

theorem CongList.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {as bs : List Term}
    (hc : CongList d₁ as bs) : CongList d₂ as bs := by
  match hc with
  | .nil => exact .nil
  | .cons hc hl => exact .cons (Cong.mono h hc) (CongList.mono h hl)

end

mutual

/-- Derivable assertions suffice to transport a congruence derivation. -/
theorem Cong.of_assertions {d e : Database}
    (h : ∀ p ∈ d.eqs, Cong e p.1 p.2) {a b : Term}
    (hc : Cong d a b) : Cong e a b := by
  match hc with
  | .assert hp => exact h _ hp
  | .subterm ht hs => exact .subterm (Cong.of_assertions h ht) hs
  | .symm hc => exact .symm (Cong.of_assertions h hc)
  | .trans hl hr => exact .trans (Cong.of_assertions h hl) (Cong.of_assertions h hr)
  | .congr hl hr hs =>
    exact .congr (Cong.of_assertions h hl)
      (Cong.of_assertions h hr) (CongList.of_assertions h hs)

theorem CongList.of_assertions {d e : Database}
    (h : ∀ p ∈ d.eqs, Cong e p.1 p.2) {as bs : List Term}
    (hc : CongList d as bs) : CongList e as bs := by
  match hc with
  | .nil => exact .nil
  | .cons ht hs => exact .cons (Cong.of_assertions h ht) (CongList.of_assertions h hs)

end

/-- The terms come along. `Contained` is stated on `eqs` alone, and this is the clause it
used to carry: a term is present when it is self-equal, and that derivation transports. -/
theorem Database.Contained.terms {d₁ d₂ : Database} (h : d₁.Contained d₂) :
    d₁.terms ⊆ d₂.terms := fun _ ht => Cong.mono h ht

/-- Every term a derivation mentions is one the database holds, so `Cong db` is an
equivalence relation on `db.terms` and relates nothing outside it. Free now that existence
is itself an equation. -/
theorem Cong.mem_of {db : Database} {a b : Term} (hc : Cong db a b) :
    a ∈ db.terms ∧ b ∈ db.terms := eqsInTerms_free hc

theorem CongList.mem_of {db : Database} {as bs : List Term} (hc : CongList db as bs) :
    (∀ a ∈ as, a ∈ db.terms) ∧ (∀ b ∈ bs, b ∈ db.terms) := by
  match hc with
  | .nil => exact ⟨by simp, by simp⟩
  | .cons hab hl =>
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hab.mem_of.1
      · exact (CongList.mem_of hl).1 a ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hab.mem_of.2
      · exact (CongList.mem_of hl).2 b hb

mutual

/-- The least relation closed under assertions, subterm existence, and congruence. -/
theorem Cong.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hcongr : ∀ f as bs, Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms →
      List.Forall₂ R as bs → R (.app f as) (.app f bs))
    (hsubterm : ∀ t s, R t t → s ∈ t.subterms → R s s)
    {a b : Term} (h : Cong db a b) : R a b := by
  match h with
  | .assert hm => exact hassert _ _ hm
  | .subterm ht hs =>
    exact hsubterm _ _
      (Cong.le hassert hsymm htrans hcongr hsubterm ht) hs
  | .symm h => exact hsymm _ _ (Cong.le hassert hsymm htrans hcongr hsubterm h)
  | .trans h₁ h₂ =>
    exact htrans _ _ _ (Cong.le hassert hsymm htrans hcongr hsubterm h₁)
      (Cong.le hassert hsymm htrans hcongr hsubterm h₂)
  | .congr hm₁ hm₂ hl =>
    exact hcongr _ _ _ hm₁ hm₂ (CongList.le hassert hsymm htrans hcongr hsubterm hl)

theorem CongList.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hcongr : ∀ f as bs, Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms →
      List.Forall₂ R as bs → R (.app f as) (.app f bs))
    (hsubterm : ∀ t s, R t t → s ∈ t.subterms → R s s)
    {as bs : List Term} (h : CongList db as bs) : List.Forall₂ R as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (Cong.le hassert hsymm htrans hcongr hsubterm hab)
      (CongList.le hassert hsymm htrans hcongr hsubterm hl)

end

/-- Reasserting a held term derives nothing new. -/
theorem Cong.of_addTerm {db : Database} (hw : db.WF) {t : Term} (ht : t ∈ db.terms)
    {a b : Term} (hc : Cong (db.addTerm t) a b) : Cong db a b := by
  have hmem : ∀ {s : Term}, s ∈ (db.addTerm t).terms → s ∈ db.terms := by
    intro s hs
    rcases Database.addTerm_terms ▸ hs with hs | hs
    · exact hs
    · exact hw.subtermClosed t ht hs
  refine Cong.le (R := Cong db) (fun a b hm => ?_) (fun _ _ => Cong.symm)
    (fun _ _ _ => Cong.trans) (fun _ _ _ ha hb hl => Cong.congr' (hmem ha) (hmem hb) hl)
    (fun t s ht hs => hw.subtermClosed t ht hs) hc
  rcases Set.mem_insert_iff.mp hm with heq | hm
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ht
  · exact .assert hm

/-! ### A literal's class is a singleton

`Database.LitsIsolated` constrains the *asserted* equations. That the derived ones are
constrained too is one induction: `congr` relates applications, so it cannot reach a
literal at all, and `symm`/`trans` carry the literal along. `evalAction`'s `union` check is
what establishes the hypothesis. -/

/-- **A literal is congruent to nothing but itself.** -/
theorem Cong.eq_of_isLit {db : Database} (hl : db.LitsIsolated) {a b : Term}
    (hc : Cong db a b) : a.isLit ∨ b.isLit → a = b := by
  induction hc using Cong.rec (motive_2 := fun _ _ _ => True) with
  | assert hab => exact hl _ hab
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

/-- The list form: an operand list of literals has no congruent neighbours either. -/
theorem CongList.eq_of_isLit {db : Database} (hl : db.LitsIsolated) :
    ∀ {as bs : List Term}, CongList db as bs → (∀ a ∈ as, a.isLit) → as = bs
  | _, _, .nil, _ => rfl
  | a :: _, _, .cons hab hrest, hlit => by
    rw [Cong.eq_of_isLit hl hab (Or.inl (hlit a (by simp))),
      CongList.eq_of_isLit hl hrest fun x hx => hlit x (by simp [hx])]

namespace Cong
variable {db : Database}

theorem mem_left {a b : Term} (hc : Cong db a b) : a ∈ db.terms := hc.mem_of.1

theorem mem_right {a b : Term} (hc : Cong db a b) : b ∈ db.terms := hc.mem_of.2

/-- Nothing is derivable in the empty database. -/
theorem not_of_empty {a b : Term} (hc : Cong Database.empty a b) : False := by
  simpa using hc.mem_left

/-- `Cong db` is an equivalence on the subtype of `db.terms`. This is the e-graph viewed
as a set of e-classes: the `Quotient` of this setoid is `db`'s e-classes. Reflexivity is
the subtype's own property. -/
def setoid (db : Database) : Setoid {t : Term // t ∈ db.terms} where
  r a b := Cong db a.val b.val
  iseqv := ⟨fun a => a.property, .symm, .trans⟩

end Cong
theorem Cong.isValue_iff {db : Database} (hs : db.StoreOk) {a b : Term}
    (h : Cong db a b) : a.IsValue db.sig ↔ b.IsValue db.sig := by
  induction h using Cong.rec
      (motive_2 := fun as bs _ =>
        (∀ a ∈ as, a.IsValue db.sig) ↔ ∀ b ∈ bs, b.IsValue db.sig) with
  | assert he =>
    rcases hs.typed _ he with hv | ⟨row, _, heq⟩
    · exact iff_of_true hv.1 hv.2
    · have hab := congrArg Prod.fst heq
      have hbb := congrArg Prod.snd heq
      dsimp only at hab hbb
      rw [hab, hbb]
  | subterm => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ _ _ ih => simp only [Term.isValue_app_iff, ih]
  | nil => simp
  | cons _ _ ih₁ ih₂ => simp only [List.forall_mem_cons, ih₁, ih₂]

end Egglog
