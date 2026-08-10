import EgglogSemantics.Spec.Congruence
import EgglogSemantics.Proofs.Database

namespace Egglog
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

/-- Reflexivity, pointwise. -/
theorem refl {as : List Term} (h : ∀ a ∈ as, a ∈ db.terms) : CongList db as as := by
  induction as with
  | nil => exact .nil
  | cons a as ih =>
    refine .cons (Cong.refl (h a (by simp))) (ih fun b hb => h b (by simp [hb]))

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
namespace Cong
variable {db : Database}

/-- `Cong.congr` stated over `List.Forall₂`. -/
theorem congr' {f : FnName} {as bs : List Term} (ha : Term.app f as ∈ db.terms)
    (hb : Term.app f bs ∈ db.terms) (h : List.Forall₂ (Cong db) as bs) :
    Cong db (.app f as) (.app f bs) :=
  .congr ha hb (CongList.forall₂.mpr h)

/-- **For a constructor, the table's functional dependency is derivable congruence.** Two
rows of one constructor whose keys are congruent have congruent outputs, column by column
— `Spec/Merge.lean`'s `MCong.fd`, here as a *result* about `Cong` rather than a
constructor of a second relation. The M9 insight, in the direction that costs nothing.

The only hypothesis is the **shape of the constructor rows**: wherever `db` records a row
of a constructor, its output column is the application itself and that application is a
term `db` holds. Nothing else — no `Database.CtorRows`, no `Database.RowsComplete`, no
`Database.CtorTerms`, so this is strictly less than `mcong_iff_cong` needs. It is
`Proofs/Merge.lean`'s `FDatabase.Inv.ctorRows` with its guard weakened from
`mergeOf r.fn = none` to `IsCtor r.fn`, which is the clause that survives a `:merge`
declaration of some other name; it is spelled out rather than named because its three
siblings live in `Spec/Database.lean` and a fourth one here would split the family.

`Cong.congr` is the case `as = bs`; `Cong.refl` on an application is the case where the
two rows are one. -/
theorem fd {f : FnName} {as bs a b : List Term} {x y : Term}
    (hrow : ∀ r ∈ db.rows, db.sig.IsCtor r.fn →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    (hra : Row.mk f as a ∈ db.rows) (hrb : Row.mk f bs b ∈ db.rows)
    (hu : db.sig.IsCtor f) (hl : CongList db as bs) (hxy : (x, y) ∈ a.zip b) :
    Cong db x y := by
  obtain ⟨rfl, hma⟩ : a = [Term.app f as] ∧ Term.app f as ∈ db.terms := hrow _ hra hu
  obtain ⟨rfl, hmb⟩ : b = [Term.app f bs] ∧ Term.app f bs ∈ db.terms := hrow _ hrb hu
  simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  exact .congr hma hmb hl

end Cong
mutual

/-- Adding terms and equalities only adds derivations. -/
theorem Cong.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {a b : Term}
    (hc : Cong d₁ a b) : Cong d₂ a b := by
  match hc with
  | .assert hm => exact .assert (h.eqs hm)
  | .refl hm => exact .refl (h.terms hm)
  | .symm hc => exact .symm (Cong.mono h hc)
  | .trans h₁ h₂ => exact .trans (Cong.mono h h₁) (Cong.mono h h₂)
  | .congr hm₁ hm₂ hl => exact .congr (h.terms hm₁) (h.terms hm₂) (CongList.mono h hl)

theorem CongList.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {as bs : List Term}
    (hc : CongList d₁ as bs) : CongList d₂ as bs := by
  match hc with
  | .nil => exact .nil
  | .cons hc hl => exact .cons (Cong.mono h hc) (CongList.mono h hl)

end

mutual

/-- Every term a derivation mentions is in the database, so `Cong db` is an
equivalence relation on `db.terms` and relates nothing outside it. -/
theorem Cong.mem_of {db : Database} (hw : db.WF) {a b : Term} (hc : Cong db a b) :
    a ∈ db.terms ∧ b ∈ db.terms := by
  match hc with
  | .assert hm => exact hw.eqsInTerms _ hm
  | .refl hm => exact ⟨hm, hm⟩
  | .symm hc => exact (Cong.mem_of hw hc).symm
  | .trans h₁ h₂ => exact ⟨(Cong.mem_of hw h₁).1, (Cong.mem_of hw h₂).2⟩
  | .congr hm₁ hm₂ _ => exact ⟨hm₁, hm₂⟩

theorem CongList.mem_of {db : Database} (hw : db.WF) {as bs : List Term}
    (hc : CongList db as bs) :
    (∀ a ∈ as, a ∈ db.terms) ∧ (∀ b ∈ bs, b ∈ db.terms) := by
  match hc with
  | .nil => exact ⟨by simp, by simp⟩
  | .cons hab hl =>
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact (Cong.mem_of hw hab).1
      · exact (CongList.mem_of hw hl).1 a ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact (Cong.mem_of hw hab).2
      · exact (CongList.mem_of hw hl).2 b hb

end

mutual

/-- `Cong db` is the *least* congruence on `db`'s terms containing its asserted
equalities: any relation with the same closure properties contains it.

This is `Cong.rec` packaged usefully. It is how negative facts about the closure get
proved — exhibit such a relation that the pair is not in — and it is the shape the
proof-checker soundness argument will take, since a proof term denotes exactly one
of these derivations. -/
theorem Cong.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hcongr : ∀ f as bs, Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms →
      List.Forall₂ R as bs → R (.app f as) (.app f bs))
    {a b : Term} (h : Cong db a b) : R a b := by
  match h with
  | .assert hm => exact hassert _ _ hm
  | .refl hm => exact hrefl _ hm
  | .symm h => exact hsymm _ _ (Cong.le hassert hrefl hsymm htrans hcongr h)
  | .trans h₁ h₂ =>
    exact htrans _ _ _ (Cong.le hassert hrefl hsymm htrans hcongr h₁)
      (Cong.le hassert hrefl hsymm htrans hcongr h₂)
  | .congr hm₁ hm₂ hl =>
    exact hcongr _ _ _ hm₁ hm₂ (CongList.le hassert hrefl hsymm htrans hcongr hl)

theorem CongList.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hcongr : ∀ f as bs, Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms →
      List.Forall₂ R as bs → R (.app f as) (.app f bs))
    {as bs : List Term} (h : CongList db as bs) : List.Forall₂ R as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (Cong.le hassert hrefl hsymm htrans hcongr hab)
      (CongList.le hassert hrefl hsymm htrans hcongr hl)

end

namespace Cong
variable {db : Database}

theorem mem_left {a b : Term} (hw : db.WF) (hc : Cong db a b) : a ∈ db.terms :=
  (hc.mem_of hw).1

theorem mem_right {a b : Term} (hw : db.WF) (hc : Cong db a b) : b ∈ db.terms :=
  (hc.mem_of hw).2

/-- Nothing is derivable in the empty database. -/
theorem not_of_empty {a b : Term} (hc : Cong Database.empty a b) : False :=
  (hc.mem_left Database.WF.empty).elim

/-- `Cong db` is an equivalence on the subtype of `db.terms`. This is the e-graph viewed
as a set of e-classes: the `Quotient` of this setoid is `db`'s e-classes. -/
def setoid (db : Database) : Setoid {t : Term // t ∈ db.terms} where
  r a b := Cong db a.val b.val
  iseqv := ⟨fun a => .refl a.property, .symm, .trans⟩

end Cong
end Egglog
