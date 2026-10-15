import EgglogSemantics.Spec.Step
import EgglogSemantics.Proofs.Match

/-! Structural equality in mathematical union-free states, and syntax inversion for
ordering-free source expressions. No executable state is involved. -/

namespace Egglog

/-- Every asserted equation is reflexive. -/
def Database.Diag (db : Database) : Prop := ∀ p ∈ db.eqs, p.1 = p.2

/-- A state whose merge bodies and rule heads assert nothing either. The three fields are
what the three phases read: `diag` is the state, `sig` is what a `MergeStep` runs, `rules`
is what a `RunRules` runs. -/
structure Database.NoUnions (db : Database) : Prop where
  diag : db.Diag
  sig : Signature.UnionFree db.sig
  rules : ∀ r ∈ db.rules, Actions.UnionFree r.actions

namespace Database

/-- A subset of a diagonal is diagonal. -/
theorem Diag.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hd : d₂.Diag) : d₁.Diag :=
  fun p hp => hd p (h.eqs hp)

theorem Diag.addTerm {db : Database} (h : db.Diag) (t : Term) : (db.addTerm t).Diag := by
  rintro p (hp | ⟨s, -, rfl⟩)
  · exact h p hp
  · rfl

theorem Diag.addTerms {db : Database} (h : db.Diag) (ts : List Term) :
    (db.addTerms ts).Diag := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem Diag.eqsRefl {db : Database} (h : db.Diag) {t : Term}
    (ht : t ∈ db.terms) : (t, t) ∈ db.eqs := by
  obtain ⟨u, hp | hp⟩ := mem_terms_iff.mp ht
  · have he : t = u := h _ hp
    exact he ▸ hp
  · have he : u = t := h _ hp
    exact he ▸ hp

/-- `withOperands` posits its operands reflexively, so it cannot break diagonality. -/
theorem Diag.withOperands {db : Database} (h : db.Diag) (ts : List Term) :
    (db.withOperands ts).Diag := h.addTerms ts

theorem Diag.eraseEntry {db : Database} (h : db.Diag) (row : Entry) :
    (db.eraseEntry row).Diag := fun p hp => h p hp.1

theorem Diag.putEntry {db : Database} (h : db.Diag) (row : Entry) :
    (db.putEntry row).Diag := h.addTerm row.atom

end Database

/-- **On a diagonal state congruence is equality.** No equation relates two distinct terms,
so `assert` cannot and neither can `congr`, whose arguments are equal by the pointwise
hypothesis. -/
theorem Cong.eq_of_diag {E : Database} (h : E.Diag) : ∀ {a b : Term}, Cong E a b → a = b := by
  intro a b hc
  induction hc using Cong.rec (motive_2 := fun as bs _ => as = bs) with
  | assert hab => exact h _ hab
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ _ _ ihl => exact congrArg _ ihl
  | nil => rfl
  | cons _ _ ih ihl => exact congrArg₂ List.cons ih ihl

theorem congOn_eq_of_diag {E : Database} (h : E.Diag) {ts : List Term} {a b : Term}
    (hc : CongOn E ts a b) : a = b := Cong.eq_of_diag (h.withOperands ts) hc

/-- On diagonal states, inferred-state comparison is exact state comparison. -/
theorem Database.SameMeaning.eq_of_diag {d e : Database} (h : d.SameMeaning e)
    (hd : d.Diag) (he : e.Diag) : d = e := by
  have incl {d e : Database} (hd : d.Diag) (he : e.Diag)
      (hi : ∀ a b, d.Infers a b → e.Infers a b) : d.eqs ⊆ e.eqs := by
    intro p hp
    have ht : p.1 ∈ d.terms := (Cong.assert hp).mem_left
    have hcon := ht.mono (Database.Contained.addTerms [p.1, p.1] d)
    obtain ⟨w, hw, hc, _⟩ := hi _ _ ⟨p.1, ht, hcon, hcon⟩
    have hr := he.eqsRefl ((congOn_eq_of_diag he hc) ▸ hw)
    change (p.1, p.2) ∈ e.eqs
    rw [← hd p hp]
    exact hr
  apply Database.ext h.sig _ h.env h.rules
  exact Set.Subset.antisymm
    (incl hd he (fun a b => (h.inferred a b).mp))
    (incl he hd (fun a b => (h.inferred a b).mpr))

theorem CongList.eq_of_diag {d : Database} (h : d.Diag) {as bs : List Term}
    (hc : CongList d as bs) : as = bs := by
  have hpair := CongList.forall₂.mp hc
  clear hc
  induction hpair with
  | nil => rfl
  | cons hc _ ih => exact congrArg₂ List.cons (Cong.eq_of_diag h hc) ih

theorem Database.Out.entry {d : Database} (h : d.Diag) {f : FnName} {as vs : List Term}
    (ho : d.Out f as vs) : Entry.mk f as vs ∈ d.entries := by
  obtain ⟨bs, hc, ht⟩ := ho
  exact CongList.eq_of_diag h hc ▸ ht

theorem Database.Out.columns {d : Database} (h : d.StoreOk) {f : FnName} {as vs : List Term}
    (ho : d.Out f as vs) : ∀ t ∈ as ++ vs, t ∈ d.terms := by
  obtain ⟨bs, hc, ht⟩ := ho
  intro t hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨b, _, hb⟩ := (CongList.forall₂.mp hc).flip.exists_left hm
    exact hb.mem_left
  · exact h.columns _ ht t (List.mem_append_right _ hm)

/-- `Expr.OrderingFree`, read off an application: its arguments are. -/
theorem Expr.orderingFree_app {f : FnName} {args : List Expr}
    (h : Expr.OrderingFree (.app f args)) : Expr.OrderingFreeList args := h

/-- `Expr.OrderingFree`, read off a `min`: there is none. -/
theorem Expr.not_orderingFree_min {a b : Expr} (h : Expr.OrderingFree (.min a b)) : False := by
  simp [Expr.OrderingFree, Expr.hasMin] at h

/-- `Expr.OrderingFreeList`, read off a cons. -/
theorem Expr.orderingFreeList_cons {e : Expr} {es : List Expr}
    (h : Expr.OrderingFreeList (e :: es)) : e.OrderingFree ∧ Expr.OrderingFreeList es := by
  simpa [Expr.OrderingFreeList, Expr.OrderingFree, Expr.hasMinList] using h

end Egglog
