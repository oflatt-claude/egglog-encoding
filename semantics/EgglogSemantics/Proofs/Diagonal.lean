import EgglogSemantics.Proofs.Out

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
  rintro p (rfl | hp)
  · rfl
  · exact h p hp

theorem Diag.addTerms {db : Database} (h : db.Diag) (ts : List Term) :
    (db.addTerms ts).Diag := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

/-- `withOperands` posits its operands reflexively, so it cannot break diagonality. -/
theorem Diag.withOperands {db : Database} (h : db.Diag) (ts : List Term) :
    (db.withOperands ts).Diag := h.addTerms ts

theorem Diag.eraseEntry {db : Database} (h : db.Diag) (row : Entry) :
    (db.eraseEntry row).Diag := by
  rintro p (hp | ⟨t, _, rfl⟩)
  · exact h p hp.1
  · rfl

theorem Diag.putEntry {db : Database} (h : db.Diag) (row : Entry) :
    (db.putEntry row).Diag := h.addTerm row.atom

end Database

/-- **On a diagonal state congruence is equality.** No equation relates two distinct terms,
so `direct` cannot and neither can `congr`, whose arguments are equal by the pointwise
hypothesis. -/
theorem StoredCong.eq_of_diag {E : Database} (h : E.Diag) :
    ∀ {a b : Term}, StoredCong E a b → a = b := by
  intro a b hc
  induction hc using StoredCong.rec (motive_2 := fun as bs _ => as = bs) with
  | direct hab => exact h _ hab
  | subterm => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ _ _ ihl => exact congrArg _ ihl
  | nil => rfl
  | cons _ _ ih ihl => exact congrArg₂ List.cons ih ihl

/-- Semantic congruence also reduces to equality on a diagonal store. -/
theorem Cong.eq_of_diag {d : Database} (hd : d.Diag) {a b : Term}
    (h : Cong d a b) : a = b := by
  induction h using Cong.rec (motive_2 := fun as bs _ => as = bs) with
  | direct hp => exact hd _ hp
  | subterm => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ ih => exact congrArg _ ih
  | nil => rfl
  | cons _ _ ih ihs => exact congrArg₂ List.cons ih ihs

theorem CongList.eq_of_diag {d : Database} (hd : d.Diag) {as bs : List Term}
    (h : CongList d as bs) : as = bs := by
  match h with
  | .nil => rfl
  | .cons h hs => exact congrArg₂ List.cons (h.eq_of_diag hd) (hs.eq_of_diag hd)

theorem congOn_eq_of_diag {E : Database} (h : E.Diag) {ts : List Term} {a b : Term}
    (hc : StoredCongOn E ts a b) : a = b := StoredCong.eq_of_diag (h.withOperands ts) hc

/-- Equal meaning on diagonal states implies equal held terms. -/
theorem Database.SameMeaning.terms_eq_of_diag {d e : Database} (h : d.SameMeaning e)
    (hd : d.Diag) (he : e.Diag) : d.terms = e.terms := by
  have incl {d e : Database} (he : e.Diag)
      (hi : ∀ a b, d.Infers a b → e.Infers a b) : d.terms ⊆ e.terms := by
    intro t ht
    have hc := (Database.toStored ht).mono (Database.Contained.addTerms [t, t] d)
    obtain ⟨w, hw, hc, _⟩ := hi _ _ ⟨t, ht, hc, hc⟩
    exact (congOn_eq_of_diag he hc) ▸ hw
  exact Set.Subset.antisymm
    (incl he (fun a b => (h.inferred a b).mp))
    (incl hd (fun a b => (h.inferred a b).mpr))

theorem StoredCongList.eq_of_diag {d : Database} (h : d.Diag) {as bs : List Term}
    (hc : StoredCongList d as bs) : as = bs := by
  have hpair := StoredCongList.forall₂.mp hc
  clear hc
  induction hpair with
  | nil => rfl
  | cons hc _ ih => exact congrArg₂ List.cons (StoredCong.eq_of_diag h hc) ih

theorem Database.Out.entry {d : Database} (h : d.Diag) {f : FnName} {as vs : List Term}
    (ho : d.Out f as vs) : Entry.mk f as vs ∈ d.entries := by
  obtain ⟨bs, hc, ht⟩ := ho
  exact CongList.eq_of_diag h hc ▸ ht

theorem Database.Out.term {d : Database} (h : d.Diag) {f : FnName} {as vs : List Term}
    (ho : d.Out f as vs) : Term.app f (as ++ vs) ∈ d.terms :=
  (StoredCong.direct (ho.entry h).2).toHeld

theorem Database.Out.columns {d : Database} (h : d.Diag) {f : FnName} {as vs : List Term}
    (ho : d.Out f as vs) : ∀ t ∈ as ++ vs, t ∈ d.terms := by
  intro t ht
  exact d.subtermClosed _ (ho.term h) (Term.arg_subterms ht t.self_mem_subterms)

/-- `Expr.OrderingFree`, read off an application: its arguments are. -/
theorem Expr.orderingFree_app {f : FnName} {args : List Expr}
    (h : Expr.OrderingFree (.app f args)) : Expr.OrderingFreeList args := h

/-- `Expr.OrderingFree`, read off a `min`: there is none. -/
theorem Expr.not_orderingFree_min {a b : Expr} (h : Expr.OrderingFree (.min a b)) : False := by
  simp [Expr.OrderingFree, Expr.hasMin] at h

theorem Expr.not_orderingFree_ite {lhs rhs : List Expr} {yes no : Expr}
    (h : Expr.OrderingFree (.ite lhs rhs yes no)) : False := by
  simp [Expr.OrderingFree, Expr.hasMin] at h

/-- `Expr.OrderingFreeList`, read off a cons. -/
theorem Expr.orderingFreeList_cons {e : Expr} {es : List Expr}
    (h : Expr.OrderingFreeList (e :: es)) : e.OrderingFree ∧ Expr.OrderingFreeList es := by
  simpa [Expr.OrderingFreeList, Expr.OrderingFree, Expr.hasMinList] using h

end Egglog
