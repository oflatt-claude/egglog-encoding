import EgglogSemantics.Proofs.Step

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

/-- `withOperands` posits its operands reflexively, so it cannot break diagonality. -/
theorem Diag.withOperands {db : Database} (h : db.Diag) (ts : List Term) :
    (db.withOperands ts).Diag := h.addTerms ts

theorem Diag.consumeWrite {db : Database} (h : db.Diag) (row : Entry) :
    (db.consumeWrite row).Diag := h

theorem Diag.eraseEntry {db : Database} (h : db.Diag) (row : Entry) :
    (db.eraseEntry row).Diag := h

theorem Diag.writeEntry {db : Database} (h : db.Diag) (row : Entry) :
    (db.writeEntry row).Diag := h.addTerms row.columns

theorem Diag.putEntry {db : Database} (h : db.Diag) (row : Entry) :
    (db.putEntry row).Diag := h.addTerms row.columns

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
  · exact h.columns _ (Or.inl ht) t (List.mem_append_right _ hm)

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
