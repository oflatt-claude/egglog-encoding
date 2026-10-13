import EgglogSemantics.SourceProof.Globals

namespace Egglog.SourceProof

open Conservativity

def ambient (db : Database) : Database := amb db Set.univ

theorem ambient_refl (db : Database) (t : Term) : Cong (ambient db) t t :=
  .assert (amb_refl (Set.mem_univ _))

theorem ambient_contains (db : Database) : db.Contained (ambient db) := ⟨subset_amb⟩

/-- Every subterm has a representative that actually exists in the source. -/
def Supports (db : Database) (t : Term) : Prop :=
  ∀ s ∈ t.subterms, ∃ u ∈ db.terms, Cong (ambient db) s u

structure Claim.Supported (db : Database) (c : Claim) : Prop where
  equality : c.Holds (ambient db)
  lhs : Supports db c.lhs
  rhs : Supports db c.rhs

theorem supports_of_mem {db : Database} (hw : db.WF) {t : Term} (ht : t ∈ db.terms) :
    Supports db t := fun s hs =>
  ⟨s, hw.subtermClosed t ht hs, ambient_refl db s⟩

theorem Claim.Holds.supported {db : Database} (hw : db.WF) {c : Claim}
    (h : c.Holds db) : c.Supported db :=
  ⟨h.mono (ambient_contains db), supports_of_mem hw (eqsInTerms_free h).1,
    supports_of_mem hw (eqsInTerms_free h).2⟩

theorem Claim.Supported.holds {db : Database} (hw : db.WF) {c : Claim}
    (h : c.Supported db) (hl : c.lhs ∈ db.terms) (hr : c.rhs ∈ db.terms) : c.Holds db :=
  conservative hw.subtermClosed (fun _ hp => mem_amb_eqs hp) hl hr h.equality

theorem Claim.Supported.symm {db : Database} {a b : Term}
    (h : Claim.Supported db ⟨a, b⟩) : Claim.Supported db ⟨b, a⟩ :=
  ⟨h.equality.symm, h.rhs, h.lhs⟩

theorem Claim.Supported.trans {db : Database} {a b c : Term}
    (h₁ : Claim.Supported db ⟨a, b⟩) (h₂ : Claim.Supported db ⟨b, c⟩) :
    Claim.Supported db ⟨a, c⟩ := ⟨h₁.equality.trans h₂.equality, h₁.lhs, h₂.rhs⟩

private theorem congrList_set {db : Database} {as : List Term} {i : Nat} {x y : Term}
    (hi : as[i]? = some x) (hxy : Cong (ambient db) x y) :
    CongList (ambient db) as (as.set i y) := by
  induction as generalizing i with
  | nil => simp at hi
  | cons a as ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst a
          exact .cons hxy (CongList.refl fun t _ => ambient_refl db t)
      | succ i => exact .cons (ambient_refl db a) (ih hi)

private theorem mem_set_cases {as : List Term} {i : Nat} {y t : Term}
    (ht : t ∈ as.set i y) : t = y ∨ t ∈ as := by
  induction as generalizing i with
  | nil => simp at ht
  | cons a as ih =>
      cases i with
      | zero =>
          rcases List.mem_cons.mp ht with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      | succ i =>
          rcases List.mem_cons.mp ht with h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · exact (ih h).imp_right (List.mem_cons_of_mem _)

/-- The base proof supplies existence of the enclosing application. -/
theorem Claim.Supported.congr {db : Database} {a x y : Term} {f : FnName}
    {as : List Term} {i : Nat} (base : Claim.Supported db ⟨a, .app f as⟩)
    (child : Claim.Supported db ⟨x, y⟩) (hi : as[i]? = some x) :
    Claim.Supported db ⟨a, .app f (as.set i y)⟩ := by
  have hc : Cong (ambient db) (.app f as) (.app f (as.set i y)) :=
    .congr (ambient_refl db _) (ambient_refl db _) (congrList_set hi child.equality)
  refine ⟨base.equality.trans hc, base.lhs, ?_⟩
  intro s hs
  cases hs with
  | refl =>
      obtain ⟨u, hu, hcu⟩ := base.rhs _ (Term.self_mem_subterms _)
      exact ⟨u, hu, hc.symm.trans hcu⟩
  | @arg t _ _ ht hst =>
      rcases mem_set_cases ht with rfl | ht
      · exact child.rhs s hst
      · exact base.rhs s (.arg ht hst)

theorem Claim.Supported.of_recorded {A db : Database} (hr : A.Recorded db)
    (hA : A.WF) (hw : db.WF) {c : Claim} (hc : c.Holds A) : c.Supported db := by
  have hmono : ∀ {ts : List Term} {x y : Term}, CongOn db ts x y →
      Cong (ambient db) x y := fun h =>
    Cong.mono ⟨withOperands_subset_amb (fun _ _ _ _ => Set.mem_univ _)⟩ h
  refine ⟨hmono (Cong.mono_recorded hr hA hw hc), ?_, ?_⟩
  · intro s hs
    obtain ⟨u, hu, hsu⟩ := terms_clause hr hA
      (hA.subtermClosed _ (eqsInTerms_free hc).1 hs)
    exact ⟨u, hu, hmono hsu⟩
  · intro s hs
    obtain ⟨u, hu, hsu⟩ := terms_clause hr hA
      (hA.subtermClosed _ (eqsInTerms_free hc).2 hs)
    exact ⟨u, hu, hmono hsu⟩

end Egglog.SourceProof
