import Mathlib.Data.List.Forall2
import EgglogSemantics.Spec.Database

/-!
# Congruence

`Cong db a b` says `a = b` is derivable in `db`: an **inductive predicate**, not a set of
pairs the state carries. Subterm closure is not a rule here but `Database.WF.subtermClosed`.
-/

namespace Egglog
mutual

/-- The congruence closure of `db`'s asserted equalities. A **partial equivalence
relation**: symmetric and transitive, but reflexive only on `db.terms`, since a term does
not exist by default. `Cong db a a` therefore says `a` is present. -/
inductive Cong (db : Database) : Term → Term → Prop where
  | assert {a b : Term} : (a, b) ∈ db.eqs → Cong db a b
  | refl {a : Term} : a ∈ db.terms → Cong db a a
  | symm {a b : Term} : Cong db a b → Cong db b a
  | trans {a b c : Term} : Cong db a b → Cong db b c → Cong db a c
  | congr {f : FnName} {as bs : List Term} :
      Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms → CongList db as bs →
      Cong db (.app f as) (.app f bs)

/-- Pointwise `Cong` over argument lists; `CongList.forall₂` bridges it to
`List.Forall₂ (Cong db)`. -/
inductive CongList (db : Database) : List Term → List Term → Prop where
  | nil : CongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      Cong db a b → CongList db as bs → CongList db (a :: as) (b :: bs)

end

/-! ### Congruence with extra terms in scope -/
/-- `db` plus the terms `ts`, used to relate a term the database may not hold — a pattern
instance, say — to one it does. It **asserts nothing**. -/
def Database.withOperands (db : Database) (ts : List Term) : Database := db.addTerms ts

@[inherit_doc Database.withOperands] def CongOn
    (db : Database) (ts : List Term) (a b : Term) : Prop := Cong (db.withOperands ts) a b

end Egglog
