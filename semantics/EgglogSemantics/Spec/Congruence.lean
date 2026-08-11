import Mathlib.Data.List.Forall2
import EgglogSemantics.Spec.Database

/-!
# Congruence

`Cong db a b` says `a = b` is derivable in `db`. The closure is an **inductive
predicate**, not a set of pairs the state carries and repairs to a fixpoint: the only
place congruence is consulted is e-matching's side conditions (`ValidSubst`), which ask
for a derivation directly.

Subterm closure is not a rule here. It changes the term set rather than the relation, and
is `Database.WF.subtermClosed`.
-/

namespace Egglog
mutual

/-- The congruence closure of `db`'s asserted equalities.

A **partial equivalence relation**: symmetric and transitive, but reflexive only on
`db.terms`. A term does not exist by default — something has to build it — which is why
`refl` carries a hypothesis, and why `Cong db a a` says that `a` is present
(`Proofs/Congruence.lean`'s `Cong.mem_of`). -/
inductive Cong (db : Database) : Term → Term → Prop where
  | assert {a b : Term} : (a, b) ∈ db.eqs → Cong db a b
  | refl {a : Term} : a ∈ db.terms → Cong db a a
  | symm {a b : Term} : Cong db a b → Cong db b a
  | trans {a b c : Term} : Cong db a b → Cong db b c → Cong db a c
  | congr {f : FnName} {as bs : List Term} :
      Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms → CongList db as bs →
      Cong db (.app f as) (.app f bs)

/-- Pointwise `Cong` over argument lists. `List.Forall₂ (Cong db)` would say the same
thing, but passing `Cong db` as a parameter of another inductive is not a legal recursive
occurrence, so the two are declared mutually and `CongList.forall₂` bridges them. -/
inductive CongList (db : Database) : List Term → List Term → Prop where
  | nil : CongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      Cong db a b → CongList db as bs → CongList db (a :: as) (b :: bs)

end

end Egglog
