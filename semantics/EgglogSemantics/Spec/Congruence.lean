import Mathlib.Data.List.Forall2
import EgglogSemantics.Spec.Database

/-!
# Congruence

`Cong db a b` says `a = b` is derivable in `db`. The closure is an **inductive
predicate**, not a set of pairs the state carries and repairs to a fixpoint: nothing
in the semantics needs that set, since the only place congruence is consulted is
e-matching's side conditions (`MValidSubst`), which ask for a derivation directly.
Deriving an
equality rather than computing one is also what makes a proof term an induction —
`PLAN.md`, "What a proof value is".

Subterm closure is not a rule here. It changes the term set rather than the relation,
and is `Database.WF.subtermClosed`.

Reflexivity is restricted to terms the database holds: an e-graph knows nothing about
a term it does not contain, and that restriction is what makes the witness condition
in e-matching bite.
-/

namespace Egglog
mutual

/-- The congruence closure of `db`'s asserted equalities. -/
inductive Cong (db : Database) : Term → Term → Prop where
  | assert {a b : Term} : (a, b) ∈ db.eqs → Cong db a b
  | refl {a : Term} : a ∈ db.terms → Cong db a a
  | symm {a b : Term} : Cong db a b → Cong db b a
  | trans {a b c : Term} : Cong db a b → Cong db b c → Cong db a c
  | congr {f : FnName} {as bs : List Term} :
      Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms → CongList db as bs →
      Cong db (.app f as) (.app f bs)

/-- Pointwise `Cong` over argument lists.

Companion of `Cong.congr`. `List.Forall₂ (Cong db)` would say the same thing, but
passing `Cong db` as a parameter of another inductive is not a legal recursive
occurrence, so the two are declared mutually and `CongList.forall₂` bridges them. -/
inductive CongList (db : Database) : List Term → List Term → Prop where
  | nil : CongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      Cong db a b → CongList db as bs → CongList db (a :: as) (b :: bs)

end

/-- `a = b` holds in `db` once both terms are built.

`Cong`'s `refl` and `congr` are restricted to `db.terms`, so a pair the database does not
hold cannot be related at all. Adding the two first is what `Spec/Merge.lean`'s
`Database.withOperands` does for a pattern's operands, and adding a term asserts nothing,
so this is a conservative reading of `Cong` rather than a weaker relation. On
`a b ∈ db.terms` under `Database.WF` the two coincide. The added terms are the *related*
ones, which is why this needs no separate operand list as `MCongOn` does.

M11 needs it on the encoded side,
whose rebuild re-keys view rows to applications the source never built
(`Encoding/Encode.lean`). -/
def CongOn (db : Database) (a b : Term) : Prop :=
  Cong ((db.addTerm a).addTerm b) a b

end Egglog
