import Mathlib.Data.List.Forall2
import EgglogSemantics.Spec.Database

/-!
# Congruence

`Cong db a b` says `a = b` is derivable in `db`: an **inductive predicate** over the
asserted equalities, not a set of pairs the state carries.
-/

namespace Egglog
mutual

/-- The congruence closure of `db`'s asserted equalities. A **partial equivalence
relation**: symmetric and transitive, but reflexive only where an equation makes it so. -/
inductive Cong (db : Database) : Term → Term → Prop where
  | assert {a b : Term} : (a, b) ∈ db.eqs → Cong db a b
  | subterm {t s : Term} : Cong db t t → s ∈ t.subterms → Cong db s s
  | symm {a b : Term} : Cong db a b → Cong db b a
  | trans {a b c : Term} : Cong db a b → Cong db b c → Cong db a c
  | congr {f : FnName} {as bs : List Term} :
      Cong db (.app f as) (.app f as) → Cong db (.app f bs) (.app f bs) →
      CongList db as bs → Cong db (.app f as) (.app f bs)

/-- Pointwise `Cong` over argument lists. -/
inductive CongList (db : Database) : List Term → List Term → Prop where
  | nil : CongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      Cong db a b → CongList db as bs → CongList db (a :: as) (b :: bs)

end

/-- The terms `db` holds: a term is present exactly when it is self-equal. -/
def Database.terms (db : Database) : Set Term := {t | Cong db t t}

/-- Bindings range over held values, excluding row atoms. -/
def Database.values (db : Database) : Set Term :=
  {t | t ∈ db.terms ∧ t.IsValue db.sig}

/-- Every application the database holds is a **declared** function's entry: its head is
declared, and it carries that declaration's `entryWidth` children. -/
def Database.DeclaredTerms (db : Database) : Prop :=
  ∀ f as, Term.app f as ∈ db.terms → ∃ d, db.sig f = some d ∧ as.length = d.entryWidth

/-- Function rows name declared functions and contain existing values.
This store invariant is separate from the equation and environment invariant `WF`. -/
structure Database.StoreOk (db : Database) : Prop where
  declared : ∀ row ∈ db.entries,
    ∃ decl, db.sig row.name = some decl ∧ decl.merge ≠ none
  columns : ∀ row ∈ db.entries, ∀ t ∈ row.columns, t ∈ db.terms
  typed : ∀ p ∈ db.eqs,
    (p.1.IsValue db.sig ∧ p.2.IsValue db.sig) ∨
      ∃ row : Entry, row.Valid db.sig ∧ p = (row.atom, row.atom)
  envValues : ∀ b ∈ db.env, b.2.IsValue db.sig

/-- No asserted equation puts a literal beside anything but itself: `evalAction` refuses a
`union` on a literal and `addTerm` writes only reflexive pairs. `Cong.eq_of_isLit` reads it
back as "a literal's class is a singleton", which is what makes `min` on literals stable. -/
def Database.LitsIsolated (db : Database) : Prop :=
  ∀ p ∈ db.eqs, p.1.isLit ∨ p.2.isLit → p.1 = p.2

/-- Environment bindings exist, and literals have singleton equivalence classes. -/
structure Database.WF (db : Database) : Prop where
  envInTerms : ∀ b ∈ db.env, b.2 ∈ db.terms
  litsIsolated : db.LitsIsolated

/-- `db` plus the terms `ts`, used to relate a term the database may not hold — a pattern
instance, say — to one it does. It records that each of `ts` exists and **adds no equation
between distinct terms**, so it can relate `a` to `b` only for a reason `db` already had. -/
def Database.withOperands (db : Database) (ts : List Term) : Database := db.addTerms ts

@[inherit_doc Database.withOperands] def CongOn
    (db : Database) (ts : List Term) (a b : Term) : Prop := Cong (db.withOperands ts) a b

/-- An inferred equality has a witness in the original database. Its diagonal expresses
represented existence; merely mentioning an absent term does not establish it. -/
def Database.Infers (db : Database) (a b : Term) : Prop :=
  ∃ w ∈ db.terms, CongOn db [a, b] w a ∧ CongOn db [a, b] a b

/-- Completed states agree on inferred facts, including function atoms. -/
structure Database.SameMeaning (d₁ d₂ : Database) : Prop where
  sig : d₁.sig = d₂.sig
  env : d₁.env = d₂.env
  rules : d₁.rules = d₂.rules
  inferred : ∀ a b, d₁.Infers a b ↔ d₂.Infers a b

end Egglog
