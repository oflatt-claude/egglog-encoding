import EgglogSemantics.Proofs.StoredCong

/-! Constructor data and flat rows: invariants used only by the compiler proofs. -/

namespace Egglog
namespace Term
mutual

/-- Values contain only literals and declared constructors, never table atoms. -/
def isValue (sig : Signature) : Term → Bool
  | .lit _ => true
  | .app f args => decide (sig.IsCtor f) && areValues sig args

def areValues (sig : Signature) : List Term → Bool
  | [] => true
  | t :: ts => isValue sig t && areValues sig ts

end

abbrev IsValue (sig : Signature) (t : Term) : Prop := t.isValue sig = true

end Term

/-- A decoded row whose columns contain only constructor data. -/
def Entry.Valid (sig : Signature) (e : Entry) : Prop :=
  ∃ d, sig e.name = some d ∧ d.merge ≠ none ∧
    e.key.length = d.arity ∧ e.value.length = d.outArity ∧
    ∀ t ∈ e.columns, t.IsValue sig

/-- Held constructor data, used to bound the generated rebuilding computation. -/
def Database.values (db : Database) : Set Term :=
  {t | t ∈ db.terms ∧ t.IsValue db.sig}

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

end Egglog
