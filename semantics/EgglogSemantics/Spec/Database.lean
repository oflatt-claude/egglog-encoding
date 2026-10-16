import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Term

/-!
# The database

One assertion set stores value equations and reflexive atom facts. Function rows
are decoded using declarations; merging deletes displaced atom facts, preserving
their column values. Both compiler sides use this mathematical representation.
-/

namespace Egglog
/-- Variable bindings, innermost first. -/
abbrev Env := List (Var × Term)

namespace Env
/-- The first binding for `v`, if any. -/
def lookup (v : Var) : Env → Option Term
  | [] => none
  | (w, t) :: rest => if v = w then some t else lookup v rest

/-- The variables bound by `σ`, in order. -/
def dom (σ : Env) : List Var := σ.map Prod.fst

/-- Environments no `lookup` can tell apart. -/
def Agree (σ₁ σ₂ : Env) : Prop := ∀ v, lookup v σ₁ = lookup v σ₂

/-- `lookup` is left-biased: a binding in the prefix wins. -/
theorem lookup_append_of_some {v : Var} {t : Term} {σ₁ σ₂ : Env}
    (h : lookup v σ₁ = some t) : lookup v (σ₁ ++ σ₂) = some t := by
  induction σ₁ with
  | nil => rw [lookup] at h; exact absurd h (by simp)
  | cons b σ ih =>
      obtain ⟨w, u⟩ := b
      rw [List.cons_append, lookup]
      rw [lookup] at h
      split at h
      · rename_i hvw; rw [if_pos hvw]; exact h
      · rename_i hvw; rw [if_neg hvw]; exact ih h

@[inherit_doc lookup_append_of_some]
theorem lookup_append_of_none {v : Var} {σ₁ σ₂ : Env} (h : lookup v σ₁ = none) :
    lookup v (σ₁ ++ σ₂) = lookup v σ₂ := by
  induction σ₁ with
  | nil => rfl
  | cons b σ ih =>
      obtain ⟨w, u⟩ := b
      rw [List.cons_append, lookup]
      rw [lookup] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hvw; rw [if_neg hvw]; exact ih h

end Env

/-- A decoded function row, used by normalization. -/
structure Entry where
  name : FnName
  key : List Term
  value : List Term
  deriving DecidableEq

/-- All values mentioned by an entry. Entry atoms themselves are not constructor values. -/
def Entry.columns (e : Entry) : List Term := e.key ++ e.value

def Entry.atom (e : Entry) : Term := .app e.name e.columns

/-- Declarations fix the functional dependency and the unique column split. -/
def Entry.Valid (sig : Signature) (e : Entry) : Prop :=
  ∃ d, sig e.name = some d ∧ d.merge ≠ none ∧
    e.key.length = d.arity ∧ e.value.length = d.outArity ∧
    ∀ t ∈ e.columns, t.IsValue sig

/-- Egglog's global state. -/
@[ext]
structure Database where
  /-- The declared functions. Written only by `Cmd.decl`. -/
  sig : Signature
  /-- Value equations and reflexive atom facts; not closed under congruence. -/
  eqs : Set (Term × Term)
  /-- The evaluation context, installed temporarily for a rule or merge firing.
  Commands preserve it; a program starting at `empty` leaves it empty. -/
  env : Env
  /-- The rules, run by `Cmd.run`. -/
  rules : Set Rule

namespace Database
/-- Function rows are a view of reflexive assertions, not a separate store. -/
def entries (db : Database) : Set Entry :=
  {e | e.Valid db.sig ∧ (e.atom, e.atom) ∈ db.eqs}

/-- The initial database. -/
def empty : Database where
  sig := fun _ => none
  eqs := ∅
  env := []
  rules := ∅

/-- Record `t` and all of its subterms, each by its reflexive equation. -/
def addTerm (t : Term) (db : Database) : Database :=
  { db with eqs := db.eqs ∪ {(s, s) | s ∈ t.subterms} }

def addTerms (ts : List Term) (db : Database) : Database :=
  ts.foldl (fun d t => d.addTerm t) db

/-- Assert `a = b` and record both operands' subterms. Symmetry and endpoint reflexivity
follow from congruence; subterm existence and the stored diagonals need these writes. -/
def addEq (a b : Term) (db : Database) : Database :=
  let d := (db.addTerm a).addTerm b
  { d with eqs := insert (a, b) d.eqs }

/-- Insert a function entry, recording its column values. Identical writes coalesce;
distinct conflicting rows remain until merging resolves them. -/
def putEntry (e : Entry) (db : Database) : Database :=
  db.addTerm e.atom

def eraseEntry (e : Entry) (db : Database) : Database :=
  { db with eqs := db.eqs \ {(e.atom, e.atom)} }

/-- Union in a whole family of databases at once, taking `sig`, `env` and `rules` from
`db`. -/
def sUnion (db : Database) (S : Set Database) : Database :=
  { db with eqs := db.eqs ∪ ⋃ d ∈ S, d.eqs }

/-- Databases that differ only in an environment no `lookup` can tell apart. -/
structure EnvAgree (d₁ d₂ : Database) : Prop where
  sig : d₁.sig = d₂.sig
  eqs : d₁.eqs = d₂.eqs
  rules : d₁.rules = d₂.rules
  env : Env.Agree d₁.env d₂.env

/-- `d₁`'s equalities are among `d₂`'s; the other fields are ignored. -/
structure Contained (d₁ d₂ : Database) : Prop where
  eqs : d₁.eqs ⊆ d₂.eqs

end Database
end Egglog
