import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Term

/-!
# The database

The state separates constructor existence/equations from function entries. Writes
insert directly into the entry set, which may temporarily contain conflicting rows.
Both compiler sides use this same mathematical representation.
There is no separate constructor term set: `t = t` records that `t`
was built, and `Database.terms` is the terms that are self-equal. Replacing a function
entry preserves the existence of its columns and all established equalities.
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

/-- A current function entry. Outputs are an explicit tuple, separate from the key. -/
structure Entry where
  name : FnName
  key : List Term
  value : List Term
  deriving DecidableEq

/-- All values mentioned by an entry. Entry atoms themselves are not constructor values. -/
def Entry.columns (e : Entry) : List Term := e.key ++ e.value

/-- Egglog's global state. -/
@[ext]
structure Database where
  /-- The declared functions. Written only by `Cmd.decl`. -/
  sig : Signature
  /-- The *asserted* equalities: `union`s, and a reflexive `t = t` per term built. Not
  closed under congruence, and never shrinks. -/
  eqs : Set (Term × Term)
  /-- Current function entries; merging replaces displaced entries. -/
  entries : Set Entry := ∅
  /-- The evaluation context, installed temporarily for a rule or merge firing.
  Commands preserve it; a program starting at `empty` leaves it empty. -/
  env : Env
  /-- The rules, run by `Cmd.run`. -/
  rules : Set Rule

namespace Database
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

/-- Assert `a = b`, recording both terms. -/
def addEq (a b : Term) (db : Database) : Database :=
  let d := (db.addTerm a).addTerm b
  { d with eqs := insert (a, b) d.eqs }

/-- Insert a function entry, recording its column values. Identical writes coalesce;
distinct conflicting rows remain until merging resolves them. -/
def putEntry (e : Entry) (db : Database) : Database :=
  let d := db.addTerms e.columns
  { d with entries := insert e d.entries }

def eraseEntry (e : Entry) (db : Database) : Database :=
  { db with entries := db.entries \ {e} }

/-- Union in a whole family of databases at once, taking `sig`, `env` and `rules` from
`db`. -/
def sUnion (db : Database) (S : Set Database) : Database :=
  { db with
    eqs := db.eqs ∪ ⋃ d ∈ S, d.eqs
    entries := db.entries ∪ ⋃ d ∈ S, d.entries }

/-- Databases that differ only in an environment no `lookup` can tell apart. -/
structure EnvAgree (d₁ d₂ : Database) : Prop where
  sig : d₁.sig = d₂.sig
  eqs : d₁.eqs = d₂.eqs
  entries : d₁.entries = d₂.entries
  rules : d₁.rules = d₂.rules
  env : Env.Agree d₁.env d₂.env

/-- `d₁`'s equalities are among `d₂`'s; the other fields are ignored. -/
structure Contained (d₁ d₂ : Database) : Prop where
  eqs : d₁.eqs ⊆ d₂.eqs

end Database
end Egglog
