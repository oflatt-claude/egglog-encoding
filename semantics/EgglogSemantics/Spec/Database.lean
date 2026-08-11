import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Term

/-!
# The database

The global state: the terms the program has built, the equalities it has asserted, the
global bindings, the rules, and the declarations. A function's table lives in the term set:
a merge function's entry at the key `a…` with value columns `v…` is the term `f(a…, v…)`,
a constructor's entry is `f(a…)`, and `Database.DeclaredTerms` says every application the
state holds is one of the two.
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

end Env
/-- Egglog's global state. -/
@[ext]
structure Database where
  /-- The declared functions. Written only by `Cmd.decl`. -/
  sig : Signature
  /-- The terms the database holds — the values it built and the entries it recorded.
  Subterm-closed under `WF`, and never shrinks. -/
  terms : Set Term
  /-- The *asserted* equalities, from `union` actions. Not closed under congruence. -/
  eqs : Set (Term × Term)
  /-- Global bindings, extended by a top-level `let`. -/
  env : Env
  /-- The rules, run by `Cmd.run`. -/
  rules : Set Rule

namespace Database
/-- The initial database. -/
def empty : Database where
  sig := fun _ => none
  terms := ∅
  eqs := ∅
  env := []
  rules := ∅

/-- Every application the database holds is a **declared** function's entry: its head is
declared, and it carries that declaration's `entryWidth` children. -/
def DeclaredTerms (db : Database) : Prop :=
  ∀ f as, Term.app f as ∈ db.terms → ∃ d, db.sig f = some d ∧ as.length = d.entryWidth

/-- Insert `t` and all of its subterms. -/
def addTerm (t : Term) (db : Database) : Database :=
  { db with terms := db.terms ∪ t.subterms }

def addTerms (ts : List Term) (db : Database) : Database :=
  ts.foldl (fun d t => d.addTerm t) db

/-- Assert `a = b`, inserting both terms. -/
def addEq (a b : Term) (db : Database) : Database :=
  { (db.addTerm a).addTerm b with eqs := insert (a, b) db.eqs }

/-- Union in a whole family of databases at once, taking `sig`, `env` and `rules` from
`db`. -/
def sUnion (db : Database) (S : Set Database) : Database :=
  { db with
    terms := db.terms ∪ ⋃ d ∈ S, d.terms
    eqs := db.eqs ∪ ⋃ d ∈ S, d.eqs }

/-- Databases that differ only in an environment no `lookup` can tell apart. -/
structure EnvAgree (d₁ d₂ : Database) : Prop where
  sig : d₁.sig = d₂.sig
  terms : d₁.terms = d₂.terms
  eqs : d₁.eqs = d₂.eqs
  rules : d₁.rules = d₂.rules
  env : Env.Agree d₁.env d₂.env

/-- `d₁`'s terms and asserted equalities are among `d₂`'s; the other fields are ignored. -/
structure Contained (d₁ d₂ : Database) : Prop where
  terms : d₁.terms ⊆ d₂.terms
  eqs : d₁.eqs ⊆ d₂.eqs

/-- The database invariants: it holds the children of every term it holds, and only ever
talks about terms it holds. -/
structure WF (db : Database) : Prop where
  subtermClosed : ∀ t ∈ db.terms, t.subterms ⊆ db.terms
  eqsInTerms : ∀ p ∈ db.eqs, p.1 ∈ db.terms ∧ p.2 ∈ db.terms
  envInTerms : ∀ b ∈ db.env, b.2 ∈ db.terms

end Database
end Egglog
