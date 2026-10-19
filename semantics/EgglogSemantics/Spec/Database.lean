import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Term

/-!
# The database

One assertion set stores equations and reflexive atom facts. Function rows
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

end Env

/-- A decoded function row, used by normalization. -/
structure Entry where
  name : FnName
  key : List Term
  value : List Term
  deriving DecidableEq

/-- The key and output columns of an entry. -/
def Entry.columns (e : Entry) : List Term := e.key ++ e.value

def Entry.atom (e : Entry) : Term := .app e.name e.columns

/-- Declarations fix the functional dependency and the unique column split. -/
def Entry.Shape (sig : Signature) (e : Entry) : Prop :=
  ∃ d, sig e.name = some d ∧ d.merge ≠ none ∧
    e.key.length = d.arity ∧ e.value.length = d.outArity

/-- Egglog's global state. -/
@[ext, blueprint "def:state"
  (statement := /--
  \[
  \begin{gathered}
    D=(\Sigma,E,\mathcal R)\qquad
    \Sigma:\mathit{Fn}\rightharpoonup\mathit{Decl}\qquad
    E\subseteq\{(s,t)\mid s,t\in\mathit{Term}\}\qquad
    \mathcal R=\{\rho_1,\ldots,\rho_m\}\\[1em]
    \rows D=\{f(t_1,\ldots,t_n)\mid
      (f(t_1,\ldots,t_n),f(t_1,\ldots,t_n))\in E,\
      \Sigma(f)=\kw{fun}(k,\ell,\mu)\}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
structure Database where
  /-- The declared functions. Written only by `Cmd.decl`. -/
  sig : Signature
  /-- Equations and reflexive atom facts; not closed under congruence. -/
  eqs : Set (Term × Term)
  /-- The evaluation context, installed temporarily for a rule or merge firing.
  Commands preserve it; a program starting at `empty` leaves it empty. -/
  env : Env
  /-- The rules, run by `Cmd.run`. -/
  rules : Set Rule

namespace Database
/-- Function rows are a view of reflexive assertions, not a separate store. -/
def entries (db : Database) : Set Entry :=
  {e | e.Shape db.sig ∧ (e.atom, e.atom) ∈ db.eqs}

/-- The initial database. -/
def empty : Database where
  sig := fun _ => none
  eqs := ∅
  env := []
  rules := ∅

/-- Assert that `t` exists; congruence supplies subterm existence. -/
def addTerm (t : Term) (db : Database) : Database :=
  { db with eqs := insert (t, t) db.eqs }

def addTerms (ts : List Term) (db : Database) : Database :=
  ts.foldl (fun d t => d.addTerm t) db

/-- Assert `a = b`; congruence supplies endpoint and subterm existence. -/
def addEq (a b : Term) (db : Database) : Database :=
  { db with eqs := insert (a, b) db.eqs }

/-- Assert a set of equations. -/
def addEqs (ps : Set (Term × Term)) (db : Database) : Database :=
  { db with eqs := db.eqs ∪ ps }

/-- Insert a function entry, recording its column values. Identical writes coalesce;
distinct conflicting rows remain until merging resolves them. -/
def putEntry (e : Entry) (db : Database) : Database :=
  db.addTerm e.atom

/-- Remove a row while retaining its column values. -/
@[blueprint "def:erase-row"
  (statement := /--
  \[
  D\ominus f(t_1,\ldots,t_n)\triangleq
    D[E\gets(E\setminus\{(f(t_1,\ldots,t_n),f(t_1,\ldots,t_n))\})
      \cup\{(t_i,t_i)\mid 1\le i\le n\}]
  \]
  -/)
  (latexEnv := "paperfragment")]
def eraseEntry (e : Entry) (db : Database) : Database :=
  { db with eqs := (db.eqs \ {(e.atom, e.atom)}) ∪
      {p | ∃ t ∈ e.columns, p = (t, t)} }

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
