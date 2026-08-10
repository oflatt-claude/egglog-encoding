import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Term

/-!
# The database

The global state: the terms and rows the program has built, the equalities it has
asserted, the global bindings, the rules, and the declarations. Two things are worth
saying about it up front.

* `eqs` holds only the *asserted* equalities. The equalities that *follow* are `Cong`,
  a predicate, so there is no closed set for the state to carry or maintain. See
  `PLAN.md`, "Where 'restored congruence' went".
* `Database.addTerm` inserts a term together with all of its subterms, so the database
  holds the children of everything it holds by construction, rather than by a repair
  pass between commands. This is unobservable because no action consults congruence.
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

/-- Environments no `lookup` can tell apart. `Env.UnionAll` may leave a variable bound
twice with the same term, which `Agree` ignores. -/
def Agree (σ₁ σ₂ : Env) : Prop := ∀ v, lookup v σ₁ = lookup v σ₂

end Env
/-- Egglog's global state. -/
@[ext]
structure Database where
  /-- The declared functions. Written only by `Cmd.decl`. -/
  sig : Signature
  /-- The terms the database holds. Subterm-closed under `WF`. -/
  terms : Set Term
  /-- The *asserted* rows. A merge never removes one; it adds the combined row beside
  the two it merged, which is what keeps the state monotone. For a constructor the rows
  are determined by `terms` via `Term.ctorRows`, and `addTerm` maintains that. -/
  rows : Set Row
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
  rows := ∅
  eqs := ∅
  env := []
  rules := ∅

/-- The constructor rows a term set induces.

`addTerm` maintains `rows` at exactly this value for a constructor-only program, which
is the precise sense in which `terms` determines `rows` there. -/
def ctorRowsOf (terms : Set Term) : Set Row :=
  {r | r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ terms}

/-- The database's rows are exactly the constructor rows its terms induce.

True of `empty`, preserved by `addTerm`/`addEq`, and false as soon as a `set` writes a
`:merge` function's row. It is the hypothesis under which the functional dependency
`Cong.fd` coincides with plain congruence — see `Proofs/Merge.lean`'s `mcong_iff_cong`. -/
def CtorRows (db : Database) : Prop := db.rows = ctorRowsOf db.terms

/-- Every application the database holds is a **declared** constructor's.

True of any database a program builds: `Expr.eval` builds only at a declared constructor —
a merge function's application would be a lookup and an undeclared name has no rule at all
— so only constructors ever appear inside a `Term` (`Term.ctorRows` says the same thing
from the other side). Unlike `CtorRows` this survives a `:merge` declaration of some
*other* name, because it constrains `terms`, which merging never touches —
`FDatabase.mergeRound_confined`.

It is the second hypothesis of `Proofs/Merge.lean`'s `mcong_iff_cong`, and it has to be
carried as a state invariant (`Database.CtorState`): `Signature.AllConstructors` says
nothing *is* a merge function, which leaves an undeclared name neither. -/
def CtorTerms (db : Database) : Prop :=
  ∀ f as, Term.app f as ∈ db.terms → db.sig.IsCtor f

/-- The database holds the constructor row of every application it holds.

The *inclusion* half of `CtorRows`, and the half that survives merging: `addTerm` inserts
these rows, and a merge only adds and removes rows of `.merge` functions. `CtorRows` is
this plus the reverse inclusion, and it is the reverse one that a `set` or a `:merge`
declaration breaks. -/
def RowsComplete (db : Database) : Prop := ctorRowsOf db.terms ⊆ db.rows

/-- Insert `t`, all of its subterms, and their constructor rows. -/
def addTerm (t : Term) (db : Database) : Database :=
  { db with terms := db.terms ∪ t.subterms, rows := db.rows ∪ t.ctorRows }

/-- `addTerm` over a list. -/
def addTerms (ts : List Term) (db : Database) : Database :=
  ts.foldl (fun d t => d.addTerm t) db

/-- `(set (f as…) vs)`: build the operands, then assert the row. Only *asserted* — a
collision with a congruent key is resolved by `Cong.fd` or by `MergeStep`, neither of
which removes this row. -/
def addRow (f : FnName) (as vs : List Term) (db : Database) : Database :=
  { (db.addTerms as).addTerms vs with
    rows := insert ⟨f, as, vs⟩ ((db.addTerms as).addTerms vs).rows }

/-- Assert `a = b`, inserting both terms. -/
def addEq (a b : Term) (db : Database) : Database :=
  { (db.addTerm a).addTerm b with eqs := insert (a, b) db.eqs }

/-- Union in a whole family of databases at once.

Specialized to the way it is used: `sig`, `env` and `rules` are taken from `db`. That
loses nothing because the only union the semantics takes is `(run)`'s, whose operands
all carry the caller's env and rules — `ruleResults_env` and `ruleResults_rules`. -/
def sUnion (db : Database) (S : Set Database) : Database :=
  { db with
    terms := db.terms ∪ ⋃ d ∈ S, d.terms
    rows := db.rows ∪ ⋃ d ∈ S, d.rows
    eqs := db.eqs ∪ ⋃ d ∈ S, d.eqs }

/-- Databases that differ only in an environment no `lookup` can tell apart.

Nothing but `Expr.eval` reads the environment, so this is enough to make two
databases behave identically. It is the invariant `evalActions_envAgree` carries. -/
structure EnvAgree (d₁ d₂ : Database) : Prop where
  sig : d₁.sig = d₂.sig
  terms : d₁.terms = d₂.terms
  rows : d₁.rows = d₂.rows
  eqs : d₁.eqs = d₂.eqs
  rules : d₁.rules = d₂.rules
  env : Env.Agree d₁.env d₂.env

/-- `d₁`'s terms and asserted equalities are among `d₂`'s. This is exactly what
`Cong` monotonicity needs, so it ignores the other fields. -/
structure Contained (d₁ d₂ : Database) : Prop where
  terms : d₁.terms ⊆ d₂.terms
  rows : d₁.rows ⊆ d₂.rows
  eqs : d₁.eqs ⊆ d₂.eqs

/-- The database invariants.

`subtermClosed` says the database holds the children of every term it holds, which
`addTerm` maintains by construction. The other two say the database only ever talks
about terms it holds. -/
structure WF (db : Database) : Prop where
  subtermClosed : ∀ t ∈ db.terms, t.subterms ⊆ db.terms
  eqsInTerms : ∀ p ∈ db.eqs, p.1 ∈ db.terms ∧ p.2 ∈ db.terms
  envInTerms : ∀ b ∈ db.env, b.2 ∈ db.terms

end Database
end Egglog
