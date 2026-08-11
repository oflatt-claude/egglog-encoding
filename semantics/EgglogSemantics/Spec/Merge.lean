import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# `:merge` functions

Merge closure, e-matching, and what a command and a program do. A merge function's entry
for `f` at the key `a…` with value columns `v…` is the term `f(a…, v…)`; a constructor's is
`f(a…)` alone. Nothing is removed: both colliding entries survive a merge.
-/

namespace Egglog
/-! ### Reading a table -/
namespace Database
/-- `vs` are outputs `db` records for `f` at the class of the key `as`: a lookup searches
the key's congruence class rather than the term set, and a class may record several. -/
def Out (db : Database) (f : FnName) (as : List Term) (vs : List Term) : Prop :=
  ∃ bs, CongList db as bs ∧ Term.app f (bs ++ vs) ∈ db.terms

/-- **Every term `d₁` holds `d₂` holds up to congruence**, and `d₁`'s equalities are
`d₂`'s. The witness `t'` must be one of `d₂`'s own terms, or the clause says nothing:
`CongOn d₂ [t] t t` holds by reflexivity alone. -/
structure Recorded (d₁ d₂ : Database) : Prop where
  terms : ∀ t ∈ d₁.terms, ∃ t' ∈ d₂.terms, CongOn d₂ [t] t t'
  eqs : d₁.eqs ⊆ d₂.eqs

end Database
/-! ### The merge step -/
/-- The environment a `:merge` body runs in: the two colliding entries' outputs, every
column bound, named `old<i>`/`new<i>` per value column, and nothing else. -/
def mergeEnvIdx : Nat → List Term → List Term → Env
  | _, [], _ => []
  | _, _, [] => []
  | i, o :: os, n :: ns =>
      ("old" ++ toString i, o) :: ("new" ++ toString i, n) :: mergeEnvIdx (i + 1) os ns

/-- `mergeEnvIdx`, with the unindexed names `old`/`new` for a single value column. -/
def mergeEnv : List Term → List Term → Env
  | [o], [n] => [("old", o), ("new", n)]
  | os, ns => mergeEnvIdx 0 os ns

/-- One `:merge` firing: any two entries of `f` whose keys are congruent, resolved by
running `f`'s body once and then evaluating `res`, one expression per value column. The two
`arity` premises supply the key/value split; without them the split `key = []` fires every
entry of `f` against every other, since `CongList db [] []` holds unconditionally. The
combined entry is recorded at the key `as` alone, and with no `a ≠ b` guard an entry
collides with itself. -/
inductive MergeStep : Database → Database → Prop where
  | collide {db d : Database} {f : FnName} {decl : FnDecl} {as bs a b vs : List Term}
      {body : List Action} {res : List Expr} :
      db.sig f = some decl → decl.merge = some (.merge body res) →
      as.length = decl.arity → bs.length = decl.arity →
      Term.app f (as ++ a) ∈ db.terms → Term.app f (bs ++ b) ∈ db.terms →
      CongList db as bs →
      evalActions { db with env := mergeEnv a b } body = some d →
      Expr.evalList d.sig res d.env = some vs →
      MergeStep db
        { d.addTerm (.app f (as ++ vs)) with env := db.env, rules := db.rules }

/-- Merge closure: any number of merge steps. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-- No merge collision *changes* anything. Not "no step applies", which is unsatisfiable:
every entry collides with itself, so a step always applies. -/
def MergeSaturated (db : Database) : Prop := ∀ db', MergeStep db db' → db' = db

/-- `:no-merge` is respected: no two entries of a `.noMerge` function collide on congruent
keys with different outputs. The `arity` premises play the same role as in `MergeStep`. -/
def Database.NoMergeOk (db : Database) : Prop :=
  ∀ f decl as bs (a b : List Term), db.sig f = some decl → decl.merge = some .noMerge →
    as.length = decl.arity → bs.length = decl.arity →
    Term.app f (as ++ a) ∈ db.terms → Term.app f (bs ++ b) ∈ db.terms →
    CongList db as bs → a = b

/-! ### E-matching and running -/
/-- A pattern **matches** under `σ` when its instance is congruent to a term the database
holds. The **witness** `w` is drawn from the *original* terms: without one, reflexivity on
the freshly added instance would match everything. -/
inductive Matches (db : Database) : Pattern → Env → Prop where
  | expr {e : Expr} {σ : Env} {w t : Term} :
      w ∈ db.terms → e.eval db.sig (db.env ++ σ) = some t → CongOn db [t] w t →
      Matches db (.expr e) σ
  | eq {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term} :
      w ∈ db.terms →
      e₁.eval db.sig (db.env ++ σ) = some t₁ → e₂.eval db.sig (db.env ++ σ) = some t₂ →
      CongOn db [t₁, t₂] w t₁ → CongOn db [t₁, t₂] t₁ t₂ →
      Matches db (.eq e₁ e₂) σ
  /-- The entry atom: `f`'s entry at a key class congruent to `as`, with value columns
  congruent to `vs`, whose instance is the term `f(as…, vs…)`. **The only read.** -/
  | values {vs : List Expr} {f : FnName} {as : List Expr} {σ : Env}
      {us ts : List Term} {w : Term} :
      w ∈ db.terms →
      Expr.evalList db.sig as (db.env ++ σ) = some ts →
      Expr.evalList db.sig vs (db.env ++ σ) = some us →
      CongOn db [.app f (ts ++ us)] w (.app f (ts ++ us)) →
      Matches db (.values vs f as) σ

/-- The substitutions one query pattern admits: `σ` binds exactly the pattern's free
variables, and the pattern matches under it. -/
def ValidSubst (db : Database) (p : Pattern) (σ : Env) : Prop :=
  ValidEnv (p.freeVars db.env) db σ ∧ Matches db p σ

/-- The substitutions a whole query admits: one per pattern, unioned. -/
def ValidQuerySubst (db : Database) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (ValidSubst db) q σs ∧ Env.UnionAll σs σ

/-- The databases one rule contributes, one per substitution satisfying its query. -/
def RuleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ, ValidQuerySubst db r.query σ ∧ evalLocalActions db r.actions σ = some d}

/-- The rule-firing half of a round: every rule fires on every substitution satisfying its
query *in the pre-state*, and all the results are unioned in. -/
def RunRules (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ db.rules, d ∈ RuleResults db r}

/-- One round: fire every rule, then take any number of merge steps. Merges are
**deferred**, and the merge phase is not required to saturate. -/
def RunStep (db db' : Database) : Prop := MergeClosure (RunRules db) db'

/-- Run one command. An `action` takes merge closure before the next command, so a
top-level `set` is its own merge phase; `run` is exactly one round. -/
inductive CmdStep : Database → Cmd → Database → Prop where
  | action {db d db' : Database} {a : Action} :
      evalAction db a = some d → MergeClosure d db' → CmdStep db (.action a) db'
  | rule {db : Database} {r : Rule} :
      CmdStep db (.rule r) { db with rules := insert r db.rules }
  | run {db db' : Database} : RunStep db db' → CmdStep db .run db'
  | decl {db : Database} {f : FnName} {d : FnDecl} :
      CmdStep db (.decl f d) { db with sig := Function.update db.sig f (some d) }

/-- Run the commands in order. `ProgramStep Database.empty p` is running the program `p`. -/
inductive ProgramStep : Database → Program → Database → Prop where
  | nil {db : Database} : ProgramStep db [] db
  | cons {db d d' : Database} {c : Cmd} {cs : Program} :
      CmdStep db c d → ProgramStep d cs d' → ProgramStep db (c :: cs) d'

end Egglog
