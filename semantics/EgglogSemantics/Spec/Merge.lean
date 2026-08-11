import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# `:merge` functions

A merge function's table lives in the term set: the entry recording the value columns `v…`
for `f` at the key `a…` is the term `f(a…, v…)`. A constructor's entry is `f(a…)` alone,
since a constructor's value is its own application. Three things follow.

* **Congruence is the functional dependency.** A constructor's entry is its own value, so
  `Cong.congr` — a rule of the relation, not a side condition on a table — already says
  that congruent keys give congruent values. That is why a constructor has no merge
  specification, and `Action.SetLegal` is what keeps a `set` from giving it one.
* **A `:merge` body is an action list.** It records entries of other tables, so
  `MergeStep` is a relation on *databases* rather than a function combining two values, and
  merge closure is a phase of `RunStep` rather than a definition of "the value of a key".
* **Reading is a query atom, never an evaluation.** The *only* read is `Pattern.values`;
  every expression the semantics evaluates names constructors and primitives alone, so
  `Expr.eval` needs nothing of the database but its signature.

Nothing is ever removed from `terms` or `eqs`; both colliding entries survive a merge,
which is what keeps the state monotone.

The spec deliberately **over-approximates** egglog: a lookup reads any recorded output,
not the current one, and a round takes any number of merge steps, not all of them.
`MERGE.md` is the design record, and every claim here about egglog's behaviour is sourced
there.
-/

namespace Egglog
/-! ### Reading a table

Keys are compared up to congruence, so a lookup searches the key's class rather than the
term set. -/
namespace Database
/-- `vs` are outputs `db` records for `f` at the class of the key `as`.

Quantifying over congruent keys rather than re-keying entries is what lets `MergeStep`
record the combined entry at one key only and still be seen from the other, so the state
never needs re-canonicalization.

Where the key ends and the value columns begin is the caller's to say: `f(A, 1)` splits
three ways, and only the declaration knows which. A key class may record several outputs,
which is why this is a relation and not a function. Nothing *evaluates* through it, so the
over-approximation is confined to the query — `MERGE.md`, "Why the reader
over-approximates". -/
def Out (db : Database) (f : FnName) (as : List Term) (vs : List Term) : Prop :=
  ∃ bs, CongList db as bs ∧ Term.app f (bs ++ vs) ∈ db.terms

/-- **Every term `d₁` holds `d₂` holds up to congruence** — and `d₁`'s equalities are
`d₂`'s. This is the contract a reference implementation is held to: `Database.Contained`
with its term clause read up to `Cong` instead of `⊆`.

The weakening is what an implementation that **re-keys** needs. egglog's rebuild moves an
entry from its key to the canonical member of that key's congruence class; nothing here
moves one, because `Out` searches the class instead. So after a rebuild the implementation
holds `f(A, v)` where the specification still holds `f(B, v)` with `A ≅ B`, and syntactic
containment fails although nothing new is claimed. `Contained` remains the relation where
syntactic containment is what is meant.

`CongOn` rather than `Cong`, because `Cong.congr` needs *both* applications in
`d₂.terms` and `d₂` is the side that never built `f(A, v)`. The witness `t'` is what keeps
the clause from saying nothing: `CongOn d₂ [t] t t` holds by reflexivity alone. -/
structure Recorded (d₁ d₂ : Database) : Prop where
  terms : ∀ t ∈ d₁.terms, ∃ t' ∈ d₂.terms, CongOn d₂ [t] t t'
  eqs : d₁.eqs ⊆ d₂.eqs

end Database
/-! ### The merge step -/
/-- The environment a `:merge` body runs in: the two colliding entries' outputs, named
`old<i>`/`new<i>` per value column, and nothing else.

*Every* column is bound, not just the one being computed, because a column's merge may
reference any output column of the old entry. Globals desugar to nullary functions, so they
are lookups rather than environment reads. -/
def mergeEnvIdx : Nat → List Term → List Term → Env
  | _, [], _ => []
  | _, _, [] => []
  | i, o :: os, n :: ns =>
      ("old" ++ toString i, o) :: ("new" ++ toString i, n) :: mergeEnvIdx (i + 1) os ns

/-- `mergeEnvIdx`, with egglog's unindexed names for a single value column. -/
def mergeEnv : List Term → List Term → Env
  | [o], [n] => [("old", o), ("new", n)]
  | os, ns => mergeEnvIdx 0 os ns

/-- One `:merge` firing: any two entries of `f` whose keys are congruent, resolved by
running `f`'s body. A relation on *databases*, because the body is an action list: it
records entries of its own, which a value combiner `Term → Term → Term` could not express.

* The declaration supplies the **key/value split**. `f(A, 1)` is a term, and `arity` is
  the only thing that says its key is `A` and its value `1`; without that premise the
  split `key = []` would collide every entry of `f` with every other, since `CongList db
  [] []` holds unconditionally.
* Nothing is removed, and both colliding entries survive.
* **There is no `a ≠ b` guard.** `CongList` is reflexive, so an entry collides with
  *itself*. That over-approximates egglog in the safe direction, and it is why the safety
  theorem needs **no** scope condition on the signature — no `merge (x, x) = x`, no
  identity-guardedness. It works only because `MergeSaturated` is the "no step *changes*
  anything" form; the two are coupled — `MERGE.md`, "No guard on the collision".
* The combined entry is recorded at the key `as` only; `Out` reads it from `bs` too.
* The two entries are premises in both orders, so a non-commutative merge relates `db` to
  two different results — the relational reading of what egglog calls user-visible
  undefined behaviour for a non-monotone merge.
* **The body runs once, before any column is computed**, which is egglog's order: `res` is
  one expression per value column, each evaluated in the `d` that `evalActions`
  produces. -/
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

/-- Merge closure. A relation, not a fixpoint function: a merge body can build terms, so
the candidate universe grows as the closure runs and there is no measure to recurse on.
The congruence closure is different — `Impl/Closure.lean`'s `closure` stays well-founded
because `terms` is fixed while it runs. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-- No merge collision *changes* anything. egglog's `merge_all` runs to exactly this.

Stated as "every step is the identity" and not as "no step applies", which is
**unsatisfiable** here: nothing removes terms, and with no guard on the collision every
entry collides with itself, so a step always applies. -/
def MergeSaturated (db : Database) : Prop := ∀ db', MergeStep db db' → db' = db

/-- `:no-merge` is respected: no two entries of a `.noMerge` function collide on congruent
keys with different outputs.

A side condition rather than a step, and **nothing consumes it**. A `:no-merge` collision
is a program error egglog rejects at runtime, and this model has no error state for a step
to enter; stating the condition anyway is what stops `.noMerge` silently meaning "keep the
old value". -/
def Database.NoMergeOk (db : Database) : Prop :=
  ∀ f decl as bs (a b : List Term), db.sig f = some decl → decl.merge = some .noMerge →
    as.length = decl.arity → bs.length = decl.arity →
    Term.app f (as ++ a) ∈ db.terms → Term.app f (bs ++ b) ∈ db.terms →
    CongList db as bs → a = b

/-! ### E-matching and running

Which substitutions a query admits, what a round does with them, and what a command and a
program do. Congruence is read as `Cong` throughout, and a round gains one phase: merge
closure, which is a state change where congruence closure is only a relation. -/
/-- A pattern **matches** under `σ` when its instance is congruent to a term the database
holds.

The **witness** `w` is drawn from the *original* terms: without one, reflexivity on the
freshly added instance would match everything, so the witness is what stops a pattern from
matching a term the e-graph does not contain. -/
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
  congruent to `vs`. **This is the only read in the semantics.**

  The instance is the entry term `f(as…, vs…)`; the operands are its subterms, so this is
  `.expr`'s clause at a pattern the expression grammar cannot write — an application of a
  name `Expr.eval` refuses to build. -/
  | values {vs : List Expr} {f : FnName} {as : List Expr} {σ : Env}
      {us ts : List Term} {w : Term} :
      w ∈ db.terms →
      Expr.evalList db.sig as (db.env ++ σ) = some ts →
      Expr.evalList db.sig vs (db.env ++ σ) = some us →
      CongOn db [.app f (ts ++ us)] w (.app f (ts ++ us)) →
      Matches db (.values vs f as) σ

/-- The substitutions one query pattern admits: `σ` binds exactly the pattern's free
variables, each to a term the database holds, and the pattern matches under it. -/
def ValidSubst (db : Database) (p : Pattern) (σ : Env) : Prop :=
  ValidEnv (p.freeVars db.env) db σ ∧ Matches db p σ

/-- The substitutions a whole query admits: one per pattern, unioned. -/
def ValidQuerySubst (db : Database) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (ValidSubst db) q σs ∧ Env.UnionAll σs σ

/-- The databases one rule contributes, one per substitution satisfying its query.
Substitutions whose actions get stuck contribute nothing, which cannot happen for a
scoped, evaluable rule (`Scope.lean`). -/
def RuleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ, ValidQuerySubst db r.query σ ∧ evalLocalActions db r.actions σ = some d}

/-- The rule-firing half of a round: every rule fires on every substitution satisfying its
query *in the pre-state*, and all the results are unioned in. Rules therefore cannot see
each other's output within one round.

A function, but not a computation: the set of matching substitutions is carved out by a
predicate rather than enumerated. `Impl/Interp.lean`'s `execRunRules` enumerates it. -/
def RunRules (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ db.rules, d ∈ RuleResults db r}

/-- One round: fire every rule, then take any number of merge steps.

Merges are **deferred**: rule heads stage entries and the merge phase runs once every rule
has been searched, so no rule sees another's merged value within a round. The phase is not
required to *saturate*, so this relation reaches every state egglog reaches plus partially
merged ones; saturation is instead a hypothesis of the theorems that need it — `MERGE.md`,
"Saturation is a hypothesis, not a step". -/
def RunStep (db db' : Database) : Prop := MergeClosure (RunRules db) db'

/-- Run one command.

There is no congruence-restoring pass between commands, because congruence is the
predicate `Cong` rather than a set the state has to carry (`PLAN.md`, "Where 'restored
congruence' went").

`action` resolves collisions before the next command: a top-level `set` is its own merge
phase, so `(set (f) 1) (set (f) 2)` on a `:merge (max old new)` function records `f(2)`
with no `(run)` anywhere.

`run` is exactly one round; schedules are not modelled, and egglog's `(run n)` is `n`
copies of it. -/
inductive CmdStep : Database → Cmd → Database → Prop where
  | action {db d db' : Database} {a : Action} :
      evalAction db a = some d → MergeClosure d db' → CmdStep db (.action a) db'
  | rule {db : Database} {r : Rule} :
      CmdStep db (.rule r) { db with rules := insert r db.rules }
  | run {db db' : Database} : RunStep db db' → CmdStep db .run db'
  | decl {db : Database} {f : FnName} {d : FnDecl} :
      CmdStep db (.decl f d) { db with sig := Function.update db.sig f (some d) }

/-- Run the commands in order, from `db`. `ProgramStep Database.empty p` is what running
the whole program `p` means. -/
inductive ProgramStep : Database → Program → Database → Prop where
  | nil {db : Database} : ProgramStep db [] db
  | cons {db d d' : Database} {c : Cmd} {cs : Program} :
      CmdStep db c d → ProgramStep d cs d' → ProgramStep db (c :: cs) d'

end Egglog
