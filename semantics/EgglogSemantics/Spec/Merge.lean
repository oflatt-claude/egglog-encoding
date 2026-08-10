import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# `:merge` functions

The state gains a **row set**. A row `⟨f, args, out⟩` says the database records the value
columns `out` for `f` at `args`. For a constructor there is one value column and it holds
the application itself. Three things follow.

* **Congruence is the functional dependency.** `MCong.fd` says two rows of one constructor
  whose keys are congruent have congruent outputs. At constructor rows — where
  `out = [.app f args]` — that *is* `Cong.congr`; at equal keys it is the functional
  dependency. There is no separate `congr` constructor, and `Proofs/Merge.lean`'s
  `mcong_iff_cong` is the compatibility theorem.
* **A `:merge` body is an action list.** It writes rows to other tables, so `MergeStep` is
  a relation on *databases* rather than a function combining two values, and merge closure
  is a phase of `RunStep` rather than a definition of "the value of a key".
* **Reading is a query atom, never an evaluation.** The *only* read is `Pattern.values`;
  every expression the semantics evaluates names constructors and primitives alone, so
  `Expr.eval` needs nothing of the database but its signature.

Nothing is ever removed, from any of `terms`, `rows` or `eqs`; both colliding rows survive
a merge, which is what keeps the state monotone.

The spec deliberately **over-approximates** egglog: a lookup reads any recorded output,
not the current one, and a round takes any number of merge steps, not all of them.
`MERGE.md` is the design record, and every claim here about egglog's behaviour is sourced
there.
-/

namespace Egglog
/-! ### Congruence, generalized

`MCong` is `Cong` with `congr` replaced by `fd`. Everything else is unchanged. -/
mutual

/-- Derivable equality: the congruence closure of `db`'s asserted equalities *and* the
functional dependencies of its constructors. Like `Cong`, a **partial equivalence
relation** — symmetric and transitive, but reflexive only on `db.terms`, so `MCong db a a`
says that `a` is present.

`fd` is one rule with three readings:

* at constructor rows and congruent keys, `Cong.congr`;
* at constructor rows and *equal* keys, `Cong.refl` on an application;
* at any constructor, "one key, one output" — the functional dependency.

A merge function contributes nothing here: a constructor collision is the only one whose
whole effect is an equality between terms that already exist, so it is the only one a
*relation* can express. The rest are `MergeStep`. The rule is per *column* —
`⟨x, y⟩ ∈ a.zip b` — so a multi-column constructor equates its outputs positionally. -/
inductive MCong (db : Database) : Term → Term → Prop where
  | assert {a b : Term} : (a, b) ∈ db.eqs → MCong db a b
  | refl {a : Term} : a ∈ db.terms → MCong db a a
  | symm {a b : Term} : MCong db a b → MCong db b a
  | trans {a b c : Term} : MCong db a b → MCong db b c → MCong db a c
  | fd {f : FnName} {as bs a b : List Term} {x y : Term} :
      ⟨f, as, a⟩ ∈ db.rows → ⟨f, bs, b⟩ ∈ db.rows →
      db.sig.IsCtor f → MCongList db as bs →
      (x, y) ∈ a.zip b → MCong db x y

/-- Pointwise `MCong` over key tuples. -/
inductive MCongList (db : Database) : List Term → List Term → Prop where
  | nil : MCongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      MCong db a b → MCongList db as bs → MCongList db (a :: as) (b :: bs)

end

/-! ### Reading a table

Keys are compared up to congruence, so a lookup searches the key's class rather than
the row set. -/
namespace Database
/-- `vs` are outputs `db` records for `f` at the class of the key `as`.

Quantifying over congruent keys rather than re-keying rows is what lets `MergeStep` write
the combined row at one key only and still be seen from the other, so the row set never
needs re-canonicalization.

A key class may record several outputs, which is why this is a relation and not a
function. Nothing *evaluates* through it, so the over-approximation is confined to the
query — `MERGE.md`, "Why the reader over-approximates". -/
def Out (db : Database) (f : FnName) (as : List Term) (vs : List Term) : Prop :=
  ∃ bs, MCongList db as bs ∧ Row.mk f bs vs ∈ db.rows

/-- **Every row `d₁` holds is one `d₂` records** — and `d₁`'s terms and equalities are
`d₂`'s. This is the contract a reference implementation is held to: `Database.Contained`
with its row clause read through `Out` instead of `⊆`.

The weakening is what an implementation that **re-keys** needs. egglog's rebuild moves a
row from its key to the canonical member of that key's congruence class; nothing here
moves one, because `Out` searches the class instead. So after a rebuild the implementation
holds `⟨f, [A], v⟩` where the specification still holds `⟨f, [B], v⟩` with `A ≅ B`, and
syntactic containment fails although nothing new is claimed. `Contained` remains the
relation where syntactic containment is what is meant. -/
structure Recorded (d₁ d₂ : Database) : Prop where
  terms : d₁.terms ⊆ d₂.terms
  rows : ∀ r ∈ d₁.rows, d₂.Out r.fn r.args r.out
  eqs : d₁.eqs ⊆ d₂.eqs

end Database
/-! ### The merge step -/
/-- The environment a `:merge` body runs in: the two colliding rows' outputs, named
`old<i>`/`new<i>` per value column, and nothing else.

*Every* column is bound, not just the one being computed, because a column's merge may
reference any output column of the old row. Globals desugar to nullary functions, so they
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

/-- One `:merge` firing: any two rows of `f` whose keys are congruent, resolved by running
`f`'s body. A relation on *databases*, because the body is an action list: it writes rows
of its own, which a value combiner `Term → Term → Term` could not express.

* Nothing is removed, and both colliding rows survive.
* **There is no `a ≠ b` guard.** `MCongList` is reflexive, so a row collides with
  *itself*. That over-approximates egglog in the safe direction, and it is why the safety
  theorem needs **no** scope condition on the signature — no `merge (x, x) = x`, no
  identity-guardedness. It works only because `MergeSaturated` is the "no step *changes*
  anything" form; the two are coupled — `MERGE.md`, "No guard on the collision".
* The combined row is written at the key `as` only; `Out` reads it from `bs` too.
* The two rows are premises in both orders, so a non-commutative merge relates `db` to
  two different results — the relational reading of what egglog calls user-visible
  undefined behaviour for a non-monotone merge.
* **The body runs once, before any column is computed**, which is egglog's order: `res` is
  one expression per value column, each evaluated in the `d` that `evalActions`
  produces. -/
inductive MergeStep : Database → Database → Prop where
  | collide {db d : Database} {f : FnName} {as bs a b vs : List Term}
      {body : List Action} {res : List Expr} :
      ⟨f, as, a⟩ ∈ db.rows → ⟨f, bs, b⟩ ∈ db.rows → MCongList db as bs →
      db.sig.mergeOf f = some (.merge body res) →
      evalActions { db with env := mergeEnv a b } body = some d →
      Expr.evalList d.sig res d.env = some vs →
      MergeStep db { d.addRow f as vs with env := db.env, rules := db.rules }

/-- Merge closure. A relation, not a fixpoint function: a merge body can build terms, so
the candidate universe grows as the closure runs and there is no measure to recurse on.
The congruence closure is different — `Impl/Closure.lean`'s `closure` stays well-founded
because `terms` and `rows` are fixed while it runs. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-- No merge collision *changes* anything. egglog's `merge_all` runs to exactly this.

Stated as "every step is the identity" and not as "no step applies", which is
**unsatisfiable** here: nothing removes rows, and with no guard on the collision every row
collides with itself, so a step always applies. -/
def MergeSaturated (db : Database) : Prop := ∀ db', MergeStep db db' → db' = db

/-- `:no-merge` is respected: no two rows of a `.noMerge` function collide on congruent
keys with different outputs.

A side condition rather than a step, and **nothing consumes it**. A `:no-merge` collision
is a program error egglog rejects at runtime, and this model has no error state for a step
to enter; stating the condition anyway is what stops `.noMerge` silently meaning "keep the
old value". -/
def Database.NoMergeOk (db : Database) : Prop :=
  ∀ f as bs (a b : List Term), Row.mk f as a ∈ db.rows → Row.mk f bs b ∈ db.rows →
    MCongList db as bs → db.sig.mergeOf f = some .noMerge → a = b

/-! ### E-matching and running

Which substitutions a query admits, what a round does with them, and what a command and a
program do. Congruence is read as `MCong` throughout, and a round gains one phase: merge
closure, which is a state change where congruence closure is only a relation. -/
/-- The database a match is checked in: `db` plus the terms the pattern's operands denote.

An operand is an *expression*, so it may denote a term the program never built, and `MCong`
relates nothing outside `db.terms`. Adding the operands first is what makes such an operand
matchable, and is how this model captures egglog's flattening of a nested fact into one atom
per subterm. It **asserts nothing**, so this is a conservative reading of `MCong` and not a
weaker one: `MCong.fd` still needs *both* rows present. -/
def Database.withOperands (db : Database) (ts : List Term) : Database := db.addTerms ts

@[inherit_doc Database.withOperands] def MCongOn
    (db : Database) (ts : List Term) (a b : Term) : Prop := MCong (db.withOperands ts) a b

@[inherit_doc Database.withOperands] def MCongListOn
    (db : Database) (ts : List Term) (as bs : List Term) : Prop :=
  MCongList (db.withOperands ts) as bs

/-- A pattern **matches** under `σ`, up to congruence.

The **witness** `w` is drawn from the *original* terms: without one, reflexivity on the
freshly added operand would match everything, so the witness is what stops a pattern from
matching a term the e-graph does not contain. -/
inductive MMatches (db : Database) : Pattern → Env → Prop where
  | expr {e : Expr} {σ : Env} {w t : Term} :
      w ∈ db.terms → e.eval db.sig (db.env ++ σ) = some t → MCongOn db [t] w t →
      MMatches db (.expr e) σ
  | eq {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term} :
      w ∈ db.terms →
      e₁.eval db.sig (db.env ++ σ) = some t₁ → e₂.eval db.sig (db.env ++ σ) = some t₂ →
      MCongOn db [t₁, t₂] w t₁ → MCongOn db [t₁, t₂] t₁ t₂ →
      MMatches db (.eq e₁ e₂) σ
  /-- The row atom: `f`'s row at a key class congruent to `as`, with value columns
  congruent to `vs`. **This is the only read in the semantics.**

  Its key premise is `Database.Out`'s. There is no `w ∈ db.terms` witness: the row itself
  is what forbids matching something the database does not hold. -/
  | values {vs : List Expr} {f : FnName} {as : List Expr} {σ : Env}
      {us ts ws bs : List Term} :
      Expr.evalList db.sig vs (db.env ++ σ) = some us →
      Expr.evalList db.sig as (db.env ++ σ) = some ts →
      MCongListOn db (ts ++ us) ts bs → MCongListOn db (ts ++ us) us ws →
      Row.mk f bs ws ∈ db.rows →
      MMatches db (.values vs f as) σ

/-- The substitutions one query pattern admits: `σ` binds exactly the pattern's free
variables, each to a term the database holds, and the pattern matches under it. -/
def MValidSubst (db : Database) (p : Pattern) (σ : Env) : Prop :=
  ValidEnv (p.freeVars db.env) db σ ∧ MMatches db p σ

/-- The substitutions a whole query admits: one per pattern, unioned. -/
def MValidQuerySubst (db : Database) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (MValidSubst db) q σs ∧ Env.UnionAll σs σ

/-- The databases one rule contributes, one per substitution satisfying its query.
Substitutions whose actions get stuck contribute nothing, which cannot happen for a
scoped, evaluable rule (`Scope.lean`). -/
def RuleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ, MValidQuerySubst db r.query σ ∧ evalLocalActions db r.actions σ = some d}

/-- The rule-firing half of a round: every rule fires on every substitution satisfying its
query *in the pre-state*, and all the results are unioned in. Rules therefore cannot see
each other's output within one round.

A function, but not a computation: the set of matching substitutions is carved out by a
predicate rather than enumerated. `Impl/Interp.lean`'s `execRunRules` enumerates it. -/
def RunRules (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ db.rules, d ∈ RuleResults db r}

/-- One round: fire every rule, then take any number of merge steps.

Merges are **deferred**: rule heads stage rows and the merge phase runs once every rule
has been searched, so no rule sees another's merged value within a round. The phase is not
required to *saturate*, so this relation reaches every state egglog reaches plus partially
merged ones; saturation is instead a hypothesis of the theorems that need it — `MERGE.md`,
"Saturation is a hypothesis, not a step". -/
def RunStep (db db' : Database) : Prop := MergeClosure (RunRules db) db'

/-- Run one command.

There is no congruence-restoring pass between commands, because congruence is the
predicate `MCong` rather than a set the state has to carry (`PLAN.md`, "Where 'restored
congruence' went").

`action` resolves collisions before the next command: a top-level `set` is its own merge
phase, so `(set (f) 1) (set (f) 2)` on a `:merge (max old new)` function leaves one row
holding `2` with no `(run)` anywhere.

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
