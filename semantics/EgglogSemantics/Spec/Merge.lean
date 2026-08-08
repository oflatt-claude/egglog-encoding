import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# `:merge` functions

The state gains a **row set**. A row `⟨f, args, out⟩` says the database records the
value columns `out` for `f` at `args`. For a constructor there is one value column and
it holds the application itself.

Three things follow, and the first is the milestone:

* **Congruence is the functional dependency.** `MCong.fd` says two rows of one
  `.union` function whose keys are congruent have congruent outputs. At constructor
  rows — where `out = [.app f args]` — that *is* `Cong.congr`; at equal keys it is the
  functional dependency. There is no separate `congr` constructor.
  `Proofs/Merge.lean`'s `mcong_iff_cong` is the compatibility theorem.
* **A `:merge` body is an action list.** It writes rows to other tables, so `MergeStep`
  is a relation on *databases*, not a function combining two values, and merge closure
  is a phase of `RunStep` rather than a definition of "the value of a key".
* **Reading is a query atom, never an evaluation.** The *only* read is `Pattern.values`;
  every expression the semantics evaluates names constructors and primitives alone. So
  `Expr.MEval` is `Expr.eval` plus primitive resolution — deterministic, and a function
  of the signature and the environment rather than of the database.

Nothing is ever removed, from any of `terms`, `rows` or `eqs`. Both colliding rows
survive a merge, which is what keeps the state monotone.

The spec deliberately **over-approximates** egglog rather than matching it: a lookup
reads any recorded output, not the current one, and a round takes any number of merge
steps, not all of them.

`MERGE.md` is the design record — what egglog does, what was rejected, and the open
questions. Every claim here about egglog's behaviour is sourced there.
-/

namespace Egglog
/-! ### Congruence, generalized

`MCong` is `Cong` with `congr` replaced by `fd`. Everything else is unchanged. -/
mutual

/-- Derivable equality: the congruence closure of `db`'s asserted equalities *and* the
functional dependencies of its `.union` functions.

Compared with `Cong`, the `congr` constructor is gone and `fd` has taken its place.
One rule, three readings:

* at constructor rows and congruent keys, `Cong.congr`;
* at constructor rows and *equal* keys, `Cong.refl` on an application;
* at any `.union` function, "one key, one output" — the functional dependency.

A `.merge` or `.noMerge` function contributes nothing here. That is deliberate: a
`.union` collision is the only one whose whole effect is an equality between terms
that already exist, so it is the only one a *relation* can express. The rest are
`MergeStep`.

The rule is per *column* — `⟨x, y⟩ ∈ a.zip b` — so a multi-column `.union` function
equates its outputs positionally. See `MERGE.md`, "Multi-column outputs". -/
inductive MCong (db : Database) : Term → Term → Prop where
  | assert {a b : Term} : (a, b) ∈ db.eqs → MCong db a b
  | refl {a : Term} : a ∈ db.terms → MCong db a a
  | symm {a b : Term} : MCong db a b → MCong db b a
  | trans {a b c : Term} : MCong db a b → MCong db b c → MCong db a c
  | fd {f : FnName} {as bs a b : List Term} {x y : Term} :
      ⟨f, as, a⟩ ∈ db.rows → ⟨f, bs, b⟩ ∈ db.rows →
      db.sig.mergeOf f = MergeSpec.union → MCongList db as bs →
      (x, y) ∈ a.zip b → MCong db x y

/-- Pointwise `MCong` over key tuples. Companion of `MCong.fd`, for the same reason
`CongList` is `Cong.congr`'s. -/
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

Quantifying over congruent keys rather than re-keying rows is what lets `MergeStep`
write the combined row at one key only and still be seen from the other, so the row set
never needs re-canonicalization. Monotone in `Contained`, because `MCongList` is.

A key class may record several outputs, which is why this is a relation and not a
function. Nothing *evaluates* through it — `Expr.MEval` does not read — so the
over-approximation is confined to the query, where `MValidSubst.values` matches any
recorded row. See `MERGE.md`, "Why the reader over-approximates". -/
def Out (db : Database) (f : FnName) (as : List Term) (vs : List Term) : Prop :=
  ∃ bs, MCongList db as bs ∧ Row.mk f bs vs ∈ db.rows

end Database
/-! ### The term order

One definition with two jobs. `ordering-min`/`ordering-max` are part of the *program*
the encoding writes — the union-find's merge body is literally
`(set (@UF_<S> (ordering-max old new)) (values (ordering-min old new) ()))` — and they
are also what makes an interpreter's choice of which collision to fire deterministic.

`Term.blt` is a *structural* order where egglog's is an allocation order, so the two pick
different class representatives. That is an accepted deviation and a hypothesis of any
future simulation theorem; `MERGE.md`, "The representative deviation", has the argument
and two repros against the binary. -/
mutual

/-- A total order on terms: literals below applications, then by argument count, then
by name, then lexicographically. Written by hand and mutually, for the same reason
`Term.decEq` is. -/
def Term.blt : Term → Term → Bool
  | .lit (.int m), .lit (.int n) => decide (m < n)
  | .lit _, .app _ _ => true
  | .app _ _, .lit _ => false
  | .app f as, .app g bs =>
      if as.length ≠ bs.length then decide (as.length < bs.length)
      else if f ≠ g then decide (f < g)
      else Term.bltList as bs

/-- `Term.blt` lexicographically over argument lists. -/
def Term.bltList : List Term → List Term → Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then Term.bltList as bs else Term.blt a b

end

/-- egglog's `ordering-min`. -/
def Term.orderingMin (s t : Term) : Term := if Term.blt s t then s else t

/-- egglog's `ordering-max`. -/
def Term.orderingMax (s t : Term) : Term := if Term.blt s t then t else s

/-- The primitives this fragment has. egglog resolves a primitive by name out of a
table that shares a namespace with user functions, which is why these are `Expr.app`
of a reserved name rather than a new `Expr` constructor — see `MERGE.md`, "Primitives
without churning `Expr`". -/
inductive Prim where
  | orderingMin
  | orderingMax
  /-- egglog's `i64` `min`. -/
  | intMin
  /-- egglog's `i64` `max`. -/
  | intMax
  deriving DecidableEq, Repr

/-- The reserved names. A user function of the same name is shadowed, as in egglog. See
`MERGE.md`, "Primitives without churning `Expr`", for why `min`/`max` are among them. -/
def Prim.ofName : FnName → Option Prim
  | "ordering-min" => some .orderingMin
  | "ordering-max" => some .orderingMax
  | "min" => some .intMin
  | "max" => some .intMax
  | _ => none

/-- A primitive's meaning. `none` for the wrong arity, and for `min`/`max` also for a
non-literal operand — they are `i64` primitives, and this model has no sort discipline to
reject the application statically. -/
def Prim.apply : Prim → List Term → Option Term
  | .orderingMin, [s, t] => some (Term.orderingMin s t)
  | .orderingMax, [s, t] => some (Term.orderingMax s t)
  | .intMin, [.lit (.int m), .lit (.int n)] => some (.lit (.int (min m n)))
  | .intMax, [.lit (.int m), .lit (.int n)] => some (.lit (.int (max m n)))
  | _, _ => none

/-! `Prim.ofName` resolves a *reserved name*, so whether an application builds a term or
runs a primitive is a property of the name and not of the syntax. `NoPrim` is that
property, quantified over the names an expression actually mentions — the unrestricted
form `∀ f, Prim.ofName f = none` is *false*, `ordering-min` being one, which is why the
quantifier has to be over `e`. It is the condition under which `Expr.eval` and
`Expr.MEval` agree. -/
mutual

/-- No reserved primitive name occurs in `e`, so "build an application" is the right
reading of every `.app` in it. -/
def Expr.NoPrim : Expr → Prop
  | .lit _ => True
  | .var _ => True
  | .app f args => Prim.ofName f = none ∧ Expr.NoPrimList args

/-- `Expr.NoPrim` over an argument list. -/
def Expr.NoPrimList : List Expr → Prop
  | [] => True
  | e :: es => Expr.NoPrim e ∧ Expr.NoPrimList es

end

/-! `Expr.NoPrim` lifted to the program, in the shape `Program.CtorDecls` has: every
expression position a run evaluates, and no threading, because `Prim.ofName` reads a name
and nothing a command does changes what it says.

The positions are the ones `Expr.MEval` is invoked from — a top-level action, a rule head,
and a query's operands. A `Pattern.values` atom's *function name* is not one of them: it
names a table to read rather than a term to build, so a reserved name there is not an
application at all. -/

/-- No expression position of `a` names a primitive. -/
def Action.NoPrim : Action → Prop
  | .expr e => e.NoPrim
  | .letBind _ e => e.NoPrim
  | .union e₁ e₂ => e₁.NoPrim ∧ e₂.NoPrim
  | .set _ args out => Expr.NoPrimList args ∧ Expr.NoPrimList out

/-- Every action in the list. -/
def Actions.NoPrim : List Action → Prop
  | [] => True
  | a :: as => a.NoPrim ∧ Actions.NoPrim as

/-- A query fact. -/
def Pattern.NoPrim : Pattern → Prop
  | .expr e => e.NoPrim
  | .eq e₁ e₂ => e₁.NoPrim ∧ e₂.NoPrim
  | .values vs _ as => Expr.NoPrimList vs ∧ Expr.NoPrimList as

/-- A rule's query and head. -/
def Rule.NoPrim (r : Rule) : Prop :=
  (∀ p ∈ r.query, p.NoPrim) ∧ Actions.NoPrim r.actions

/-- A command. A `decl` carries expressions only in a `:merge` body, and the fragment this
is used in has none: `Cmd.CtorDecl` forces the merge to be `.union`. -/
def Cmd.NoPrim : Cmd → Prop
  | .action a => a.NoPrim
  | .rule r => r.NoPrim
  | .run => True
  | .decl _ _ => True

/-- Every command, as `Program.CtorDecls`. -/
def Program.NoPrim (p : Program) : Prop := ∀ c ∈ p, c.NoPrim

/-! ### Evaluation

`Expr.eval` is a function of the environment alone, which is exactly right while every
function is a constructor: a term is its own identity, so building one reads nothing.
`Expr.MEval` adds the one thing `:merge` forces, which is not reading but **primitives**
— a `:merge (min old new)` body has to compute `3` rather than build the term
`min(5, 3)`.

It does *not* read the database. An application of a non-constructor is a lookup, and a
lookup is a query atom (`Pattern.values`), never an expression, so there is no `lookup`
constructor here, `MEval` is deterministic, and it consults `db` only for `db.sig`. -/
mutual

/-- The value an expression denotes: `Expr.eval` with primitives resolved.

`ctor` builds and `prim` computes, split on the reserved name first, as egglog's primitive
table is consulted first. A `Term` therefore contains only constructor applications, which
is what lets `Term.ctorRows` need no signature.

There is deliberately **no rule for a non-constructor application**. That is a lookup, and
`Impl/Check.lean`'s `noLookup` rejects one statically in every position this relation is
used from — a rule head, a top-level action, a `:merge` body, and a query's operands — so
a program the model accepts never reaches the missing case. Reading happens in the query,
where `MValidSubst.values` matches a row directly.

Partiality that was `none` in `Expr.eval` is "no `t` related": an unbound variable, or a
primitive at the wrong operands. `Scope.lean`'s "a well-scoped program never gets stuck"
covers the first and not the second, which is egglog's own `i64` type error. -/
inductive Expr.MEval (db : Database) (σ : Env) : Expr → Term → Prop where
  | lit {l : Lit} : Expr.MEval db σ (.lit l) (.lit l)
  | var {v : Var} {t : Term} : Env.lookup v σ = some t → Expr.MEval db σ (.var v) t
  | ctor {f : FnName} {args : List Expr} {ts : List Term} :
      Prim.ofName f = none → db.sig.mergeOf f = MergeSpec.union →
      Expr.MEvalList db σ args ts → Expr.MEval db σ (.app f args) (.app f ts)
  | prim {f : FnName} {p : Prim} {args : List Expr} {ts : List Term} {v : Term} :
      Prim.ofName f = some p → Expr.MEvalList db σ args ts → p.apply ts = some v →
      Expr.MEval db σ (.app f args) v

/-- `Expr.MEval` over an argument list. -/
inductive Expr.MEvalList (db : Database) (σ : Env) : List Expr → List Term → Prop where
  | nil : Expr.MEvalList db σ [] []
  | cons {e : Expr} {es : List Expr} {t : Term} {ts : List Term} :
      Expr.MEval db σ e t → Expr.MEvalList db σ es ts →
      Expr.MEvalList db σ (e :: es) (t :: ts)

end

/-! ### Actions that write rows -/
/-- One row action.

The three inherited cases are `evalAction`'s, read relationally. `set` is the new one,
and it only ever adds. -/
inductive Database.ActionStep : Database → Action → Database → Prop where
  | expr {db : Database} {e : Expr} {t : Term} :
      Expr.MEval db db.env e t → Database.ActionStep db (.expr e) (db.addTerm t)
  | letBind {db : Database} {v : Var} {e : Expr} {t : Term} :
      Expr.MEval db db.env e t →
      Database.ActionStep db (.letBind v e)
        { db.addTerm t with env := (v, t) :: db.env }
  | union {db : Database} {e₁ e₂ : Expr} {t₁ t₂ : Term} :
      Expr.MEval db db.env e₁ t₁ → Expr.MEval db db.env e₂ t₂ →
      Database.ActionStep db (.union e₁ e₂) (db.addEq t₁ t₂)
  | set {db : Database} {f : FnName} {args out : List Expr} {ts vs : List Term} :
      Expr.MEvalList db db.env args ts → Expr.MEvalList db db.env out vs →
      Database.ActionStep db (.set f args out) (db.addRow f ts vs)

/-- A sequence of row actions, run in order. -/
inductive Database.ActionsStep : Database → List Action → Database → Prop where
  | nil {db : Database} : Database.ActionsStep db [] db
  | cons {db d d' : Database} {a : Action} {as : List Action} :
      Database.ActionStep db a d → Database.ActionsStep d as d' →
      Database.ActionsStep db (a :: as) d'

/-! ### The merge step -/
/-- The environment a `:merge` body runs in: the two colliding rows' outputs, named
`old<i>`/`new<i>` per value column, and nothing else.

*Every* column is bound, not just the one being computed, because a column's merge may
reference any output column of the old row. A body's own `let`s extend this; globals
desugar to nullary functions, so they are lookups rather than environment reads. -/
def mergeEnvIdx : Nat → List Term → List Term → Env
  | _, [], _ => []
  | _, _, [] => []
  | i, o :: os, n :: ns =>
      ("old" ++ toString i, o) :: ("new" ++ toString i, n) :: mergeEnvIdx (i + 1) os ns

/-- `mergeEnvIdx`, with egglog's unindexed names for a single value column. -/
def mergeEnv : List Term → List Term → Env
  | [o], [n] => [("old", o), ("new", n)]
  | os, ns => mergeEnvIdx 0 os ns

/-- One `:merge` firing: any two rows of `f` whose keys are congruent, resolved by
running `f`'s body.

A relation on *databases*, because the body is an action list: it writes rows of its
own, which a value combiner `Term → Term → Term` could not express.

* Nothing is removed — `db` is `Contained` in the result, and both colliding rows
  survive, which keeps every monotonicity lemma alive.
* **There is no `a ≠ b` guard, deliberately.** `MCongList` is reflexive, so a row
  collides with *itself*. That over-approximates egglog in the safe direction, and it is
  why the safety theorem needs **no** scope condition on the signature — no
  `merge (x, x) = x`, no identity-guardedness. It works only because `MergeSaturated` is
  the "no step *changes* anything" form; the two are coupled. `MERGE.md`, "No guard on
  the collision", has the argument and its two intended consequences.
* The combined row is written at the key `as` only; `Out` reads it from `bs` too.
* The two rows are premises in both orders, so a non-commutative merge relates `db` to
  two different results — the relational reading of what egglog calls user-visible
  undefined behaviour for a non-monotone merge.
* **The body runs once, before any column is computed**: `ActionsStep` produces `d` and
  every column of `res` is then evaluated in `d`, which is egglog's order. `res` is one
  expression per value column. -/
inductive MergeStep : Database → Database → Prop where
  | collide {db d : Database} {f : FnName} {as bs a b vs : List Term}
      {body : List Action} {res : List Expr} :
      ⟨f, as, a⟩ ∈ db.rows → ⟨f, bs, b⟩ ∈ db.rows → MCongList db as bs →
      db.sig.mergeOf f = MergeSpec.merge body res →
      Database.ActionsStep { db with env := mergeEnv a b } body d →
      Expr.MEvalList d d.env res vs →
      MergeStep db { d.addRow f as vs with env := db.env, rules := db.rules }

/-- Merge closure.

A relation, not a fixpoint function: a merge body can build terms, so the candidate
universe grows as the closure runs and there is no measure to recurse on. This is
`PLAN.md` M9's "no termination claim", and it is what separates the merge closure from
the congruence closure — `Impl/Closure.lean`'s `closure` stays well-founded because
`terms` and `rows` are fixed while it runs. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-- No merge collision *changes* anything. egglog's `merge_all` runs to exactly this.

Stated as "every step is the identity" and not as "no step applies", which is
**unsatisfiable** here: nothing removes rows, and with no guard on the collision every
row collides with itself, so a step always applies. This form is what makes dropping the
guard workable, so the two are coupled — see `MERGE.md`, "Saturation is a hypothesis,
not a step". -/
def MergeSaturated (db : Database) : Prop := ∀ db', MergeStep db db' → db' = db

/-- `:no-merge` is respected: no two rows of a `.noMerge` function collide on
congruent keys with different outputs.

A side condition rather than a step, and **nothing consumes it** — deliberately. A
`:no-merge` collision is a program error egglog rejects at runtime, and this model has no
error state for a step to enter, so the condition is stated without being enforced.
Having it stated is what stops `.noMerge` silently meaning "keep the old value". See
`MERGE.md`, "`:no-merge` collisions, out of scope". -/
def Database.NoMergeOk (db : Database) : Prop :=
  ∀ f as bs (a b : List Term), Row.mk f as a ∈ db.rows → Row.mk f bs b ∈ db.rows →
    MCongList db as bs → db.sig.mergeOf f = MergeSpec.noMerge → a = b

/-! ### E-matching and running

`Match.lean` and `Step.lean` ported by replacing `Cong` with `MCong` and `Expr.eval`
with `Expr.MEval`. The one non-mechanical change is `RunStep`: merge closure is a
*phase* of a round, because it is a state change where congruence closure is only a
relation. -/
/-- `ValidSubst`, over `MCong`. The witness formulation is unchanged. -/
inductive MValidSubst (db : Database) : Pattern → Env → Prop where
  | expr {e : Expr} {σ : Env} {w t : Term} :
      ValidEnv (e.freeVars db.env) db σ → w ∈ db.terms →
      Expr.MEval db (db.env ++ σ) e t → MCong (db.addTerm t) w t →
      MValidSubst db (.expr e) σ
  | eq {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term} :
      ValidEnv (e₁.freeVars db.env ∪ e₂.freeVars db.env) db σ → w ∈ db.terms →
      Expr.MEval db (db.env ++ σ) e₁ t₁ → Expr.MEval db (db.env ++ σ) e₂ t₂ →
      MCong ((db.addTerm t₁).addTerm t₂) w t₁ → MCong ((db.addTerm t₁).addTerm t₂) t₁ t₂ →
      MValidSubst db (.eq e₁ e₂) σ
  /-- The row atom: `f`'s row at a key class congruent to `as`, with value columns
  congruent to `vs`. **This is the only read in the semantics.**

  Its key premise is `Database.Out`'s and its value premise is the same comparison applied
  to the value columns, both read in the database **extended with the operands**, as the
  `expr` and `eq` cases read theirs. `ValidSubst.values` says what that extension buys and
  why it is conservative rather than permissive.

  There is no `w ∈ db.terms` witness: the row itself is what forbids matching something
  the database does not hold. -/
  | values {vs : List Expr} {f : FnName} {as : List Expr} {σ : Env}
      {us ts ws bs : List Term} :
      ValidEnv (Expr.freeVarsList vs db.env ∪ Expr.freeVarsList as db.env) db σ →
      Expr.MEvalList db (db.env ++ σ) vs us → Expr.MEvalList db (db.env ++ σ) as ts →
      MCongList ((db.addTerms ts).addTerms us) ts bs →
      MCongList ((db.addTerms ts).addTerms us) us ws → Row.mk f bs ws ∈ db.rows →
      MValidSubst db (.values vs f as) σ

/-- `ValidQuerySubst`, over `MValidSubst`. -/
def MValidQuerySubst (db : Database) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (MValidSubst db) q σs ∧ Env.UnionAll σs σ

/-- The databases one rule contributes, one per substitution satisfying its query. -/
def RuleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ d', MValidQuerySubst db r.query σ ∧
        Database.ActionsStep { db with env := db.env ++ σ } r.actions d' ∧
        d = { d' with env := db.env, rules := db.rules }}

/-- Every rule fires on every substitution satisfying its query in the pre-state, and
the results are unioned in. `runRules`, with rows. -/
def RunRules (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ db.rules, d ∈ RuleResults db r}

/-- One round: fire every rule, then take any number of merge steps.

Merges are **deferred**, which this records: rule heads stage rows and the merge phase
runs once every rule has been searched, so no rule sees another's merged value within a
round.

The phase is not required to *saturate*, so this relation reaches every state egglog
reaches plus partially merged ones. Saturation is instead a hypothesis of the theorems
that need it — simulation, and matching egglog's row counts. `MERGE.md`, "Saturation is
a hypothesis, not a step". -/
def RunStep (db db' : Database) : Prop := MergeClosure (RunRules db) db'

/-- `stepCmd`, relationally.

`action` resolves collisions before the next command: a top-level `set` is its own merge
phase, so `(set (f) 1) (set (f) 2)` on a `:merge (max old new)` function leaves one row
holding `2` with no `(run)` anywhere. See `MERGE.md`, "The merge phase runs between
commands". -/
inductive CmdStep : Database → Cmd → Database → Prop where
  | action {db d db' : Database} {a : Action} :
      Database.ActionStep db a d → MergeClosure d db' → CmdStep db (.action a) db'
  | rule {db : Database} {r : Rule} :
      CmdStep db (.rule r) { db with rules := insert r db.rules }
  | run {db db' : Database} : RunStep db db' → CmdStep db .run db'
  | decl {db : Database} {f : FnName} {d : FnDecl} :
      CmdStep db (.decl f d) { db with sig := Function.update db.sig f (some d) }

/-- `runProgram`, relationally. -/
inductive ProgramStep : Database → Program → Database → Prop where
  | nil {db : Database} : ProgramStep db [] db
  | cons {db d d' : Database} {c : Cmd} {cs : Program} :
      CmdStep db c d → ProgramStep d cs d' → ProgramStep db (c :: cs) d'

end Egglog
