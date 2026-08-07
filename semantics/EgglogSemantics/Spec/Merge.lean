import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# `:merge` functions

M9. See `MERGE.md` for the design, what was rejected, and the open questions. Every
claim below about egglog's behaviour is sourced there.

The state gains a **row set**. A row `⟨f, args, out⟩` says the database records the
value columns `out` for `f` at `args`. For a constructor there is one value column and
it holds the application itself, so `Database` embeds by `Database.toM`.

Three things follow, and the first is the milestone:

* **Congruence is the functional dependency.** `MCong.fd` says two rows of one
  `.union` function whose keys are congruent have congruent outputs. At constructor
  rows — where `out = [.app f args]` — that *is* `Cong.congr`; at equal keys it is the
  functional dependency. There is no separate `congr` constructor.
  `Proofs/Merge.lean`'s `mcong_toM_iff` is the compatibility theorem.
* **A `:merge` body is an action list.** It writes rows to other tables — the
  union-find's merge `set`s the displaced parent edge — so `MergeStep` is a relation
  on *databases*, not a function combining two values, and merge closure is a phase
  of `RunStep` rather than a definition of "the value of a key".
* **Evaluation becomes a relation.** A non-constructor application in an action is a
  *lookup*, not a construction, and a key class can record several outputs. So
  `Expr.eval` is replaced by `Expr.MEval`, and everything downstream of it —
  actions, rule firing, `run` — is a relation too.

Nothing is ever removed, from any of `terms`, `rows` or `eqs`. Both colliding rows
survive a merge, which is what keeps the state monotone; the encoding depends on the
same property ("Nothing is ever removed from it, which lets proofs refer to terms after
they leave the e-graph").

The spec deliberately **over-approximates** egglog rather than matching it. A lookup
reads any recorded output, not the current one; a round takes any number of merge
steps, not all of them. The M11 safety theorem is an invariant over this relation, and
an invariant needs neither termination nor confluence — see `MERGE.md`,
"Over-approximating egglog", and `Proofs/Merge.lean`'s `invariant_of_step`.
-/

namespace Egglog
/-! ### Rows -/
/-- One tuple of one function's table: `fn args… ↦ out…`.

`out` is a *list*, one entry per value column. egglog's tables are multi-column and the
encoding depends on it — `@UF_<Sort>` carries a parent *and* a proof, `@<C>View` an
e-class and a proof — so M11 cannot be stated without this. A constructor has exactly
one value column. -/
@[ext]
structure Row where
  fn : FnName
  args : List Term
  out : List Term
  deriving DecidableEq

/-- The constructor rows of `t`: one per application among its subterms, each mapping
its own children to itself.

Only a *constructor* application ever occurs inside a `Term` — `Expr.MEval` resolves a
`:merge` function's application to its recorded output — so this needs no signature. -/
def Term.ctorRows (t : Term) : Set Row :=
  {r | r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ t.subterms}

/-! ### The M9 command language

`Rule` and `Cmd` carry `Action`, which has no `set`, so an M9 program needs its own.
`MRule`/`MCmd`/`MProgram` are those with `RowAction` in its place, and `Cmd.toMCmd`
embeds the old language. Nothing else differs; when `RowAction` replaces `Action`
outright (`MERGE.md`, "One action language or two") these collapse into `Rule`/`Cmd`. -/
/-- A rule whose head may write rows. -/
structure MRule where
  query : Query
  actions : List RowAction

/-- A top-level command over `RowAction`. -/
inductive MCmd where
  | action : RowAction → MCmd
  | rule : MRule → MCmd
  | run : MCmd
  | decl : FnName → FnDecl → MCmd

/-- An M9 program. -/
abbrev MProgram := List MCmd

/-- The old rule language, embedded. -/
def Rule.toMRule (r : Rule) : MRule := ⟨r.query, r.actions.map Action.toRowAction⟩

/-- The old command language, embedded. -/
def Cmd.toMCmd : Cmd → MCmd
  | .action a => .action a.toRowAction
  | .rule r => .rule r.toMRule
  | .run => .run
  | .decl f d => .decl f d

/-- Egglog's global state, with rows.

`terms`, `eqs`, `env` and `rules` are `Database`'s. `rows` is new, and `terms` is
*not* derivable from it: a literal is a term with no row, and `MCong.refl`'s side
condition reads `terms`. -/
@[ext]
structure MDatabase where
  /-- The declared functions. Read by `MCong.fd`, `Expr.MEval` and `MergeStep`. -/
  sig : Signature
  /-- The terms the database holds. Subterm-closed under `WF`. -/
  terms : Set Term
  /-- The *asserted* rows. A merge never removes one; it adds the combined row beside
  the two it merged. -/
  rows : Set Row
  /-- The *asserted* equalities, from `union` actions. -/
  eqs : Set (Term × Term)
  /-- Global bindings, extended by a top-level `let`. -/
  env : Env
  /-- The rules, run by `MCmd.run`. -/
  rules : Set MRule

namespace MDatabase
/-- The initial database. -/
def empty : MDatabase where
  sig := fun _ => none
  terms := ∅
  rows := ∅
  eqs := ∅
  env := []
  rules := ∅

/-- Build `t`: insert it, its subterms, and the constructor row of each application
among them.

This is `Database.addTerm` plus the rows, and it is the only thing that writes a
constructor row — which is what makes `Database.toM` an embedding rather than a
projection. -/
def build (t : Term) (db : MDatabase) : MDatabase :=
  { db with terms := db.terms ∪ t.subterms, rows := db.rows ∪ t.ctorRows }

/-- `build` over a list, left to right. -/
def buildAll (ts : List Term) (db : MDatabase) : MDatabase :=
  ts.foldl (fun d t => d.build t) db

/-- Assert one row, changing nothing else. -/
def insertRow (r : Row) (db : MDatabase) : MDatabase :=
  { db with rows := insert r db.rows }

/-- `(set (f as…) v)`: build the operands, then assert the row.

Only *asserted*. A collision with a congruent key is resolved by `MCong.fd` or by
`MergeStep`, neither of which removes this row — which is what keeps the state
monotone under a merge. -/
def addRow (f : FnName) (as : List Term) (vs : List Term) (db : MDatabase) : MDatabase :=
  ((db.buildAll as).buildAll vs).insertRow ⟨f, as, vs⟩

/-- Assert `a = b`, building both terms. -/
def addEq (a b : Term) (db : MDatabase) : MDatabase :=
  { (db.build a).build b with eqs := insert (a, b) db.eqs }

/-- Union in a whole family of databases at once, as `Database.sUnion`. -/
def sUnion (db : MDatabase) (S : Set MDatabase) : MDatabase :=
  { db with
    terms := db.terms ∪ ⋃ d ∈ S, d.terms
    rows := db.rows ∪ ⋃ d ∈ S, d.rows
    eqs := db.eqs ∪ ⋃ d ∈ S, d.eqs }

/-- `d₁`'s terms, rows and asserted equalities are among `d₂`'s.

The `rows` field is the whole monotonicity story: a merge adds a row rather than
overwriting one, so `MergeStep` preserves this and every M2–M8 lemma resting on
`Database.Contained` transports. -/
structure Contained (d₁ d₂ : MDatabase) : Prop where
  terms : d₁.terms ⊆ d₂.terms
  rows : d₁.rows ⊆ d₂.rows
  eqs : d₁.eqs ⊆ d₂.eqs

/-- The database invariants: `Database.WF` plus that a row talks about terms the
database holds.

A row's key is *not* required to be a term. `.app g as` for a `:merge` function `g` is
a key, not a value — it has no e-class and cannot be unioned — and with one untyped
`Term` there is nothing to stop it being written as a term except this. See
`MERGE.md`, "Base sorts". -/
structure WF (db : MDatabase) : Prop where
  subtermClosed : ∀ t ∈ db.terms, t.subterms ⊆ db.terms
  eqsInTerms : ∀ p ∈ db.eqs, p.1 ∈ db.terms ∧ p.2 ∈ db.terms
  envInTerms : ∀ b ∈ db.env, b.2 ∈ db.terms
  rowsInTerms : ∀ r ∈ db.rows, (∀ a ∈ r.args, a ∈ db.terms) ∧ ∀ v ∈ r.out, v ∈ db.terms

/-- Every function is used at its declared key and value arities. Separate from `WF`
because nothing in the semantics needs it — it is the decidable half of the sort
discipline `MERGE.md` defers. -/
def ArityOk (db : MDatabase) : Prop :=
  ∀ r ∈ db.rows, ∀ d, db.sig r.fn = some d →
    r.args.length = d.arity ∧ r.out.length = d.outArity

end MDatabase
/-- Every application `db` holds becomes its own row, `f as… ↦ (f as…)`.

This is `PLAN.md`'s "for a constructor the invariant is `out = .app f args`", read as
an embedding rather than as an invariant to maintain. `mcong_toM_iff` — that `MCong`
on the image is `Cong` on the original — is what licenses replacing `Database` by
`MDatabase` outright. -/
def Database.toM (db : Database) : MDatabase where
  sig := db.sig
  terms := db.terms
  rows := {r | r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms}
  eqs := db.eqs
  env := db.env
  rules := Rule.toMRule '' db.rules

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
equates its outputs positionally. Nothing in the encoding needs that: a `.union`
function is a source-program constructor, which has one value column, and the encoded
program has **no** `.union` function at all. `@AddView` resolves congruence through its
merge *body* (`set (@UF_Math …)`) and the `@UF` table, not through `fd`. So in the
target, congruence is entirely simulated — see `MERGE.md`, "Multi-column outputs". -/
inductive MCong (db : MDatabase) : Term → Term → Prop where
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
inductive MCongList (db : MDatabase) : List Term → List Term → Prop where
  | nil : MCongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      MCong db a b → MCongList db as bs → MCongList db (a :: as) (b :: bs)

end

namespace MCong
variable {db : MDatabase}

/-- `MCong db` is an equivalence on `db.terms`, as `Cong.setoid`. Its quotient is the
e-class set, and the bridge to M11: an e-class here is an `@UF` leader there. -/
def setoid (db : MDatabase) : Setoid {t : Term // t ∈ db.terms} where
  r a b := MCong db a.val b.val
  iseqv := ⟨fun a => .refl a.property, .symm, .trans⟩

end MCong
/-! ### Reading a table

Keys are compared up to congruence, so a lookup searches the key's class rather than
the row set. `Out` is the relation; `Greatest` is the single value `PLAN.md` calls the
merge-fold. -/
namespace MDatabase
/-- `v` is an output `db` records for `f` at the class of the key `as`.

Quantifying over congruent keys here rather than re-keying rows is what lets
`MergeStep` write the combined row at one key only and still be seen from the other,
and it is why the row set never needs the re-canonicalization egglog's rebuild does.
Monotone in `Contained`, because `MCongList` is. -/
def Out (db : MDatabase) (f : FnName) (as : List Term) (vs : List Term) : Prop :=
  ∃ bs, MCongList db as bs ∧ Row.mk f bs vs ∈ db.rows

/-- The value a *join* merge settles on at the class of `as`: the `le`-greatest
recorded output.

**Not** what `Expr.MEval` reads — that reads `Out`, and `MERGE.md`'s "Why the reader
over-approximates" says why. `Current` exists only when `f`'s merge really is a join
for `le`: under `:merge old` every recorded output absorbs and it is not unique, and
under `:merge new` none does and it does not exist. Both are common, and egglog
settles them by insertion order, which a `Set Row` cannot express.

It is here for the two places that need to match egglog's answer rather than
over-approximate it: differential testing, and M11's simulation theorem.

This is also `PLAN.md`'s "merge-fold over all congruent asserted rows", restated as a
maximum. A fold over a set is well defined only once the merge is proved commutative
*and* associative; a greatest element is unique from antisymmetry alone
(`current_unique`), and for a `SemilatticeSup` merge it is what the fold computes.
`le` is a parameter rather than an instance because the order is per function — one
`Term` type carries every sort — and it orders whole rows, since a multi-column merge
can settle its columns jointly. -/
def Current (db : MDatabase) (le : List Term → List Term → Prop) (f : FnName)
    (as : List Term) (vs : List Term) : Prop :=
  db.Out f as vs ∧ ∀ ws, db.Out f as ws → le ws vs

end MDatabase
/-! ### The term order

Two jobs, deliberately one definition.

**A spec primitive.** `ordering-min`/`ordering-max` are part of the *program* the
encoding writes, not an implementation detail: the union-find's merge body is literally
`(set (@UF_<S> (ordering-max old new)) (values (ordering-min old new) ()))`. M11 cannot
state `encode` without them.

**An implementation tie-break.** `MergeStep` is non-deterministic in which collision
fires; an interpreter has to pick one, and ordering the candidates by this makes the
choice deterministic. It is also where a termination witness comes from, since a merge
that keeps the smaller side descends.

egglog orders by insertion instead, so it picks a different class *representative*.
That is invisible to `(print-size)`, which counts one row per class, so differential
testing is unaffected. -/
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
  deriving DecidableEq, Repr

/-- The reserved names. A user function of the same name is shadowed, as in egglog. -/
def Prim.ofName : FnName → Option Prim
  | "ordering-min" => some .orderingMin
  | "ordering-max" => some .orderingMax
  | _ => none

/-- A primitive's meaning. `none` for the wrong arity. -/
def Prim.apply : Prim → List Term → Option Term
  | .orderingMin, [s, t] => some (Term.orderingMin s t)
  | .orderingMax, [s, t] => some (Term.orderingMax s t)
  | _, _ => none
/-! ### Evaluation

`Expr.eval` is a function of the environment alone, which is exactly right while every
function is a constructor: a term is its own identity, so building one reads nothing.
A `:merge` function's application is instead a **lookup**, and egglog has no
`:default` to fall back on (removed in #461) — a missing row is a panic in an action
and simply no match in a body. So evaluation reads the database, and since a key class
may record several outputs it is a relation. -/
mutual

/-- The value(s) an expression denotes.

`ctor` builds and `lookup` reads, split on the signature; `prim` resolves a reserved
name first, as egglog's primitive table does. A `Term` therefore contains only
constructor applications, which is what lets `Term.ctorRows` need no signature.

`lookup` reads `Out` — *any* recorded output — and not `Current`. Two reasons.
`Current` frequently does not exist: `:merge old` makes every output absorb so it is
not unique, `:merge new` makes none absorb so there is none, and both are common
(the encoding's own `@<Sort>Proof` is `:merge old`). And the over-approximation is
sound for what M11 needs: term and proof rows are append-only, so every recorded proof
is valid and stays valid, and reading a stale one yields a *different proof of the same
fact*, never an invalid one. The safety theorem therefore needs no well-behavedness
hypothesis at all.

Partiality that was `none` in `Expr.eval` is now "no `t` related". `Scope.lean`'s
"a well-scoped program never gets stuck" therefore weakens: staying unstuck now also
needs every lookup to hit, which is not a scope property and is egglog's `Fail` panic
rather than anything a static check could rule out. -/
inductive Expr.MEval (db : MDatabase) (σ : Env) : Expr → Term → Prop where
  | lit {l : Lit} : Expr.MEval db σ (.lit l) (.lit l)
  | var {v : Var} {t : Term} : Env.lookup v σ = some t → Expr.MEval db σ (.var v) t
  | ctor {f : FnName} {args : List Expr} {ts : List Term} :
      Prim.ofName f = none → db.sig.mergeOf f = MergeSpec.union →
      Expr.MEvalList db σ args ts → Expr.MEval db σ (.app f args) (.app f ts)
  | lookup {f : FnName} {args : List Expr} {ts : List Term} {v : Term} :
      Prim.ofName f = none → db.sig.mergeOf f ≠ MergeSpec.union →
      Expr.MEvalList db σ args ts → db.Out f ts [v] → Expr.MEval db σ (.app f args) v
  | prim {f : FnName} {p : Prim} {args : List Expr} {ts : List Term} {v : Term} :
      Prim.ofName f = some p → Expr.MEvalList db σ args ts → p.apply ts = some v →
      Expr.MEval db σ (.app f args) v

/-- `Expr.MEval` over an argument list. -/
inductive Expr.MEvalList (db : MDatabase) (σ : Env) : List Expr → List Term → Prop where
  | nil : Expr.MEvalList db σ [] []
  | cons {e : Expr} {es : List Expr} {t : Term} {ts : List Term} :
      Expr.MEval db σ e t → Expr.MEvalList db σ es ts →
      Expr.MEvalList db σ (e :: es) (t :: ts)

end

/-! ### Actions that write rows -/
/-- One row action.

The three inherited cases are `evalAction`'s, read relationally. `set` is the new one,
and it only ever adds. egglog restricts a `:merge` body to exactly `let`, `set` and
`union` (`MergeLegal`); a rule head has these plus `expr` and more. -/
inductive MDatabase.RowActionStep : MDatabase → RowAction → MDatabase → Prop where
  | expr {db : MDatabase} {e : Expr} {t : Term} :
      Expr.MEval db db.env e t → MDatabase.RowActionStep db (.expr e) (db.build t)
  | letBind {db : MDatabase} {v : Var} {e : Expr} {t : Term} :
      Expr.MEval db db.env e t →
      MDatabase.RowActionStep db (.letBind v e)
        { db.build t with env := (v, t) :: db.env }
  | union {db : MDatabase} {e₁ e₂ : Expr} {t₁ t₂ : Term} :
      Expr.MEval db db.env e₁ t₁ → Expr.MEval db db.env e₂ t₂ →
      MDatabase.RowActionStep db (.union e₁ e₂) (db.addEq t₁ t₂)
  | set {db : MDatabase} {f : FnName} {args : List Expr} {out : Expr}
      {ts : List Term} {v : Term} :
      Expr.MEvalList db db.env args ts → Expr.MEval db db.env out v →
      MDatabase.RowActionStep db (.set f args out) (db.addRow f ts [v])

/-- A sequence of row actions, run in order. -/
inductive MDatabase.RowActionsStep : MDatabase → List RowAction → MDatabase → Prop where
  | nil {db : MDatabase} : MDatabase.RowActionsStep db [] db
  | cons {db d d' : MDatabase} {a : RowAction} {as : List RowAction} :
      MDatabase.RowActionStep db a d → MDatabase.RowActionsStep d as d' →
      MDatabase.RowActionsStep db (a :: as) d'

/-- The actions egglog admits inside a `:merge` body: `let`, `set` and `union` only.
Anything else is rejected at lowering. -/
def RowAction.MergeLegal : RowAction → Prop
  | .expr _ => False
  | .letBind _ _ => True
  | .union _ _ => True
  | .set _ _ _ => True

/-! ### The merge step -/
/-- The environment a `:merge` body runs in.

A merge body sees nothing but the two colliding rows' outputs and its own `let`s —
globals are desugared to nullary functions before it, so they are lookups rather than
environment reads.

egglog names these `old`/`new` for a single-output function and `old0`/`new0`/`old1`/…
per value column for a tuple output. *Every* column is bound, not just the one being
computed: `MergeFn::OldCol`/`NewCol` exist precisely because "a column's merge may
reference any output column of the old row". -/
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
own, which is the whole content of the union-find's `:merge`. A value combiner
`Term → Term → Term` could not express it.

Nothing is removed — `db` is `Contained` in the result. The two colliding rows are
still there afterwards, which keeps every monotonicity lemma alive and leaves the old
rows' proofs available for the `@MergeRow` that names them.

**There is no `a ≠ b` guard, deliberately.** `MCongList` is reflexive, so a row
collides with *itself*. An earlier draft excluded that, reasoning that egglog merges a
retained row against an incoming staged one and so never self-merges. But excluding it
is an **under**-approximation, and that is the unsafe direction: it lets egglog reach
states the model never checks, so a safety invariant proved here would not transfer.
Without the guard the model covers egglog either way — where egglog has
`:internal-identity-vals` on it skips a re-`set` of an equal value and we fire anyway;
where the flag is off egglog fires on the re-`set` and we fire spontaneously. The
safety theorem consequently needs **no** scope condition on the signature: no
`merge (x, x) = x`, no identity-guardedness.

Two consequences, both intended:

* For an idempotent merge nothing diverges, only finitely many *vacuous* rows appear.
  The union-find's body on a self-collision is
  `(set (@UF_<S> (ordering-max p p)) (values (ordering-min p p) ()))` — a reflexive
  self-edge, from which `MCong` derives only `p = p`, already true by `refl`. In proof
  mode it writes extra proofs of `p = p`, which are *valid*, so the invariant is
  untouched. They are not even observable: egglog's `print-size` filters
  `internal_hidden || internal_let` and reports a view under its `term_constructor`
  name, which is why `files.rs` shares one snapshot between normal and term-encoded
  runs, so `@UF_*` and `@*View` never appear in a diff.
* For `:merge (+ old new)` the model **diverges**: the self-collision derives `2v`,
  `3v`, … forever, where egglog with a single `set` merges nothing. That is the
  intended reading and not a defect. Such a program's egglog result is
  insertion-order-dependent, so there is no fixpoint for a semantics to denote, and
  diverging is more honest than inventing an answer. Same reading as the
  order-dependence below.

This works only because `MergeSaturated` was corrected to "no step *changes* anything";
the two changes are coupled, and the note there says why.

The combined row is written at the key `as` only; `Out` reads it from `bs` too.

The two rows are premises in both orders, so a non-commutative merge relates `db` to
two different results. That is deliberate: it is the relational reading of what egglog
calls user-visible undefined behaviour for a non-monotone merge.

**The body runs once, before any column is computed** — `RowActionsStep` produces `d`
and every column of `res` is then evaluated in `d`. That is egglog's order, not a
choice: "Run the block's side effects once, before computing the merged values"
(`egglog-bridge/src/lib.rs:1433`). `res` is one expression per value column. -/
inductive MergeStep : MDatabase → MDatabase → Prop where
  | collide {db d : MDatabase} {f : FnName} {as bs a b vs : List Term}
      {body : List RowAction} {res : List Expr} :
      ⟨f, as, a⟩ ∈ db.rows → ⟨f, bs, b⟩ ∈ db.rows → MCongList db as bs →
      db.sig.mergeOf f = MergeSpec.merge body res →
      MDatabase.RowActionsStep { db with env := mergeEnv a b } body d →
      Expr.MEvalList d d.env res vs →
      MergeStep db { d.addRow f as vs with env := db.env, rules := db.rules }

/-- Merge closure.

A relation, not a fixpoint function: a merge body can build terms, so the candidate
universe grows as the closure runs and there is no measure to recurse on. This is
`PLAN.md` M9's "no termination claim", and it is what separates the merge closure from
the congruence closure — `Impl/Closure.lean`'s `closure` stays well-founded because
`terms` and `rows` are fixed while it runs. -/
def MergeClosure : MDatabase → MDatabase → Prop := Relation.ReflTransGen MergeStep

/-- No merge collision *changes* anything. egglog's `merge_all` runs to exactly this.

Stated as "every step is the identity" and not as "no step applies". The latter is
**unsatisfiable** here, for two independent reasons: nothing removes rows, so two
colliding rows are still present after the step and `MergeStep` applies again forever;
and with the `a ≠ b` guard gone every row collides with itself, so a step always
applies. That is why `RunStep` does not require saturation — see `MERGE.md`,
"Saturation is a hypothesis, not a step".

This form is what makes dropping the guard workable, so the two are coupled. An
`ordering-min` self-collision re-derives a row already present, so `db' = db` and
saturation still holds; a `+` self-collision derives a genuinely new row every time and
correctly never saturates. -/
def MergeSaturated (db : MDatabase) : Prop := ∀ db', MergeStep db db' → db' = db

/-- `:no-merge` is respected: no two rows of a `.noMerge` function collide on
congruent keys with different outputs.

egglog raises `PanicError` when this fails and keeps the old row, so it is a side
condition rather than a step. Nothing in the semantics consumes it; having it stated
is what stops `.noMerge` silently meaning "keep the old value". -/
def MDatabase.NoMergeOk (db : MDatabase) : Prop :=
  ∀ f as bs (a b : List Term), Row.mk f as a ∈ db.rows → Row.mk f bs b ∈ db.rows →
    MCongList db as bs → db.sig.mergeOf f = MergeSpec.noMerge → a = b

/-! ### E-matching and running

`Match.lean` and `Step.lean` ported by replacing `Cong` with `MCong` and `Expr.eval`
with `Expr.MEval`. The one non-mechanical change is `RunStep`: merge closure is a
*phase* of a round, because it is a state change where congruence closure is only a
relation. -/
/-- `ValidEnv`, over a term set. Identical to `Spec/Match.lean`'s, which is pinned to
`Database`; the two collapse when `MDatabase` replaces `Database`. -/
def MValidEnv (vars : List Var) (db : MDatabase) (σ : Env) : Prop :=
  (Env.dom σ).Perm vars ∧ ∀ b ∈ σ, b.2 ∈ db.terms

/-- `ValidSubst`, over `MCong`. The witness formulation is unchanged. -/
inductive MValidSubst (db : MDatabase) : Pattern → Env → Prop where
  | expr {e : Expr} {σ : Env} {w t : Term} :
      MValidEnv (e.freeVars db.env) db σ → w ∈ db.terms →
      Expr.MEval db (db.env ++ σ) e t → MCong (db.build t) w t →
      MValidSubst db (.expr e) σ
  | eq {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term} :
      MValidEnv (e₁.freeVars db.env ∪ e₂.freeVars db.env) db σ → w ∈ db.terms →
      Expr.MEval db (db.env ++ σ) e₁ t₁ → Expr.MEval db (db.env ++ σ) e₂ t₂ →
      MCong ((db.build t₁).build t₂) w t₁ → MCong ((db.build t₁).build t₂) t₁ t₂ →
      MValidSubst db (.eq e₁ e₂) σ

/-- `ValidQuerySubst`, over `MValidSubst`. -/
def MValidQuerySubst (db : MDatabase) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (MValidSubst db) q σs ∧ Env.UnionAll σs σ

/-- The databases one rule contributes, one per substitution satisfying its query. -/
def MRuleResults (db : MDatabase) (r : MRule) : Set MDatabase :=
  {d | ∃ σ d', MValidQuerySubst db r.query σ ∧
        MDatabase.RowActionsStep { db with env := db.env ++ σ } r.actions d' ∧
        d = { d' with env := db.env, rules := db.rules }}

/-- Every rule fires on every substitution satisfying its query in the pre-state, and
the results are unioned in. `runRules`, with rows. -/
def MRunRules (db : MDatabase) : MDatabase :=
  db.sUnion {d | ∃ r ∈ db.rules, d ∈ MRuleResults db r}

/-- One round: fire every rule, then take any number of merge steps.

Merges are **deferred**, which this records: rule heads stage rows and the merge phase
runs once every rule has been searched, so no rule sees another's merged value within a
round.

egglog additionally runs the merge phase *to a fixpoint*, and `RunStep` deliberately
does **not**. Requiring `MergeSaturated db'` would make the step relation empty for
every program with a real merge collision, and — more importantly — nothing that
matters needs it. The M11 safety theorem is an *invariant* over this relation
(`invariant_of_step`): it holds at every reachable state, so it needs neither
termination nor confluence, and a diverging run satisfies it throughout. Saturation is
a hypothesis for the theorems that do need it, namely simulation and matching egglog's
row counts.

So this relation over-approximates: it reaches every state egglog reaches, plus
partially merged ones. `MERGE.md`, "Over-approximating egglog", says why that is the
right trade. -/
def RunStep (db db' : MDatabase) : Prop := MergeClosure (MRunRules db) db'

/-- `stepCmd`, relationally. -/
inductive CmdStep : MDatabase → MCmd → MDatabase → Prop where
  | action {db d : MDatabase} {a : RowAction} :
      MDatabase.RowActionStep db a d → CmdStep db (.action a) d
  | rule {db : MDatabase} {r : MRule} :
      CmdStep db (.rule r) { db with rules := insert r db.rules }
  | run {db db' : MDatabase} : RunStep db db' → CmdStep db .run db'
  | decl {db : MDatabase} {f : FnName} {d : FnDecl} :
      CmdStep db (.decl f d) { db with sig := Function.update db.sig f (some d) }

/-- `runProgram`, relationally. -/
inductive ProgramStep : MDatabase → MProgram → MDatabase → Prop where
  | nil {db : MDatabase} : ProgramStep db [] db
  | cons {db d d' : MDatabase} {c : MCmd} {cs : MProgram} :
      CmdStep db c d → ProgramStep d cs d' → ProgramStep db (c :: cs) d'

end Egglog
