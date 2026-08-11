# `:merge` functions (M9)

Generalizes the semantics from "every function is a constructor and congruence is `Cong`" to "a
function carries a `:merge`". Revises `PLAN.md`'s M9 section; where they disagree this is current.
Facts about egglog are cited to the Rust; guesses are flagged **[guess]**.

The state gains a **row set**: `⟨f, args, out⟩` says `f` records value columns `out` at `args`;
for a constructor there is one column holding the application itself. What that adds to
congruence is the **functional dependency**, and it is a *theorem* about `Cong` —
`Proofs/Congruence.lean`'s `Cong.fd` — rather than a second relation, so `Spec/` keeps one
congruence. A `:merge` body is an action list, so resolving a collision is a step relation on
databases, `MergeStep`, not a value combiner; command stepping becomes a relation with it. That
last consequence was not in `PLAN.md`.

**Two shapes this file argued for, and their fates.** Congruence as an inductive `fd` rule over a
second relation `MCong`, with a compatibility theorem `mcong_iff_cong` — **retired**, in favour
of `Cong.fd`. And evaluation as a relation `Expr.MEval`, because a non-constructor application was
a lookup — **retired** when reading became the query atom `Pattern.values`, after which
`Expr.eval` needs nothing of the database but its signature and is a function again. The sections
below are the design record; where they reason about `MCong` or `Expr.MEval`, the reasoning is
about a shape the development no longer has, and each such section says so.

**Status.** The `execM` refinement chain ending in `execM_contained`, and `execM_reachable`, are
proved. `Proofs/Merge.lean` has five `sorry`s: `MergeStep.diamond_of_join`,
`RunStep.unique_of_confluent`, `execM_current_of_lattice`, `mergeRound_closure`,
`FDatabase.mergeRound_rowCount`. **All five** carry a recorded defect *in the statement* — false as
written, or a hypothesis that is self-contradictory or too weak — at the point where they are
stated, with compiling witnesses in `Proofs/Counterexamples.lean` and `Proofs/Lattice.lean`.
`make lean-difftest` is **166 passed / 0 failed / 0 skipped**, 66 of those curated `:merge` cases.

## The framing: invariants over a step relation

M11's headline theorem — *every proof row the encoding writes is accepted by the checker* — is an
**invariant** over the step relation, and that shapes everything below:

```lean
theorem invariant_of_step {I : Database → Prop}
    (hstep : ∀ db c db', I db → CmdStep db c db' → I db')
    (hinit : I db) (h : ProgramStep db p db') : I db'
```

Four lines, proved. An invariant needs **neither termination nor confluence**: it holds at every
reachable state, so a diverging run satisfies it throughout and so does a differently-ordered one.

So the spec is **over-approximating**, and matching egglog exactly is a hypothesis on the theorems
that want it. A lookup reads *any* recorded output; a round takes *any number* of merge steps; a
row collides with itself. The spec reaches every state egglog reaches, plus some it does not.
Over-approximation must be **unconditional**: any under-approximation is a hole, since egglog then
reaches a state the model never checks and the invariant does not transfer. That criterion removed
the last side condition, the `a ≠ b` collision guard. Two things make this sound rather than
merely convenient.

* **Append-only rows.** In `Spec/`, term and proof rows are never deleted, so every recorded proof
  is valid and *stays* valid: a stale one is a different proof of the same fact, never an invalid
  one. The safety theorem needs no well-behavedness hypothesis at all.
* **Order-dependent merges are the user's fault.** A merge that is not a lattice join has no
  order-independent answer; egglog calls that "user-visible undefined behavior"
  (`egglog-backend-trait/src/lib.rs:46-48`) and documents that a merge must define a lattice
  (`src/ast/mod.rs:803-808`) without ever checking it.

Differential testing and M11's simulation theorem, the two places that *do* need to match egglog,
take `MergeSaturated` and a join condition as hypotheses.

## Representation

The M9 state is `Database` itself, which gained `rows : Set Row` beside `sig`, `terms`, `eqs`,
`env`, `rules`; `Row` is `⟨fn, args, out⟩` with `out : List Term`, one entry per value column.
There is no separate `MDatabase` and no `Database.toM`: an earlier draft had both, which kept the
compatibility theorem a statement relating two things rather than an assertion that a refactor was
safe; merging them turned a statement relating two state types into one relating two relations
over the same state — which is what made it possible to then delete the second relation outright.

`terms` is **not** derivable from `rows` — a literal is a term with no row, and `Cong.refl`'s
side condition, what makes the e-matching witness bite, reads `terms`. `eqs` stays because a
`union` relates two arbitrary terms and is not a row. `addTerm` writes a term's constructor rows,
`{r | r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ t.subterms}`; `Term.ctorRows` needs no
signature because a `Term` only ever contains *constructor* applications — `Expr.eval` builds only
at a declared constructor, so `(g 1)` never survives into a term. That invariant
(`Database.CtorTerms`) carries weight; see "Constraint (5)" for where it is fragile.

## Congruence is the functional dependency

This started as a second relation. `MCong` was `Cong` with `congr` deleted and an `fd`
constructor in its place — two rows of one function with congruent keys, outputs equated column by
column, guarded on the function being a constructor — plus a compatibility theorem
`mcong_iff_cong` licensing the transport of every M2–M8 result. **That is retired.** The same fact
is now `Proofs/Congruence.lean`'s `Cong.fd`:

```lean
theorem fd {f : FnName} {as bs a b : List Term} {x y : Term}
    (hrow : ∀ r ∈ db.rows, db.sig.IsCtor r.fn →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    (hra : Row.mk f as a ∈ db.rows) (hrb : Row.mk f bs b ∈ db.rows)
    (hu : db.sig.IsCtor f) (hl : CongList db as bs) (hxy : (x, y) ∈ a.zip b) :
    Cong db x y
```

Three readings, as before: constructor rows with congruent keys → `Cong.congr`; with *equal* keys
→ `Cong.refl` on an application; in general → "one key, one output". The `zip` premise makes it
per *column*.

**A theorem is strictly cheaper than a rule was.** `fd`'s only hypothesis is `hrow`, the shape of
a constructor's rows — no `Database.CtorRows`, no `CtorTerms`, no `RowsComplete`, all of which
`mcong_iff_cong` needed. And it costs nothing elsewhere: `Cong` reads neither `rows` nor `sig`, so
the congruence closure `Impl/Closure.lean` computes is unchanged whatever the row set holds, and no
declaration can take a derivation away.

**And it is now discharged, not just assumed.** `Database.CtorRows.fd_hyp` turns `CtorRows`
into `hrow`, and `ProgramStep.out_union_cong` chains it with `ProgramStep.ctorRows` to conclude
that at any state a constructor-fragment program reaches, a constructor's outputs at one key
class are congruent. Until those landed, no proof term ever discharged `hrow` and the argument
that `Spec/` needs no `fd` rule lived only in docstrings — `PLAN.md`, "`set` legality".

**It is not free.** `Action.SetLegal` is what keeps `hrow` true;
`Proofs/Counterexamples.lean`'s `setCtorProgram` — `(set (f) (c)) (set (f) (d))` on a declared
constructor `f` — is a reachable state where it fails, where the two rows say nothing, and which
egglog's front end rejects. That program is also the whole gap between the two relations:
`Cong ⊊ MCong`, and they agree pointwise exactly where `SetLegal` holds.

**Declaration is required** (`Signature.IsCtor` is `∃ d, sig f = some d ∧ d.merge = none`), so an
undeclared name is not a constructor and M0–M8 is the all-constructors case only for programs that
*declare* their constructors — which is what `Tests/Examples.lean` and `DiffTest.lean` now do, and
what egglog requires anyway. The hypothesis that carries it is a state invariant,
`Database.CtorFragment.terms`, and not a fact about the signature alone:
`Signature.AllConstructors` says nothing *is* a merge function, which does not imply that the
applications in `terms` are constructors'. `MergeStep.saturated_of_allConstructors` is the
step-side companion, also proved: with no `.merge` function there is no collision, so a round is
`RunRules` and nothing else. Together they say M9-on-constructors is M0–M8 unchanged, so all of
`Proofs/` transports.

A Lean trap that cost time twice: `obtain ⟨rfl, _⟩` on a row membership fails, because the row's
field appears under an unreduced projection (`{fn := f, args := as, out := a}.args`) and `subst`
then sees it occurring in its own definition. Route through a bridge lemma that is `Iff.rfl` but
*states* the reduced form — same class as `rw`-needs-a-bridge-lemma.

**A merge function's applications get no congruence at all.** `fd` requires a constructor: two
`@UF_Math` rows with congruent keys make their parents equal because the merge body says so, which
is a step, not by congruence. A constructor collision is the only one whose whole effect is an
equality between terms that already exist, hence the only one a relation can express. That is the
line the whole design is drawn along.

## Constraint (1): a `:merge` body is an action

**What egglog does.** The AST is `GenericMerge { actions: GenericActions, result: GenericExpr }`
(`egglog-ast/src/generic_ast.rs:45-57`); the declaration field is `merge: Option<GenericMerge<…>>`
and is *required* (`src/ast/parse.rs:585-593`). Parsing disambiguates syntactically — a list whose
head is itself a list is an action block, otherwise a bare result expression
(`src/ast/parse.rs:531-569`), so `:merge (max old new)` stays an expression. `:on_merge` was
removed and this replaced it (`CHANGELOG.md:178`, `:42-46`). The block admits **exactly `let`,
`set`, `union`**; anything else is rejected at lowering with "action `{other}` is not supported
inside a :merge block" (`src/lib.rs:1064-1067`). So `panic` and `delete` are *not* available, and
`set` into another table — or into the function's own (`src/lib.rs:1100-1106`) — is. There is a
user-facing test, `tests/merge-action-block.egg`; the union-find's block in `proof_encoding.md` is
ordinary surface syntax.

`MergeSpec.merge : List Action → List Expr → MergeSpec` carries the pair, one expression per value
column, and the merge is a relation on databases:

```lean
inductive MergeStep : Database → Database → Prop where
  | collide {db d f} {as bs a b vs : List Term} {body res} :
      ⟨f, as, a⟩ ∈ db.rows → ⟨f, bs, b⟩ ∈ db.rows → CongList db as bs →
      db.sig.mergeOf f = some (.merge body res) →
      evalActions { db with env := mergeEnv a b } body = some d →
      Expr.evalList d.sig res d.env = some vs →
      MergeStep db { d.addRow f as vs with env := db.env, rules := db.rules }
```

* **Nothing is removed** — `db.Contained` the result, both colliding rows survive. That keeps
  every monotonicity lemma alive and leaves the old rows' proofs available for the `@MergeRow`
  naming them. **No guard on the collision** either; see the section of that name.
* **The combined row is written at key `as` only.** Reads go through `Out`, which quantifies over
  congruent keys, so it is visible from `bs` too. This replaces egglog's rebuild-driven re-keying:
  keys are compared up to congruence rather than canonicalized.
* **The env is `mergeEnv a b` and nothing else** — the two outputs plus the body's `let`s. egglog
  binds `old`/`new` for a single-output function and `old0`/`new0`/`old1`/… per value column for a
  tuple output (`src/typechecking.rs:1066-1077`), and `mergeEnv` does both. *Every* column is
  bound, not just the one being computed: `MergeFn::OldCol`/`NewCol` exist precisely because "a
  column's merge may reference any output column of the old row". Globals desugar to nullary
  functions, so they are lookups, not environment reads.
* **The body runs once, before any column is computed** — `evalActions` produces `d` and every
  column of `res` is evaluated in `d`. egglog's order, not a choice: "Run the block's side effects
  once, before computing the merged values" (`egglog-bridge/src/lib.rs:1433`).
* **Both orders fire**, so a non-commutative merge relates `db` to two different results.

**Why not a value combiner.** `PLAN.md` proposed the observable value as a merge-fold over the
congruent asserted rows, no step at all. That dies here because **the union-find's merge is all
side effect**: its value output is `ordering-min old new`, which a fold gets right, but its `set`
of the displaced edge — the entire content of the union-find's transitivity — is invisible to any
fold over values, so path compression would have nothing to compress.

**One action language.** `Action` and `RowAction` were two types and are now one, forced by M11:
the encoding's rules write `(set (@AddView b a) (values rewrite_var ()))`, so `encode`'s target
language needs `set` in rule heads. Cost as estimated, ~24 match sites across 10 files; not
anticipated was that it drags the state with it, since `evalAction`'s `set` case has nowhere to put
a row unless `Database` has one. egglog restricts a `:merge` body to `let, set, union` while a rule
head also has `panic`, `delete`, `subsume`, `extract` and bare expressions. That difference is
recorded here rather than as a second type or a predicate — nothing in the model consumed the
predicate, since `MergeSpec.merge` already carries whatever body the declaration was given.

## Constraint (2): reading a table

`:default` was removed (`CHANGELOG.md:176`, #461), so a missing row behaves differently in the two
positions: in a **rule body** `(f x)` is not a lookup but a join atom (`src/core.rs:629-639`), so
no row means no match, silently; in a **rule action, top-level action or merge body** it *is* a
lookup, where a constructor mints a fresh e-class (`DefaultVal::FreshId`) and a custom function
panics (`DefaultVal::Fail`, `src/lib.rs:1122-1125`, `egglog-bridge/src/rule.rs:658-672`) —
`tests/merge_read.egg`.

**This section's conclusion is superseded.** It concluded that evaluation therefore reads the
database, and — since a key class may record several outputs — must be a *relation*
`Expr.MEval` with a `lookup` constructor reading `Database.Out`, dragging actions, rule firing and
`run` into relations with it. The model instead **forbids the lookup**: reading is the query atom
`Pattern.values` and nothing else (`PLAN.md`, "Reading is a query atom"), which is stricter than
egglog in three positions, each with a flat equivalent. So `Expr.eval` is a function of the
signature alone, and the whole `MEval` family is gone. What egglog does at a lookup, above, is
still the record of *why* the restriction is a restriction and not a simplification.

The step relations stayed relations, for an unrelated reason — the merge phase, not the reads. And
`Scope.lean` did weaken, though not in the way this section predicted: `programStep_isSome` needs
`Program.Evaluable` beside `WellScoped`, because `Expr.eval` returns `none` at a lookup and at a
mis-sorted primitive.

### Why the reader over-approximates

The one read that remains — the row atom, and `Database.Out` beneath it — takes *any* recorded
output rather than the current one, for two reasons.

**A "current value" usually does not exist.** Under `:merge old` (`merge a b = a`) every recorded
output absorbs, so a greatest element is not unique; under `:merge new` none absorbs, so there is
none. Both are ordinary: the encoding's own `(function @<Sort>Proof (<Sort>) @Proof :merge old)`
is the first, and egglog's tests use `:merge new` widely (`luminal-llama.egg`,
`factoring-multisets.egg`). egglog resolves both by *insertion order*, which a `Set Row` cannot
express and which the `Set` was chosen to avoid. **And over-approximating is sound for proof
soundness**, for the append-only reason above.

#### Why a maximum and not a fold

`Database.Current` survives as a derived definition,
`db.Out f as vs ∧ ∀ ws, db.Out f as ws → le ws vs`, used only by difftest and M11's simulation
theorem — never by evaluation. `PLAN.md` wanted the *fold* proved well defined "when the merge is a
semilattice join, using Mathlib's `SemilatticeSup`", but a fold over a set is well defined only
once the combiner is proved commutative and associative, whereas a greatest element is unique from
**antisymmetry alone** (`Database.current_unique`, three lines, discharged, no `Finset.fold`
argument anywhere), and for a `SemilatticeSup` merge the greatest element *is* what the fold
computes. `le` is a parameter rather than an instance because the order is per function — one
untyped `Term` carries every sort — and it orders whole rows, since a multi-column merge can
settle its columns jointly.

### Primitives without churning `Expr`

`ordering-min`/`ordering-max`/`min`/`max` are `Expr.app` of a *reserved name* resolved by
`Prim.ofName` ahead of the signature, not a new `Expr` constructor. It is what egglog does (a
primitive shares a namespace with user functions and shadows one of the same name), and a new
`Expr` constructor would make every existing `cases e` in `Proofs/Eval.lean`, `Proofs/Match.lean`
and `Proofs/Interp.lean` non-exhaustive, an error rather than a `sorry`. While two evaluators
coexisted, only one of them resolved reserved names, and `execM_reachable` carried a
`Program.NoPrim` hypothesis to keep them apart; with one evaluator that hypothesis is gone.

`min`/`max` are in `Prim.ofName` for the same reason, and the three things that went wrong before
they were — non-idempotent merging, a row set that squared per pass, and a rule reading a term
where egglog has a number — are under "What the widening and the composed interpreter found".

## The term order

One definition, two deliberately distinct jobs. **(a) A spec primitive**:
`ordering-min`/`ordering-max` are part of the *program* the encoding writes — the union-find's
merge body is literally `(set (@UF_<S> (ordering-max old new)) (values (ordering-min old new)
()))`, so M11 cannot state `encode` without them, and they are where a termination witness comes
from, since a merge that keeps the smaller side descends. **(b) An implementation tie-break**:
`MergeStep` is non-deterministic in which collision fires, and ordering candidates by `Term.blt` —
literals, then arity, then name, then lex, with `orderingMin`/`orderingMax` defined from it —
makes the interpreter's choice deterministic. **The spec stays non-deterministic**; this is an
`Impl/` choice only. Structural size before lexicographic, so "keep the smaller side" descends;
`Term.blt_linear` is proved, from `blt_asymm`/`blt_total`/`blt_trans`.

### The representative deviation

**`Term.blt` keeps a deterministic structural order and does not model egglog's allocation order.
That is a decision, not a defect, and the claim that used to sit here — "invisible to
`(print-size)`, so differential testing is unaffected" — is false.**

Scope, since it narrowed: this is about `ordering-min`/`ordering-max`, and *not* about which of two
colliding rows is `old`. That one is allocation order too, and `Impl/` does model it, by reading
`FDatabase.terms`' order — see "`old` is the row at the canonical key". The same repair is not
available here, because `Prim.apply` is `List Term → Option Term` and has no database to read.

egglog's `ordering-min`/`ordering-max` compare the `Value` word a term is stored as
(`egglog/src/lib.rs`, `add_primitive!(&mut eg, "ordering-min" = |a: #, b: #| -> # { if a < b { a }
else { b } })`), and a `Value` is a `u32` **id handed out in allocation order** within a session.
`Term.blt` compares structure. So the two pick different class **representatives**, deliberately —
matching egglog would mean threading a session-wide allocation counter through `Database`.

The invisibility claim holds only under two side conditions, and both are routinely violated: the
merge function must never be **read**, and its representative must never be used as a **key**. The
proof encoding does both — it keys `@UF_<Sort>` on `(ordering-max old0 new0)`. Two repros, run
against `target/release/egglog`:

**(a) An eq-sorted merge, read back.** With `(function UF (Math) Math :merge (ordering-min old
new))`, `(set (UF (A)) (Y))`, `(set (UF (B)) (X))`, `(union (A) (B))` and rules
`(rule ((= (X) (UF k))) ((HitX)))` / `(rule ((= (Y) (UF k))) ((HitY)))`, egglog prints
`(HitX 0) (HitY 1)` — it keeps `Y`, the term created first. This model keeps `X`, because
`"X" < "Y"` structurally, and predicts `(HitX 1) (HitY 0)`. Swapping the two `set`s so `X` is
written first makes egglog keep `X`, so egglog's choice is **order-driven where this one is
name-driven**. Row counts see it: `HitX` and `HitY` differ.

**(b) A negative `i64`.** With `(function D (Math) i64 :merge (ordering-min old new))`,
`(set (D (A)) -1)`, `(set (D (A)) 1)` and `(rule ((= -1 (D k))) ((Hit k)))`, egglog settles on `1`
and prints `(Hit 0)`; this model settles on `-1` and predicts `(Hit 1)`. The mechanism is the same
allocation order: an `i64` in `[0, 2³¹)` is stored *unboxed* as itself, and every other `i64` —
negative or `≥ 2³¹` — is interned and stored as `2³¹ + index` with `index` handed out in order of
first interning (`egglog/core-relations/src/base_values/`, `impl_medium_base_value!` and
`BaseInternTable::intern`). So `1` sorts below `-1`, and between two *interned* literals egglog's
answer is not even a function of the two numbers — it depends on which the session saw first.

Consequence: this deviation is a **hypothesis of any future simulation theorem** against real
egglog, not something a proof may wave away. Only a union-find-free encoding would retire the two
primitives and with them the deviation; complicating `Term.blt` to chase an order the model cannot
see is not the answer.

## Multi-column outputs

egglog's tables are multi-column and the encoding depends on it: `@UF_<Sort>` carries a parent
*and* a proof, `@<C>View` an e-class and a proof. Hence `Row.out : List Term`, with
`FnDecl.outArity` beside the key `arity`.

**The merge result is a `List Expr`, one per value column**, where surface syntax writes one
tuple-valued `(values e₀ e₁ …)`. This follows the backend, already per column —
`assert_eq!(resolved.len(), schema_math.n_vals(), "merge for {f} must have one entry per value
column")` (`egglog-bridge/src/lib.rs:1405`) — and avoids a tuple constructor in `Term`, which would
make every existing `cases t` in the M10 proofs non-exhaustive. **Recorded as a deviation from
surface syntax**: a source program writes `(values …)` and the model takes the list it denotes.

**Reading a column other than the first is `Pattern.values`**, egglog's tuple destructure
`(= (values v…) (f a…))`, and it is the *only* way egglog offers: a tuple-output function cannot
be evaluated as an expression (`eval_resolved_expr` panics on `values`, `exec_state.rs:293`) and
cannot be extracted, whose error message says "Read its columns in a rule with `(= (values ...)
({0} ...))` instead" (`typechecking.rs:1639`). egglog recognizes the shape inside an ordinary `=`
fact, in either argument order, and lowers it to the atom `f(a…, v…)` (`match_tuple_destructure`,
`ast/mod.rs:1770`). Since every read is an atom, the destructure is now the model's **only** read,
generalized to any width, and `Expr.MEval.lookup` is gone — see `PLAN.md`, "Reading is a query
atom". The historical passages below that mention `MEval.lookup` or `execExpr`'s lookup branch
describe the state before that change.

**`Cong.fd` is unaffected — the claim holds.** `fd` fires only at a constructor, which has
exactly one value column; `MergeFn::UnionId` is documented in the backend as "Use congruence to
resolve FD conflicts", so it *is* `fd`. The **encoded** program has no constructor tables of that
kind at all: `@UF_<Sort>` and `@<C>View` are `MergeFn::Block`s whose columns are expressions
(`ordering-min old0 new0`, `()`), resolving congruence through the body's `set (@UF_Math …)` plus
the `@UF` table — so in the target, congruence is **entirely simulated**, exactly the M11
simulation obligation. `fd` is still stated per column, which costs one premise and makes the
claim moot rather than load-bearing.

**One place this is coarser than egglog.** A merge kind is per *function* here and per *column*
there: `MergeFn::Columns(Vec<MergeFn>)` lets one function have `UnionId` on column 0 and `Old` on
column 1, which `MergeSpec` cannot express. Nothing needs it — the encoding's tables are uniformly
`Block`s with expression columns, source constructors single-column `UnionId`. The faithful shape
would be a per-column merge kind beside a single `actions` list run once before any column, under
which the functional dependency holds of a column and not of a function. Not done: it would put a
per-column signature lookup into `Cong.fd` for a case neither language produces.

## Restrictions on `encode`'s domain (M11)

`encode` is defined only for source programs **whose functions have no `:merge` action block**,
permanently rather than as a gap to close: the encoder itself rejects such a program with
`ProofEncodingUnsupportedReason::MergeActionBlock`, because "a `:merge` action block runs actions
before its result; the proof encoding only instruments the merged value, so mark it unsupported
rather than emit silently-incomplete proofs" (`proof_encoding_helpers.rs:1088-1096`). Not a
contradiction with the encoder *emitting* such blocks — `@UF_<Sort>` and `@<C>View` are exactly
that shape — since it knows what its own blocks prove and not what a user's does. Same check also
rejects `:no-merge` on an eq-sorted output (`NoMergeEqSortFunction`).

## Constraint (3): monotonicity

Discharged by the representation: in `Spec/` asserted rows only accumulate, a merge adds the
combined row beside the two it combined, and there is nothing to overwrite. `Database.Contained`
gains a `rows` field, and `MergeStep.contained`, `CmdStep.contained`, `ProgramStep.contained` are
what every M2–M8 lemma needs to transport; `Cong.mono` and `Database.Out.mono` follow.

`CmdStep.contained` is also the formal content of the hard constraint **never delete a term row or
a proof row**, on which the encoding depends directly ("Nothing is ever removed from it, which lets
proofs refer to terms after they leave the e-graph"). `delete` and `subsume` are outside the
fragment and, when they arrive, must not touch term or proof rows; the encoding already defers them
to marker relations and deletes only the *view* row.

**What monotonicity costs.** egglog *deletes* the displaced row and `Spec/` keeps it, so `Out` is a
sound over-approximation: every value egglog computes is derivable here, plus stale ones it has
removed. For `@UF_<Sort>` that is not merely harmless but right — any parent a term ever had is
genuinely equal to it, which is what `Out.union_cong` says.

## Constraint (4): firing counts

**What egglog does.** Merges are *deferred*: rule execution stages rows into mutation buffers, and
`Database::run_rule_set` searches and applies every rule before calling `merge_all`
(`core-relations/src/free_join/execute.rs:653-655`). `merge_all` then runs **to a fixed point**
(`free_join/mod.rs:546-628`, `:686-689`) — a merge's own `set` re-notifies and is picked up next
iteration. Within one key, merging is a left fold in staging (FIFO) order, and **the first row for
a fresh key is inserted verbatim with no merge call** (`table/mod.rs:715-790`, `:742-768`); in
parallel mode the cross-buffer order is not deterministic. Top-level actions take the same path, so
each top-level `set` is its own merge phase (`src/lib.rs:1490-1512`).

### Saturation is a hypothesis, not a step

Merge closure is a *phase* of a round — `RunStep db db' := MergeClosure (RunRules db) db'` — and
the deferral is faithful: no rule sees another's merged value within a round. But `RunStep`
deliberately does **not** require the closure to have saturated, and an earlier draft that did was
*wrong*, not merely strict: `∀ db', ¬ MergeStep db db'` is **unsatisfiable**, because nothing
removes rows, so both colliding rows are still present after the step and it applies again —
forever. (With no guard on the collision there is a second, independent reason: every row collides
with itself.) Under that definition `CmdStep … .run` is vacuous for every program with a real merge
collision. The corrected form is "every step is the identity",
`MergeSaturated db := ∀ db', MergeStep db db' → db' = db`, **assumed by the theorems that need it**
— simulation, and matching egglog's row counts — rather than built into the step. This removes
termination from the spec entirely, which is what the invariant framing buys.

### No guard on the collision

`CongList` is reflexive, so a row collides with **itself**, and `MergeStep` has no `a ≠ b` side
condition to stop it. An earlier draft had one, reasoning that egglog merges a *retained* row
against an *incoming staged* one and so never self-merges, and that a state relation — two rows in
a `Set` — cannot see how often a value was staged. That reasoning is about *matching* egglog, and
it made the guard the one **under**-approximation in an otherwise over-approximating design, the
unsafe direction: it leaves egglog reaching states the model never checks, so the safety invariant
does not transfer to real egglog.

Without the guard the model covers egglog unconditionally. egglog skips a collision that changes no
value column whenever the function declares `:internal-identity-vals` **or** its `:merge` carries an
action block, and fires on it otherwise; `MergeStep` fires either way, and on the self-collision
egglog never even sees. Over-approximate in every case. **The safety theorem therefore needs no
scope condition on the signature at all** — no `merge (x, x) = x`, no identity-guardedness
hypothesis. (`Impl/` does take the skip, because it has to predict row counts and a `:merge` body
*writes*; that is `FDatabase.noConflict`, and firing fewer steps is what its containment contract
allows. See "A collision that changes nothing runs no body" below.)

~~Read that narrowly: it is about the *safety theorem*. Congruence **monotonicity** does need a
signature condition, and it is not optional.~~ **Superseded, and this is where the second
congruence relation cost the most.** `MCong.fd` fired only where the signature said "constructor",
so redeclaring a function as `:no-merge` destroyed a derivation while adding no term, row or
equality, and `MCong.mono` and `Database.Out.mono` both had to carry `d₁.sig = d₂.sig`. `Cong`
reads neither `sig` nor `rows`, so `Cong.mono`, `CongList.mono` and `Database.Out.mono` carry only
`Database.Contained`, and `Cong.mono_update` is a one-line corollary: a declaration of *any* name
preserves every derivation. The counterexample that used to sit here is provably false now and has
been deleted. `CmdStep.mono_recorded` and `ProgramStep.mono_recorded` accordingly lost their
`Cmd.DeclFresh` hypothesis.

Two consequences, both intended.

**Idempotent merges gain vacuous rows, not divergence.** The union-find's body on a self-collision
is `(set (@UF_<S> (ordering-max p p)) (values (ordering-min p p) ()))`, a reflexive self-edge;
`Cong` derives only `p = p`, already true by `refl`. In proof mode it writes extra proofs of
`p = p`, which are *valid* — and not observable, because egglog's `print-size` filters
`internal_hidden || internal_let` and reports a view under its `term_constructor` name, which is
exactly why `files.rs` shares one snapshot between normal and term-encoded runs, so `@UF_*` and
`@*View` never appear in a diff. `MergeStep.self_id` states the fixpoint: a body that adds nothing
and returns the output it was given makes the step the identity, which keeps `MergeSaturated`
reachable.

**`:merge (+ old new)` diverges.** The self-collision derives `2v`, `3v`, … forever, where egglog
with a single `set` merges nothing. Intended: such a program's egglog result is insertion-order
dependent, so there is no fixpoint to denote and diverging is more honest than inventing an answer.
The two changes are coupled — this works only because `MergeSaturated` is the "no step *changes*
anything" form, under which `ordering-min` self-merges saturate and `+` correctly does not.
`PLAN.md`'s note that naive and seminaive "genuinely diverge" for a non-idempotent merge is right
about egglog and does not apply here, since this model has no firing count at all.

### `:internal-identity-vals`, and the skip that is now the default

In full (`egglog-bridge/src/lib.rs`, `MergeFn`): compare the first `k` **value** columns by raw
equality; if they agree, skip the action block entirely, keep the *old* value in every column
including the payload, and leave the row untouched with its old timestamp so seminaive does not
re-fire. The encoding's use is identity column = e-class, payload = proof, so a collision agreeing
on the e-class keeps the existing proof. Contract: only valid when `merge (x, x) = x`
(`egglog-bridge/src/lib.rs:227-231`). The count is a `Nat` and not a `Bool` because it marks a
**prefix** of the value columns — `:internal-identity-vals 1` on `(Math) (Math @Proof)` marks the
parent column identity and the proof column not, so re-setting the same parent with a *different*
proof keeps the old row and its old proof. The comparison is
`cur[id_lo .. id_lo + k] == new[id_lo .. id_lo + k]`, and when it holds every column, payload
included, takes the old value.

**Since `20d1461` (issue #59) the undeclared case is not "no skip".** `unchanged_width` is now
`n_identity_vals.or_else(|| (!actions.is_empty()).then(n_vals))`: a `:merge` with an **action
block** and no declaration takes the same skip over *every* value column. A single-expression
`:merge` still never short-circuits, deliberately — it may be non-idempotent, and `:merge (+ old
new)` on two rows holding `2` gives `4` on both this binary and upstream.

**That made the skip a difftest-fidelity concern, and this file said it was not.** The earlier
conclusion here — "the `print-size` filtering above means it is not a difftest-fidelity concern
either" — was about the *declared* form, which only the encoding's own views use and which
`print-size` hides. It does not survive the generalization: the difftest generates ordinary
`:merge` action blocks, they now skip by default, and comparing whole *rows* rather than value
columns cost a real divergence (recorded below). `Impl/Merge.lean`'s `FDatabase.noConflict` is the
model of the default form.

**`identityVals` stays out of `FnDecl`**, now for a narrower reason: what is left unmodelled is the
*prefix* — `k < n_vals`, where the payload columns may differ and the row is still kept. Nothing in
the difftest fragment declares it, and the trigger to revisit is unchanged: rendering `encode`'s
output to `.egg` and running it in real egglog.

### `:no-merge` collisions, out of scope

The other deliberate gap on this constraint, and the one where the model is **looser** than egglog
rather than stricter. A `:no-merge` collision is a *program error egglog rejects at runtime*, and
this model does not model runtime rejection: there is no error state for a step to enter, and the
model should not try to cover the whole egglog language. `Database.NoMergeOk` states the condition
and **nothing consumes it**; `Impl/Merge.lean` does not check it either, and `MergeStep` fires only
on `.merge`, so a `.noMerge` collision is simply inert here.

Confirmed against the binary: `(function Dist (Math) i64 :no-merge)`, `(set (Dist (A)) 1)`,
`(set (Dist (B)) 2)`, `(union (A) (B))` gives `[ERROR] Panic: Illegal merge attempted for function
Dist` and exits 1, where this model silently keeps both rows and predicts `Dist 1`. With **equal**
values the two agree — the same program with both values `1` prints `(A 1) (B 1) (Dist 1)` and the
model predicts the same — so it is exactly the conflicting-value case that is scoped out, which is
why the difftest's `:no-merge` cases keep their keys distinct.

`MergeSpec.noMerge` itself stays. Scoping out the *collision behaviour* is not "drop the
constructor": the proof encoding declares its proof nodes with `:no-merge` (`Encoding/Encode.lean`'s
`termDecl`), and `Impl/Merge.lean`'s merge phase turns on a `.noMerge` row never being deleted,
"deleting one would delete a proof".

## Constraint (5): base sorts

**Not done, deliberately.** `Lit` is still `Int` only and `Term` is still untyped. Instead:

* The FD's key comparison is `CongList`, comparing every argument position by congruence. On a
  base-sorted argument congruence degenerates to equality, since a base value is never unioned, so
  the sort discipline is **not needed for the FD to be correct** — only for typing. That is why M9
  can land without it.
* Well-formedness requires a row's *arguments* and *output* to be terms but **not its key
  application** `.app f args`: for a `:merge` function that application is a key, not a value — it
  has no e-class and cannot be unioned — and with one untyped `Term` nothing else prevents it being
  written as a term.
* The **arity** half of the discipline is done and separable from the sort half.
  `Impl/Check.lean`'s "Arity" section is egglog's column-count check, syntactic and `Bool`-valued,
  beside `SetLegal`; arity needs no sorts, which is why it landed first. What it does *not* give is
  the state-level invariant "every row has its declared width", the derived form that would let a
  width-sensitive row read be proved total; `Proofs/Counterexamples.lean`'s
  `claim3Program_not_arityOk` is the program that used to witness the gap, now rejected by the
  syntactic check. That invariant belongs inside `WF` and needs preservation lemmas through
  `evalAction` and `MergeStep`.

The shape once sorts land, where the model's single untyped `Term` finally dies, is
`Sort := eq String | i64 | str | unit` with `FnDecl` carrying `inputs`/`output`/`merge`, `Scope`
becoming `List (Var × Sort)` and `Expr.Scoped` a typing judgment. Two side conditions the sorts
would buy: a constructor requires an eq-sorted output (egglog rejects `:no-merge` on an eq-sort output
under the term encoding, `proof_encoding_helpers.rs:1067-1086`), and `Term.ctorRows` needing no
signature becomes a theorem rather than an invariant maintained by inspection. `Lit` also wants
`.str` and `.unit` before M11 — `@Rule_<k>` carries a rule *name* and the no-proof column is
`Unit` — which is cheap and independent of everything above.

## Constraint (6): termination

Out of the spec entirely: `MergeClosure := Relation.ReflTransGen MergeStep`, no fixpoint, no
measure, no saturation requirement anywhere in `Spec/`. The reason is sharper than "merges may not
terminate": **a merge body can build terms**, so the candidate universe grows as the closure runs —
exactly what `Impl/Closure.lean`'s `closure` relies on not happening, its well-founded measure
being `(candidates terms).card - rel.card` over a *fixed* `terms`. The congruence closure is fine:
`terms` and `eqs` are fixed while it runs, and the functional dependency adds no step to it at
all, since `Cong` reads no rows. Only the *merge* loop has no measure.

## The executable layer

`Impl/Merge.lean` runs the M9 semantics, `Tests/Egg.lean` renders a `Program` as `.egg`, and
`DiffTest.lean` writes the cases. Four things differ from `Impl/Interp.lean`, each a design
decision, and `Impl/Merge.lean`'s header repeats them. **The contract is containment, not
equality**, because `Impl/` deletes — see the next section. **The merge phase is one pass, not a
fixpoint**: `mergeRound` fires every collision it can see once, structurally terminating so no fuel
and no accessibility argument, and sound *because* `RunStep` carries no `MergeSaturated`
requirement, so a prefix of the closure is a reachable state; `mergeSaturateF` sits beside it,
taking a termination witness (`Acc`) rather than fuel, and `execCmdM` runs it to a fixpoint as
`merge_all` does. **A read has to pick**: `patternHolds`' row scan sees a superseded output where
the spec allows any, and where egglog sees only the current one. **The congruence closure is unchanged**, and now for a reason that needs no side condition:
`Cong` reads `terms` and `eqs` and no row at all, so `closureF` is `closureTotal` on those two
whatever the row set holds (`mem_closureF_iff_of_wf`). The functional dependency adds nothing to
decide.

### Row counts survive, and why that matters

`rowCount` counts congruence classes of **key tuples**. A merge step writes its combined row at a
key already present, so it adds no key class, and a merge with an empty action block writes nothing
anywhere else — so the count is invariant under the merge phase, which is exactly why the
interpreter can run one pass instead of saturating and still predict egglog's answer. Keeping every
superseded output, the over-approximation the design rests on, does not inflate it either: three
recorded values at one key are still one row.

`FDatabase.mergeRound_rowCount` states this and is **false as stated** — `addRow` inserts the
*result's* terms with their constructor rows, so a merge whose result builds an application adds a
key class to a different function's table. The statement the difftest relies on strengthens `hpure`
to "the merge result is a term the database already holds", satisfied by every generated case
(results are `i64` literals).

### The difftest fragment

Deliberately narrow, and the narrowness is the interesting part.

* **Every generated merge is idempotent** (`min`, `max`, `old`, `new` on `i64`). A non-idempotent
  one would give extra firings and extra values under our over-approximating reads, so a row-count
  difference would be this model's design showing rather than a real bug. **Non-commutative is a
  different question**, and excluding `old`/`new` on this bullet's reasoning was a mistake: they are
  idempotent and, unlike `+`, completely determined in egglog. While every generated merge was
  commutative, nothing could see which colliding row the model called `old` — see below.
* **Generated merge bodies are `let`-only.** A body that `set`s a side table would fire on
  self-collisions and in both orders, inflating that table's count for the same reason.
* ~~**Merge functions are written and never read.**~~ **No longer true, and it agrees.** This was
  the fragment's boundary, on the reasoning that a body atom reading a merge function binds *any*
  recorded output where egglog binds the current one. What closed it is `Impl/` deleting the rows a
  merge combined: the reference implementation now holds only the merged value, so a read sees what
  egglog sees. Reads are generated in both shapes egglog offers — `(Dist k…)` and `(= v (Dist k…))`
  — biased towards a key and a value the program actually writes, which took the reads that fire
  from 6 of 30 cases to 17 of 30; curated `read-exists` / `read-value` / `read-stale` /
  `read-congr` / `read-value-congr` / `read-nomerge` / `read-copy` sit beside them. Every one
  agrees. The *specification* still admits the stale read, which is the design showing rather than a
  defect.
* **Outputs are `i64`, keys are eq-sorted.** egglog typechecks a `(function …)` declaration, so a
  merge function needs a real output sort — this is where sorts finally bite. An eq-sorted output
  would dodge the base sort, but then `ordering-min` must render, and `Term.blt` is *structural*
  where egglog's is by allocation order, so the two would pick different representatives. **Row
  counts would not survive that** — repro (a) of "The representative deviation" is exactly this
  shape, an eq-sorted `ordering-min` merge read back by a rule, and its `Hit` counts differ.
  Eq-sorted keys also keep `Term.lit` out of constructor arguments, so `Egg.lean`'s standing
  literal mismatch stays out of the way.

The case that matters is `min-rebuild`, the shape of `egglog/tests/merge-during-rebuild.egg`: two
`Dist` rows whose keys are then unioned, so egglog's table drops from two rows to one. `min-congr`
does the same collapse through congruence rather than a direct union, and `min-rule` writes a row
from a rule head. These discriminate — a model that ignored key congruence would predict 2 where
egglog says 1.

### Still unbuilt

* ~~**Two evaluators**, functions and relations~~ and ~~**`Cong` and `MCong` still coexist**~~ —
  both **done**, and neither the way this file expected. The evaluators collapsed onto the
  *functional* side rather than the relational one, because reading became a query atom; the two
  congruences collapsed onto `Cong` with `Cong.fd` a theorem, rather than onto `MCong` via
  `mcong_iff_cong`. `exec_programStep` survived as a biconditional both times. See `PLAN.md`, "The
  consolidation arc".
* **`Database.RowsWF` is stated outside `WF`**; putting it in would make every `WF` construction
  carry a subterm-transitivity argument for no current payoff. **`Lit` is still `Int` only.**

## What the widening and the composed interpreter found

**`Action.set` takes a `List Expr` and `Pattern` gained `values`.** `Row.out`, `Database.addRow`,
`Database.Out` and `MergeSpec`'s result were multi-column from the start; `Action.set` and the
pattern language were not, so a multi-column row could be *created* by a merge and never written or
read — what `CHECKER.md` called the one blocker on M11's proof column.

**`Program.expectedSizes` now runs a composed M9 `execProgramM`.** It ran `Impl/Interp.lean`'s
`exec`, which evaluates with `Expr.eval` and never calls `mergeRound`, so `mergeOne`, `mergeRound`,
`execActions`, `execExpr`'s lookup branch and the destructure had **zero** differential coverage —
the suite's pass count said nothing about the merge implementation.

**`min` and `max` had to become primitives.** `Prim.ofName` knew only
`ordering-min`/`ordering-max`, so a `:merge (min old new)` body — the shape every merge case uses,
and the shape `tests/interval.egg` and `tests/merge-during-rebuild.egg` use — built the *term*
`min(5, 3)` where egglog computes `3`. Invisible while nothing ran the merge phase, and three
things went wrong the moment something did: no state was ever `MergeSaturated`, so `mergeSaturateF`
returned `none` for every case with a real collision; each pass wrote a genuinely new value at
every colliding key, so the row set squared per pass and **12 of 30 generated merge cases timed
out**; and a rule reading a merged value got a term where egglog has a number. `Prim.intMin`/
`intMax` on `Lit.int` fixed all three — 102 passed / 12 skipped became 114 / 0 / 0 — and saturation
became reachable again. The sharpest thing the coverage gap was hiding: the merge cases were
*generated* correctly and *predicted* by a merge implementation that had never been run.

**`Impl/` now deletes superseded merge rows; `Spec/` does not.** Both were append-only and the
contract between them was an *equality*, which is what forced `Impl/` to be append-only — making
the reference implementation faithful to this model and **unfaithful to egglog**, which replaces
the row. `Spec/` stays append-only, since the M11 safety invariant needs neither termination nor
confluence precisely because nothing is removed. `Impl/Merge.lean`'s merge phase drops the two rows
it combined and nothing else — never a term, never an equality, never a constructor row (which the
whole congruence argument rests on) and never a row of a `.noMerge`
function (how the encoding declares its proof nodes, so deleting one would delete a proof);
`FDatabase.mergeRound_confined` is that sentence, machine-checked. Saturation then follows rather
than being hoped for: deleting the pair that fired strictly shrinks each colliding key class, so
`mergeSaturateF` terminates.

The contract **splits** rather than weakens. *Soundness* is a containment — the implementation
finds **fewer** results, never more, the safe direction because everything M11 reads is positive in
the state; `ValidSubst.mono` makes "fewer rows" mean "fewer matches", and `Cong`, `CongList` and
`Database.Out` are monotone already. `execM_contained` is the top-level statement,
**proved**. *Completeness*, so containment is not vacuous, is two statements: on the constructor
fragment the existing **equality** stands untouched, since no row belongs to a `.merge` function,
so `hasMergeRow` is false, the pass is the identity (`FDatabase.mergeRound_eq_self`) and
`exec_programStep` is outside the blast radius; and on **lattice** merges the implementation holds
the `Current` value at each key class, which is `execM_current_of_lattice` — **false as stated**,
refuted three ways in `Proofs/Lattice.lean`; its `hjoin` is vacuous for the same reason
`diamond_of_join`'s is. For a
non-lattice merge `Current` does not exist and nothing is claimed. One statement became **false**
in the *harmless* direction (the implementation is smaller than anything the spec reaches, not
different): `mergeRound_closure`, since a deleting result is not `MergeClosure`-reachable when
every `MergeStep` only *grows* the state. `execM_reachable` now applies to `exec` only, and is
**proved** there under a single hypothesis, `Program.CtorDecls`, whose necessity is
`Falsity.exec_programStep_needs_ctorDecls`: a `:merge` declaration lets a row collide with itself,
so the specification reaches two states where the interpreter returns one. `Program.SetLegal` used
to sit beside it and is gone — what it maintained was `Database.CtorRows`, which the refinement
stopped reading when congruence did.

**The over-approximation was observable, and `Impl/` no longer shows it.** Until a rule could read
a value column, no oracle could see that the model keeps every superseded output where egglog
deletes it. Now one can — minimal repro, machine-checked both ways:

```
(function Dist (Math) (i64 i64) :merge (values (min old0 new0) (max old1 new1)))
(set (Dist (A)) (values 5 1))
(set (Dist (A)) (values 3 7))
(rule ((= (values 5 1) (Dist k))) ((Hit k)))
(run 1)
```

egglog reports `Hit 0`: the merge replaced the row and `(5, 1)` is gone. An append-only
implementation reports `Hit 1`, because the superseded row is still there and the destructure reads
it. It is now a difftest case (`tuple-stale`, with the single-column `read-stale` beside it) and
**it agrees**. The *specification* still says `Hit 1` is reachable, deliberately: **this is the
design showing through, not a defect** — the over-approximation argued for under "Why the reader
over-approximates", in the safe direction, since a stale row is a row that really was written. What
changed is only which side of the `Spec`/`Impl` line it lives on.

**`old` and `new` were bound backwards, and a row's *place* in `rows` is its age.** egglog binds
`old` to the value already in the table and `new` to the one being inserted; `FDatabase.addRow`
prepends, so the earlier of two rows in `d.rows` is the more recent one, and `mergeRound`'s outer
loop scans from the front — making `r₁` the newer row of a firing pair. `mergeOneWith` bound `old`
from `r₁`, so `:merge old` returned what `:merge new` should. Nothing saw it: `genMergeSpec` drew
`min` and `max` only, which are commutative, and `(print-size)` cannot see a value at all. The
second half is the same fact once more: the combined row must take `r₂`'s key **and `r₂`'s slot**,
because a merge in egglog leaves the existing table entry in place, so the survivor stays exactly
as old as the row it grew out of. Dropping both rows and prepending the result made the survivor
the *youngest* of its class and inverted the next collision —

```
(function Dist (Math) i64 :merge old)
(set (Dist (X)) 1) (set (Dist (Y)) 2) (set (Dist (Z)) 3)
(union (X) (Y)) (union (Y) (Z))
```

is `1` in egglog and was `3`. `MergeStep.collide` needed no change: it runs the body under
`mergeEnv a b` and writes at the *first* row's key, so `mergeOneWith_mergeStep` builds its witness
with the pair in the order `(r₂, r₁)` and the two line up. `genMergeSpec` now draws `:merge old`
and `:merge new`, a generated case reads back the value it wrote first (`witnessRule`, whose `Won`
count is 1 exactly when the earlier write survived), and eight curated cases pin the four shapes;
122 cases became 130, and the wrong binding fails 14 of them.

### `old` is the row at the canonical key, and insertion age is only the tie-break

The paragraph above got the *direction* right and the *rule* wrong, and every case it added agrees
with both readings, so nothing caught it. **`old` is not the row written earlier. It is the row
already in the table.** egglog's insert calls the merge function as `merge_fn(cur, row)` — `cur`
the stored row, `row` the arriving one — and binds `old` to the first
(`egglog/core-relations/src/table/mod.rs`, `SortedWritesTable::insert`). Nothing there mentions
age. A rebuild is what separates the two: it re-canonicalizes each candidate row and stages a
remove-and-re-insert for exactly those the canonicalization changed
(`egglog/core-relations/src/table/rebuild.rs`), so the row whose key is *already canonical* is
never moved and is therefore `cur`, however recently it was written, while every row whose key
moved arrives as `new`. Canonical is least e-class id, since the union-find unions **by min id**
(`egglog/union-find/src/lib.rs`), and ids are handed out as terms are built — so the canonical
member of a class is the term created first. Age decides only when no key moved (two `set`s at one
key) or when *no* row holds the canonical key (the rebuild stages them all, in table order).

Minimized against `target/release/egglog`, all `(function Dist (Math) i64 :merge new)`:

| program | egglog | what it rules out |
| --- | --- | --- |
| `(set (Dist (K)) 3) (set (Dist (A)) 2) (union (A) (K))` | `2` | — |
| the same after a bare `(A)`, so `A` exists first | `3` | insertion age: identical, answer flipped |
| `(P (K) (A))` before the two `set`s | `2` | — |
| `(P (A) (K))` before the two `set`s | `3` | argument order within one term decides too |
| `(set (Dist (K)) 3) (set (Dist (K)) 2)`, no union | `2` | canonicity alone: no key moved, age decides |
| `(Z)` first, both keys unioned into `(Z)` | `2` (`3` under `old`) | canonicity alone: neither key canonical |

Swapping the `union`'s arguments changes nothing, which is min-id and not argument order.

**`Impl/` matches this; `Spec/` neither can nor needs to.** `MergeStep.collide` takes the two rows
as premises in *both* orders, so either binding is a legal step and `mergeOneWith_mergeStep` is
indifferent to the choice — matching egglog is an implementation question, not a change to the
semantics. `Database.terms` is a `Set` and has no order to read canonicity from; `FDatabase.terms`
is a list that `addTerm` prepends to, so a position in it is an age, exactly as a position in
`rows` is. `FDatabase.canonTerm` reads canonicity off that list and `swapForCanon` orients the pair
before `mergeOneOriented` runs. Two consequences worth naming:

* **`Term.subtermList` is ordered, and load-bearing.** It now lists a term, then its arguments
  **right to left**, so that prepending it puts the first-built argument last — egglog builds an
  application's arguments left to right. Reversing it back fails `canon-arg-left`/`canon-arg-right`.
  Every other consumer goes through `mem_subtermList` and cannot see the order.
* **`swapForCanon` is guarded by the firing condition.** A weaker guard forces the congruence
  closure on pairs whose arities differ — `congrTuple` compares lengths before looking inside `cl` —
  which is enough to stall the kernel on `Proofs/Lattice.lean`'s `decide` proofs.

Six curated cases (`canon-old`, `canon-new`, `canon-arg-left`, `canon-arg-right`,
`canon-none-old`, `canon-none-new`) pin the table above, the last three being shapes where the two
readings agree, so the agreement cannot rot silently. Disabling the orientation fails three of
them; reversing `subtermList` fails two.

**What is still not modelled.** A term's list position is fixed when it is *first* added, which
tracks egglog for terms built by actions and by rule heads in the order the interpreter runs them.
A round firing several rules may build terms in another order than egglog does, and nothing here
pins that. Two further residuals, both inherited from "quantifying over congruent keys rather than
re-keying rows":

* When neither colliding key is canonical, egglog's survivor sits at the canonical key and this
  model's sits at the older row's key. `Database.Out` reads a row from every congruent key, so this
  is invisible until a row appears at that third key *later*, when the two disagree about which of
  the pair is resident. Writing at the canonical key is not an option: `MergeStep.collide` writes
  at one of the two rows' keys, and there is no row at the third.
* `ordering-min`/`ordering-max` keep using the structural `Term.blt` and remain the deviation
  recorded under "The representative deviation" — a `Prim` is `List Term → Option Term` with no
  database to consult, so the term list is not reachable from there.

**The read path had no coverage at all**, which is how this stayed invisible: the lookup branch,
reachable through `execM` from a pattern's `expr` case, was exercised zero times. One finding from
the before-measurement is worth keeping — the single-column `read-stale` **agreed even before the
deletion**, and for the wrong reason: the evaluator took the *first* recorded output and
`FDatabase.addRow` prepends, so the row it picked happened to be the merged one. The tuple
destructure searches all rows and exposed what the single-column read was hiding. An agreement that
rests on list order is not evidence of anything, the same lesson as `min`/`max`. (That branch is
gone: reads are the query atom now, and `patternHolds`' row scan is the one place the interpreter
still chooses.)

### A collision that changes nothing runs no body

`mergeRound` skipped a pair only when the two rows were **equal**, `r₁ == r₂`. egglog skips when
the two rows' **value columns** are equal and says nothing about their keys. The gap between the
two is exactly one shape — *congruent but unequal keys holding the same value* — and it is only
observable through a body that writes, which is why it survived until writing bodies were
generated:

```
(datatype Math (L) (X) (Y))
(function Log (Math) i64 :merge new)
(function Dist (Math) i64 :merge ((set (Log (L)) old) new))
(set (Dist (X)) 2) (set (Dist (Y)) 2) (union (X) (Y)) (run 1) (print-size)
```

egglog answers `L 0, Log 0`; the model answered `L 1, Log 1`. With a `union` body instead, egglog
answers `W 2` and the model answered `W 1`. Minimized against `target/release/egglog`, with the
controls that pin the trigger to *equal values at unequal keys*:

| program | egglog | model, before | what it fixes the trigger to |
| --- | --- | --- | --- |
| the repro above | `L 0, Log 0` | `L 1, Log 1` | the divergence |
| second value `3` instead of `2` | `L 1, Log 1` | `L 1, Log 1` | not "a rebuild collision"; the values must agree (this is `merge-body-set-rebuild`) |
| `(set (Dist (K)) 2)` twice, one key | `L 0, Log 0` | `L 0, Log 0` | not "equal values"; at one key the model dedups the rows, which is the case issue #59 fixed |
| width 2, one column equal, one not | `L 1, Log 1` | `L 1, Log 1` | all-or-nothing over the whole value tuple, not per column |
| three rows, two equal plus one different | `L 1, Log 1` | `L 1, Log 1` | a real conflict elsewhere in the class still fires |
| `:merge (+ old new)`, both rows `2` | `4` | — | a single-expression `:merge` does **not** short-circuit; `20d1461` records that as an explicit decision |

**The fix is in `Impl/`, not `Spec/`.** `FDatabase.noConflict body r₁ r₂` is `body ≠ [] &&
r₁.out == r₂.out`, and `mergeOneOriented` takes it as a branch that drops `r₁` and leaves `r₂` where
it stands, running neither `execActions` nor the result expressions. `Spec/Merge.lean` is untouched:
`MergeStep` still fires on the collision, which keeps it over-approximating in the safe direction —
the model **over-fired**, and firing fewer steps is precisely what `mergeRound`'s contract permits.

**Drop `r₁`, not "no-op entirely".** Both agree on the repro and on every control above, because a
key class whose rows *all* hold one value has nothing to observe and a class with any disagreement
collapses through the pairs that do fire. Dropping is still the right one: it is what egglog's
insert does — the arriving row is discarded and only the resident row remains in the table — and it
is what keeps `mergeRound`'s convergence argument true as stated ("a pass strictly shrinks the rows
at every key class that collided"), which a branch that removed nothing would break.

**One proof statement had to weaken**, and only these two: `mergeOneOriented_mergeStep` and
`mergeOneWith_mergeStep` concluded `∃ D', MergeStep D D' ∧ …` and now conclude
`∃ D', MergeClosure D D' ∧ …`. A skipped collision takes **no** specification step, and no step is
available to take instead: the implementation never evaluates the body, so `MergeStep.collide`'s
`evalActions` and `Expr.evalList` premises are not in hand and in general do not hold — nothing
scope-checks a merge body, so one with a free variable makes `evalActions` fail while the skip still
fires. Zero-or-one steps is `MergeClosure`. Everything downstream is verbatim unchanged:
`mergeRound_contained` consumed the step with `ReflTransGen.tail` and now consumes the closure with
`.trans`, and `execM_contained` and `execM_reachable` are as they were.

Four curated cases pin it — `merge-body-noop-rebuild` (the repro), `merge-body-noop-union` (the
skip seen as an equality that was never asserted), `merge-body-noop-partial` (width 2, one column
moving, so the block must still run) and `merge-body-noop-three` (a real conflict inside a class
that also contains a no-op pair). Reverting the fix fails the first two.

**This unblocks drawing writing merge bodies at random**, which `genMergeSpec` stopped short of for
exactly this reason. Widening it is a separate change.

## The merge phase runs between commands

`CmdStep.action` carries a `MergeClosure` leg:

```lean
| action {db d db' : Database} {a : Action} :
    evalAction db a = some d → MergeClosure d db' → CmdStep db (.action a) db'
```

Without it the specification could not reach the states `execM` reaches, and `execM_contained` was
**false**. Checked against the release binary, with no `(run)` anywhere:

```
(function f () i64 :merge (max old new))  (set (f) 1)  (set (f) 2)
→ (print-size f) = 1,   (f) -> 2
```

Swapping the merge gives `old` → 1, `new` → 2, `min` → 1, `max` → 2, so the merge *function* really
runs at the second `set` rather than last-write-wins. `print-size` and `print-function` are both
`&self` and cannot rebuild, so nothing else is doing it. The path is `lib.rs:2101` → `eval_actions`
(`lib.rs:1490`), which compiles a bare action into a one-rule run and calls `run_rules` at
`lib.rs:1508`; every rule-set run ends in `merge_all` (`core-relations/.../execute.rs:654`).

**The implementation was faithful all along; the specification was the side that was wrong.** That
is the case for keeping differential testing ahead of proof work — no amount of proving `Impl/`
against `Spec/` would have found this.

The consequence this section used to flag — that the fix landed in the relational `CmdStep` and not
in the functional `stepCmd`, so the two disagreed off the constructor fragment — is **resolved**:
`Spec/Step.lean` and the whole functional half were deleted, and `CmdStep` is the only command
stepping there is.

## What was rejected

| rejected | why |
| --- | --- |
| Merge as a value combiner `Term → Term → Term`, and the observable value as a fold over asserted rows (`PLAN.md` M9 §3) | the union-find's side effects live only in the closure, not in the asserted rows; what survives is `Current`, for difftest and simulation only |
| A `Current`-reading evaluator | `Current` does not exist for `:merge old` or `:merge new`, both common |
| Saturation inside `RunStep` | unsatisfiable as first written, and unnecessary once the safety theorem is an invariant |
| The `a ≠ b` collision guard, and with it a `merge (x, x) = x` or identity-guardedness hypothesis on the safety theorem | all three bought a soundness gap rather than closing one |
| Fuel-bounded merge saturation in `Impl/` | returns a wrong answer where "no answer" is correct |
| Overwriting the row in `Spec/`, and a second congruence relation carrying `fd` as a rule | the first breaks `Contained` and every M2–M8 lemma; the second turned out to be a theorem about `Cong` under a weaker hypothesis, `Cong.fd` |
| An `Expr` constructor for primitives, and a tuple constructor in `Term` | both make existing `cases` in the M10 proofs non-exhaustive; reserved names and a `List` match egglog and cost no churn |
| A fresh-id / e-class-id representation on this side | M11 adds ids to the *target* configuration only; the source keeps terms as their own identity, and `PLAN.md` is right about this |

## Open questions

1. **Is `MergeStep` confluent for a join merge?** `MergeStep.diamond_of_join`, **[guess]**, whose
   `hjoin` is self-contradictory so the statement is *unconditional* local confluence — which
   nevertheless looks true, since a step's effect does not depend on the ambient state. What is
   missing is exactness; the docstring says what would supply it. **Demoted**: no safety theorem
   needs it. It buys one thing, strengthening M10's refinement from "spec-reachable" to an equality.
2. **Settled: `WellScoped` should not carry `DeclsFresh`.** The question was whether the static
   check forbidding a redeclaration belongs inside `WellScoped` or beside it. Two things answered
   it. The reason it looked urgent is gone: `CmdStep.mono_recorded`'s `.decl` case needed
   `Cmd.DeclFresh` only because `MCong.fd` read the signature, and `Cong` does not, so both
   `mono_recorded` lemmas dropped the hypothesis and its counterexample is provably false. And
   `Spec/Scope.lean` now runs all four front-end checks — `Scoped`, `Evaluable`, `SetLegal`,
   `DeclsFresh` — over **one walk**, the `Check` structure, so the sharing that bundling would have
   bought is already there. They stay four predicates because the theorems take different subsets.
   What still wants the check is `Database.CtorTerms`: `Cmd.decl` is `Function.update`, so the
   dynamics allow a redeclaration, and `Proofs/Counterexamples.lean`'s `claim1` is one that breaks
   `FDatabase.Inv`. `FDatabase.ProgramLegal` carries the stronger `Cmd.DeclUnused`, from which
   `ProgramLegal.declsFresh` recovers `Program.DeclsFresh`.
3. **Settled: declaration is required.** `Signature.IsCtor` now asks for a declaration, so
   `Expr.eval` gets stuck on an undeclared name and `Program.Evaluable` is declare-before-use for
   free. What it cost is that `AllConstructors` no longer implies `Database.CtorTerms`, which is
   carried as a state invariant instead.
