import EgglogSemantics.Tests.Egg

/-!
# Differential test case generator

Writes one `.egg` file and one `.expected` file per case. `scripts/difftest.sh` runs
egglog on the former and diffs its `(print-size)` output against the latter.

Two kinds of case, over two fragments. The **curated** ones are the Redex `test.rkt`
programs plus a few variations, so they are only as good as whoever picked them. The
**random** ones are generated from a seed by a fixed linear congruential stream, which is
what removes that selection bias — the `redex-check` analogue the Redex had and this port
did not. Each kind covers both the constructor fragment and M9's `:merge` functions.

One invocation writes one case, so that a generated program which happens to blow up
cannot take the rest of the run down with it; the script applies a timeout per case.

Cases use nullary constructors rather than literals, since egglog's `i64` is a distinct
primitive sort while `Term.lit` shares a sort with applications here (see `Egg.lean`).

**Nothing here may emit a program egglog rejects.** A rejected program is not a failing
case but a missing one, and a generator quietly producing unrunnable programs is the
failure mode this file is written against — it once cost 34 of 60 random cases, when the
fragment still allowed bare variables. `writeCase` checks the one rule the generator could
plausibly break, `set`'s.
-/

open Egglog

/-- A nullary constructor. -/
private def C (f : FnName) : Expr := .app f []

private def add (a b : Expr) : Expr := .app "Add" [a, b]

/-! ### Curated cases -/

private def commuteRule : Rule where
  query := [.expr (add (.var "a") (.var "b"))]
  actions := [.union (add (.var "a") (.var "b")) (add (.var "b") (.var "a"))]

private def swapRule : Rule where
  query := [.expr (add (.var "a") (.var "b"))]
  actions := [.expr (add (.var "b") (.var "a"))]

private def detectRule : Rule where
  query := [.eq (.app "Wrapper" [add (C "One") (C "Two")])
                (.app "Wrapper" [add (C "Two") (C "One")])]
  actions := [.expr (.app "Success" [])]

private def assocRule : Rule where
  query := [.expr (add (add (.var "a") (.var "b")) (.var "c"))]
  actions := [.union (add (add (.var "a") (.var "b")) (.var "c"))
                     (add (.var "a") (add (.var "b") (.var "c")))]

private def curated : List (String × Program) :=
  [ ("actions",
      [.action (.expr (add (C "One") (C "Two"))),
       .action (.union (C "One") (C "One")),
       .action (.letBind "$g" (add (C "Two") (C "Three"))),
       .action (.expr (.app "Wrapper" [.var "$g"]))]),
    ("swap-1", [.action (.expr (add (C "One") (C "Two"))), .rule swapRule, .run]),
    ("swap-2", [.action (.expr (add (C "One") (C "Two"))), .rule swapRule, .run, .run]),
    ("wrapper-1",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run]),
    ("wrapper-2",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run, .run]),
    ("wrapper-3",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run, .run, .run]),
    ("assoc-1",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))), .rule assocRule, .run]),
    ("assoc-2",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))),
       .rule assocRule, .run, .run]),
    ("both-2",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))),
       .rule assocRule, .rule commuteRule, .run, .run]),
    ("seed-2", [.rule ⟨[], [.expr (add (C "One") (C "Two"))]⟩, .run, .run]) ]

/-! ### Random cases

A fixed signature — two nullary constructors, one unary, one binary — keeps every
generated program expressible in egglog, where one name may not be used at two arities.
Depths are small on purpose: a rule whose head builds a deep term grows the term set fast,
and the enumerator is |terms| ^ |vars|. -/

private def step (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- A number below `n`, and the advanced seed.

Read off the **high** bits. Bit `k` of a linear congruential generator with a
power-of-two modulus has period `2^(k+1)`, so `s % n` for a small `n` cycles almost
immediately: with `s % 4` every fourth draw agrees, and the merge cases were all emitting
the same `union` because of it. Discarding the low 16 bits is the usual fix. -/
private def pick (n : Nat) (s : Nat) : Nat × Nat :=
  let s := step s
  (s / 65536 % max n 1, s)

/-- A leaf: a nullary constructor, or one of `vars`. -/
private def genLeaf (vars : List Var) (s : Nat) : Expr × Nat :=
  let (i, s) := pick (2 + vars.length) s
  match i with
  | 0 => (C "A", s)
  | 1 => (C "B", s)
  | k => (.var (vars.getD (k - 2) "a"), s)

/-- A ground expression of depth at most `d`. -/
private def genGround : Nat → Nat → Expr × Nat
  | 0, s => genLeaf [] s
  | d + 1, s =>
    let (i, s) := pick 4 s
    match i with
    | 2 =>
      let (e, s) := genGround d s
      (.app "F" [e], s)
    | 3 =>
      let (e₁, s) := genGround d s
      let (e₂, s) := genGround d s
      (.app "G" [e₁, e₂], s)
    | _ => genLeaf [] s

/-- An expression of depth at most `d` whose leaves may be any of `vars`.

Weighted **towards building** rather than uniformly, at one leaf to two `F` to one `G`.
This is what a rule head is drawn from, so it is what decides whether a round's firings
grow the term set or just permute it: the cases worth having are the ones where a rule
matching everything builds a nested term and the next round matches that. Over the default
60 seeds the weighting takes the spread from 32 distinct row-count profiles to 38. -/
private def genOver (vars : List Var) : Nat → Nat → Expr × Nat
  | 0, s => genLeaf vars s
  | d + 1, s =>
    let (i, s) := pick 4 s
    match i with
    | 1 | 2 =>
      let (e, s) := genOver vars d s
      (.app "F" [e], s)
    | 3 =>
      let (e₁, s) := genOver vars d s
      let (e₂, s) := genOver vars d s
      (.app "G" [e₁, e₂], s)
    | _ => genLeaf vars s

/-- An expression whose top is a constructor application.

The model admits a bare variable as a query fact or as an `expr` action — it matches, or
adds, any term — where egglog's grammar does not. The fragment is therefore not a subset
of egglog's language, and the generator has to stay inside the overlap. -/
private def genApp (vars : List Var) (d : Nat) (s : Nat) : Expr × Nat :=
  -- Weighted away from a nullary top: `(A)` as a query matches at most one term, so a
  -- program full of them exercises almost nothing.
  let (i, s) := pick 6 s
  match i with
  | 0 => genLeaf [] s
  | 1 | 2 =>
    let (e, s) := genOver vars d s
    (.app "F" [e], s)
  | _ =>
    let (e₁, s) := genOver vars d s
    let (e₂, s) := genOver vars d s
    (.app "G" [e₁, e₂], s)

mutual

/-- Replace some subterms with variables. -/
private def abstractExpr (vars : List Var) : Expr → Nat → Expr × Nat
  | .app f args, s =>
    let (i, s) := pick 3 s
    match i, vars with
    | 0, v :: vs =>
      let (j, s) := pick (v :: vs).length s
      (.var ((v :: vs).getD j v), s)
    | _, _ =>
      let (args, s) := abstractArgs vars args s
      (.app f args, s)
  | e, s => (e, s)

private def abstractArgs (vars : List Var) : List Expr → Nat → List Expr × Nat
  | [], s => ([], s)
  | e :: es, s =>
    let (e, s) := abstractExpr vars e s
    let (es, s) := abstractArgs vars es s
    (e :: es, s)

end

/-- A pattern got by abstracting some subterms of `src` into variables, keeping `src`'s
root constructor.

Abstracting a term the program actually builds is what makes the rule fire: a freely
generated pattern of this shape almost never matches anything, which showed up as most
generated programs producing no rows beyond their seeded terms. Keeping the root is what
keeps it a legal egglog fact. -/
private def genPattern (vars : List Var) (src : Expr) (s : Nat) : Expr × Nat :=
  match src with
  | .app f args =>
    let (args, s) := abstractArgs vars args s
    (.app f args, s)
  | e => (e, s)

/-- A rule whose body is abstracted from `src`. The head is built only over variables the
body binds, so every generated program is well-scoped and neither engine rejects it. -/
private def genRule (src : Expr) (s : Nat) : Rule × Nat :=
  let (shape, s) := pick 3 s
  let (p, s) := genPattern ["a", "b"] src s
  match shape with
  | 0 =>
    -- one pattern, head builds a term
    let (a, s) := genApp p.vars 2 s
    (⟨[.expr p], [.expr a]⟩, s)
  | 1 =>
    -- one pattern, head unions two terms; `union` operands may be bare variables
    let (a₁, s) := genOver p.vars 2 s
    let (a₂, s) := genOver p.vars 2 s
    (⟨[.expr p], [.union a₁ a₂]⟩, s)
  | _ =>
    -- an equality body, so matching has to go through congruence
    let (q, s) := genPattern ["a", "b"] src s
    let (a, s) := genApp (p.vars ∪ q.vars) 2 s
    (⟨[.eq p q], [.expr a]⟩, s)

private def genProgram (s : Nat) : Program :=
  let (g₁, s) := genGround 2 s
  let (g₂, s) := genGround 3 s
  let (g₃, s) := genGround 3 s
  let (r₁, s) := genRule g₂ s
  let (r₂, s) := genRule g₃ s
  let (rounds, _) := pick 3 s
  -- The model keeps rules in a `Set` and so ignores a repeat; egglog panics on one.
  -- Compare the rendered form, there being no decidable equality on `Rule`.
  let rules := if r₁.toEgg = r₂.toEgg then [Cmd.rule r₁] else [Cmd.rule r₁, Cmd.rule r₂]
  [.action (.expr g₁), .action (.expr g₂), .action (.expr g₃)] ++ rules
    ++ List.replicate (rounds + 1) Cmd.run

/-! ### `:merge` cases (M9)

The first empirical check on M9. Every merge here is **idempotent**, and that is the only
exclusion the model justifies: `MergeStep` has no `a ≠ b` guard, so a row collides with
itself, and `:merge (+ old new)` therefore derives `2v`, `3v`, … forever where egglog with
a single `set` merges nothing. Such a program's egglog result is insertion-order-dependent
and there is no fixpoint to compare against, so a difference there would be this model's
design showing rather than a real bug.

**Non-commutative is not the same as non-idempotent**, and `:merge old` and `:merge new`
were wrongly excluded on that reading. They are idempotent, and unlike `+` they are
completely determined in egglog — `old` is the value already in the table, `new` the one
being inserted. Leaving them out left every merge in the suite commutative, which is
exactly why the model could bind the two colliding rows the wrong way round and stay
122-for-122 green. `genMergeSpec` draws them now, and the four curated cases below pin the
shapes that were checked against the binary.

No `:merge` **body** reads a table. An atom there would bind its variable to *any* recorded
output, where egglog binds the current one, so the model would fire more and build more;
`Spec/Scope.lean`'s "Reading in an action" rejects it statically. A body may still *write*
one, which is the `merge-body-*` family, and a rule body may read one, which is the
`read-*` family below.

`min-rebuild` is the case that matters: unioning the keys makes two `Dist` rows collide,
so egglog's table drops from two rows to one. It is the shape of
`egglog/tests/merge-during-rebuild.egg`, with nullary constructors in place of `(Node
i64)`. Row counts see it because they count *key classes*, which is also why the
interpreter need not saturate merges to predict them.
-/

private def dist (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [] [.app "min" [.var "old", .var "new"]] }

private def distMax (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [] [.app "max" [.var "old", .var "new"]] }

/-- The same join, written as egglog's **action block** — `let`-bind the combined value,
then return it.

Worth a case of its own because the emitter's block branch had never been exercised: all
seven original merge cases are `:merge (min old new)`, which takes the expression branch.
The block branch emitted two nested lists where egglog wants the actions and the result as
siblings, so every program using it was a parse error.

This is the only *non-writing* body shape. Writing ones — `set` and `union` — are the
`merge-body-*` cases below, and the reason they were once excluded ("a row collides with
itself and both orders fire") does not hold: `mergeRound` skips `r₁ == r₂`, and after
`(r₁, r₂)` fires, `r₁` is gone and `mergeOneWith`'s `rows.contains` test drops the
reversed pair. -/
private def distBlock (n : Nat) (op : FnName) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [.letBind "s" (.app op [.var "old", .var "new"])] [.var "s"] }

/-- `:merge old` / `:merge new`, the two merges no commutative one can distinguish. `old`
is the value already in the table and `new` the one being inserted. -/
private def distPick (n : Nat) (which : String) : FnDecl :=
  { arity := n, outArity := 1, merge := .merge [] [.var which] }

/-- `:no-merge`: a collision is an error rather than a resolution
(egglog panics with "Illegal merge attempted for function Dist"), so a case using it must
keep its keys distinct. Inert in the model, since `MergeStep` fires only on `.merge`. -/
private def distNoMerge (n : Nat) : FnDecl :=
  { arity := n, outArity := 1, merge := .noMerge }

private def num (n : Int) : Expr := .lit (.int n)

private def mset (f : FnName) (args : List Expr) (v : Int) : Cmd :=
  .action (.set f args [num v])

/-- A rule that copies a `Dist` entry onto the commuted key, so a merge fires from a rule
head as well as from a top-level action. -/
private def commuteDist : Rule where
  query := [.expr (.app "G" [.var "a", .var "b"])]
  actions := [.set "Dist" [.var "b", .var "a"] [num 9]]

/-! ### Multi-column outputs

`Row.out`, `Database.addRow`, `Database.Out` and `MergeSpec`'s result were multi-column
from the start; `Action.set` and `Pattern` were not, so a two-column row could be created
by a merge and never written or read. Both are now widened, and these are the cases that
exercise it — egglog's `(function f (Math) (i64 i64) …)`, `(set (f k) (values a b))` and
the tuple destructure `(= (values a b) (f k))`.

**What the oracle can and cannot see.** `(print-size)` reports one row per canonical *key*
tuple and is blind to value columns, so a row-count comparison validates that egglog
accepts the declaration, the two-column `set` and the destructure, and that the key classes
agree — it does not validate the merged values. `tuple-read` closes half of that gap
without a new oracle: its rule guards on *literal* value columns, so whether it fires is
observable in the count of the constructor its head builds. The other half — the merged
value after a real collision — is not observable through `print-size` at all, and needs
`(check (= (values …) …))`, which is a different oracle and a `Cmd.check` this fragment
does not have. -/
/-- A two-column merge function: `min` on column 0, `max` on column 1, which is what
`mergeEnvIdx`'s `old0`/`new0`/`old1`/`new1` naming is for. Emitted as
`(function Dist (Math…) (i64 i64) :merge (values (min old0 new0) (max old1 new1)))`. -/
private def distPair (n : Nat) : FnDecl :=
  { arity := n, outArity := 2,
    merge := .merge [] [.app "min" [.var "old0", .var "new0"],
                        .app "max" [.var "old1", .var "new1"]] }

private def pset (f : FnName) (args : List Expr) (v w : Int) : Cmd :=
  .action (.set f args [num v, num w])

/-- Reads a two-column row and builds a term from its *key*, gated on both value columns
being the literals written. Whether the rule fired is therefore visible in `Hit`'s row
count, which is what makes the value columns observable through `(print-size)`.

The keys are kept distinct so no merge ever fires on the guarded row. That is deliberate
and it is the fragment boundary `MERGE.md` draws: this model keeps every superseded output
where egglog deletes it, so after a collision a guard on the *pre-merge* value fires here
and not there. `MERGE.md`, "What the widening and the composed interpreter found", has the
minimal repro. -/
private def readPair : Rule where
  query := [.values [num 3, num 4] "Dist" [.var "k"]]
  actions := [.expr (.app "Hit" [.var "k"])]

/-! ### Reading a `:merge` function from a rule body

`MERGE.md` calls this the difftest fragment's boundary: every merge case so far *writes*
`Dist` and queries only constructors, so the read path — `MValidSubst.values`, reachable
through `execM` — had **no coverage at all**. That is the shape of the `min`/`max` bug: a
path the suite exercised zero times while the pass count said everything was fine.

Reading an analysis function in a rule body is ordinary egglog. Three shapes, all checked
against the binary:

* `(rule ((= o (Dist k))) …)` — existence. The value does not matter, so this agrees
  whatever the model does with superseded rows. egglog also writes this `(Dist k)` and
  compiles the two to the same atom; the model has only the atom, so it needs the output
  variable written out.
* `(rule ((= 3 (Dist k))) …)` — the value, with no collision. Also agrees.
* `(rule ((= 5 (Dist k))) …)` after a collision that merged `5` away — this is where
  keeping superseded rows shows.

All three are `Pattern.values`, which is the model's only read (`Spec/Scope.lean`,
"Reading in an action"); `Tests/Egg.lean` renders a one-column atom as `(= v (f k…))`. -/
/-- Existence: fires once per key class holding a row. The output variable is bound and
unused, which is what a bare `(Dist k)` compiles to. -/
private def readExists : Rule where
  query := [.values [.var "o"] "Dist" [.var "k"]]
  actions := [.expr (.app "Hit" [.var "k"])]

/-- The value: fires only where the recorded output is `v`. -/
private def readValue (v : Int) : Rule where
  query := [.values [num v] "Dist" [.var "k"]]
  actions := [.expr (.app "Hit" [.var "k"])]

/-- The two-column acceptance test's rule: guarded on the *pre-merge* value tuple. -/
private def readStale : Rule where
  query := [.values [num 5, num 1] "Dist" [.var "k"]]
  actions := [.expr (.app "Hit" [.var "k"])]

/-- Copy one merge function's value into another's row. The read is a query fact binding
`v` and the head only writes, which is the only shape egglog accepts for a rule and the
only shape the model accepts anywhere. -/
private def copyDist : Rule where
  query := [.values [.var "v"] "Dist" [.var "k"]]
  actions := [.set "Copy" [.var "k"] [.var "v"]]

/-! ### Making a value observable through a row count

`(print-size)` counts rows and never sees a value, so every case below that is *about* a
value pairs it with a ground read whose head builds a marker constructor: the marker's row
count is 1 exactly when the read fired, and 0 otherwise. This is `witnessRule`'s trick,
generalized over which function is read and which marker is built, because the new cases
read a *second* table — the one a `:merge` body writes.

Each such case states both the marker that must be 1 and one that must be 0. A single
positive marker only says "some value matched"; the negative one is what separates "the
model computed the wrong value" from "the model read nothing at all", since those differ in
the positive marker alone and not in the pair. -/
/-- `(rule ((= v (f key…))) ((hit key…)))`. Fires exactly when `f`'s row at `key` holds
`v`, so `hit`'s row count reports which value survived. The head reuses `key`, which is
ground, so the query costs one substitution and no enumeration. -/
private def readInto (hit f : FnName) (key : List Expr) (v : Int) : Rule where
  query := [.values [num v] f key]
  actions := [.expr (.app hit key)]

/-- `readInto` at a multi-column output. -/
private def readIntoW (hit f : FnName) (key : List Expr) (vs : List Int) : Rule where
  query := [.values (vs.map num) f key]
  actions := [.expr (.app hit key)]

/-! ### Primitives outside a `:merge` body

Every primitive application in the suite used to sit inside a `:merge` body, and that was
not a choice about coverage — the emitter could not render one anywhere else. `fnArities`
fed every applied name into the `datatype` header, so a program applying `min` in an action
emitted `(datatype Math (min Math Math) …)` and egglog answered `Primitive min already
declared.` before running a line of it. None of `writeCase`'s four guards caught it, since
none of them is about the header.

With `Prim.ofName` filtered out of `fnArities` the whole position opens up, and it is
ordinary egglog: `(set (Dist (K)) (min 5 3))` is an `i64` expression in a value column,
which is where `tests/interval.egg` puts one too.

**What the oracle sees.** `min` and `max` are the one place the model *computes* rather
than *builds* (`Prim.apply` against `Expr.MEval.ctor`), so the three ways to get this wrong
are to build the term `min(5, 3)`, to compute the wrong operation, or to compute nothing.
Each case reads the answer back at a literal and builds `Hit`, and reads the operand that
must have lost and builds `Miss`: building a term or getting stuck gives `Hit 0, Miss 0`,
and computing `max` for `min` gives `Hit 0, Miss 1`. -/
/-- Seeds a term the rule-head case's query can match. -/
private def seedF : Cmd := .action (.expr (.app "F" [C "A"]))

/-! ### `:merge` bodies that write

`MERGE.md` drew the fragment boundary at "bodies stay `let`-only", on the grounds that a
body which `set`s a side table would fire on self-collisions and in both orders and so
inflate that table's count. Neither happens: `mergeRound` skips `r₁ == r₂`, and after the
pair `(r₁, r₂)` fires, `r₁` is gone from the accumulator, so `mergeOneWith`'s
`rows.contains` test drops the reversed pair. What was left behind by the boundary is the
shape the whole proof encoding is built on — egglog's union-find `:merge`, which writes.
egglog typechecks a body under `Context::Write`, so `set` and `union` are both legal there,
and both were checked against the release binary before being generated.

**What the oracle sees**, per body action:

* a `set` into `Log` at the key `(L)` — `L` and `Log` are used *nowhere else in the
  program*, so both row counts are 0 if the body never ran and 1 if it did. That alone
  separates "runs the body" from "ignores it". `Hit`/`Miss` then read `Log`'s value, which
  is `old` or `new` according to the body, so the pair also reports which of the two
  colliding rows the model called which — the `old`/`new` bug, now inside a body.
* a `union (U) (V)` — `W` is seeded at both, so `W`'s count is 2 if the body never ran and
  1 if it did. This is the union-find merge in miniature: the body's whole effect is an
  equality, and an equality is exactly what a row count can see.

`merge-body-inert` is the negative control: the same declaration with no collision ever
reached, where `L`, `Log` and `W` must report the body *not* having run. Without it a model
that ran the body unconditionally would pass every other case in this family. -/
/-- The side table a body writes into. `min` rather than `old`/`new` on purpose: a case
with several collisions logs several values, and the count of collisions is the one thing
the two engines are not obliged to agree on, so the *combination* has to be
order-insensitive for the value read to mean anything. -/
private def logDecl : FnDecl :=
  { arity := 1, outArity := 1,
    merge := .merge [] [.app "min" [.var "old", .var "new"]] }

/-- A merge that logs one of the colliding values into `Log` and returns the other. -/
private def distLog (n : Nat) (logged kept : String) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [.set "Log" [C "L"] [.var logged]] [.var kept] }

/-- A merge whose body is `(union (U) (V))` — the body's entire effect is an equality, as
in a union-find's. -/
private def distUnion (n : Nat) (kept : String) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [.union (C "U") (C "V")] [.var kept] }

/-- A two-action body: `let` the combined value, log it, return it. Exercises the block
form at more than one action, and the `let`-bound variable as a `set`'s value. -/
private def distLetLog (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [.letBind "s" (.app "min" [.var "old", .var "new"]),
                     .set "Log" [C "L"] [.var "s"]] [.var "s"] }

/-- Seeds `W` at both operands of a body's `union`, so that `W`'s row count falls from 2 to
1 exactly when the body runs. -/
private def seedW : List Cmd :=
  [.action (.expr (.app "W" [C "U"])), .action (.expr (.app "W" [C "V"]))]

/-! ### Widths and arities the suite never drew

Every `:merge` function in the suite had one or two key columns and one or two value
columns. Three gaps followed, each a distinct branch:

* **arity 0.** `(function Zero () i64 …)` renders an empty key list, and its one key class
  is the empty tuple — `congrKeys` at length zero, which nothing had run.
* **arity 3.** Three key columns, collided through a `union` on the third, so
  `congrKeys` has to walk past two equal columns to a congruent one.
* **value width 3.** `mergeEnvIdx` binds `old0`/`new0`/`old1`/`new1`/`old2`/`new2`, and only
  the first two pairs had ever been read. The width-3 case's merge uses all three, one per
  column and a different combiner in each, so a body reading the wrong index computes a
  different tuple and the guarded read stops firing.

Eq-sorted merge outputs are deliberately still absent. They would need `ordering-min` to
render, and `Term.blt` is structural where egglog's is by insertion order — a known
divergence (`Tests/Egg.lean`, `FnDecl.toEgg`) rather than an untested path. -/
/-- A three-column merge: a different combiner per column, so every `mergeEnvIdx` binding
is load-bearing. -/
private def distTriple (n : Nat) : FnDecl :=
  { arity := n, outArity := 3,
    merge := .merge [] [.app "min" [.var "old0", .var "new0"],
                        .app "max" [.var "old1", .var "new1"],
                        .var "old2"] }

private def tset (f : FnName) (args : List Expr) (vs : List Int) : Cmd :=
  .action (.set f args (vs.map num))

private def curatedMerge : List (String × Program) :=
  [ -- One key, three writes: min wins, and the table still holds one row.
    ("min-one",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       mset "Dist" [C "A"] 7]),
    -- Two distinct keys stay two rows.
    ("min-two",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 5, mset "Dist" [C "B"] 3]),
    -- `merge-during-rebuild`: unioning the keys collapses two rows into one.
    ("min-rebuild",
      [.decl "Dist" (dist 2),
       mset "Dist" [C "X", C "Y"] 1, mset "Dist" [C "A", C "B"] 2,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run]),
    -- The same collapse, with `max`.
    ("max-rebuild",
      [.decl "Dist" (distMax 2),
       mset "Dist" [C "X", C "Y"] 1, mset "Dist" [C "A", C "B"] 2,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run]),
    -- A congruence-driven collapse: the keys become equal through `G`, not directly.
    ("min-congr",
      [.decl "Dist" (dist 1),
       .action (.expr (.app "G" [C "A", C "B"])),
       .action (.expr (.app "G" [C "X", C "Y"])),
       mset "Dist" [.app "G" [C "A", C "B"]] 4,
       mset "Dist" [.app "G" [C "X", C "Y"]] 6,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run]),
    -- A rule head writing a row, so the merge fires from a firing rather than an action.
    ("min-rule",
      [.decl "Dist" (dist 2),
       .action (.expr (.app "G" [C "A", C "B"])),
       .action (.expr (.app "G" [C "B", C "A"])),
       mset "Dist" [C "B", C "A"] 2,
       .rule commuteDist, .run]),
    -- No merge fires at all: the declaration is inert, which the counts must show.
    ("min-inert",
      [.decl "Dist" (dist 1), .action (.expr (.app "F" [C "A"])),
       mset "Dist" [C "A"] 1]),
    -- `min-one` with the merge written as an action block, which is a different parse.
    ("min-block",
      [.decl "Dist" (distBlock 1 "min"), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       mset "Dist" [C "A"] 7]),
    -- An action block resolving a collision the keys only acquire through a union.
    ("max-block-rebuild",
      [.decl "Dist" (distBlock 2 "max"),
       mset "Dist" [C "X", C "Y"] 1, mset "Dist" [C "A", C "B"] 2,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run]),
    -- `:no-merge`, with keys kept distinct so no collision is ever attempted.
    ("nomerge-two",
      [.decl "Dist" (distNoMerge 2), .action (.expr (.app "F" [C "A"])),
       mset "Dist" [C "A", C "B"] 1, mset "Dist" [C "B", C "A"] 2]),
    -- Two value columns, two distinct keys: the declaration, the `(values …)` merge and
    -- the two-column `set` all have to parse and typecheck for this to run at all.
    ("tuple-two",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 3 4, pset "Dist" [C "B"] 5 6]),
    -- The same, plus a collision on one key. Only the key classes are compared — see the
    -- note above on what `(print-size)` can see.
    ("tuple-merge",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 5 1, pset "Dist" [C "A"] 3 7,
       pset "Dist" [C "B"] 2 2]),
    -- A rule *reading* a two-column row through the destructure, gated on both value
    -- columns. `Hit` is 1 iff the read bound the columns the `set` wrote.
    ("tuple-read",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 3 4, pset "Dist" [C "B"] 5 6,
       .rule readPair, .run]),
    -- The destructure through congruent keys: `A` and `X` become one class, so the row
    -- written at `X` is readable at `A`.
    ("tuple-read-congr",
      [.decl "Dist" (distPair 1), pset "Dist" [C "X"] 3 4,
       .action (.expr (C "A")), .action (.union (C "A") (C "X")),
       .rule readPair, .run]),
    -- A rule body *reading* a single-column `:merge` function: existence only.
    ("read-exists",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 3, mset "Dist" [C "B"] 5,
       .rule readExists, .run]),
    -- The same, reading the value, with the keys distinct so no merge fires.
    ("read-value",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 3, mset "Dist" [C "B"] 5,
       .rule (readValue 3), .run]),
    -- **The acceptance test, single column.** `5` is merged away by `min`, so egglog's
    -- table no longer holds it and the rule must not fire.
    ("read-stale",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       .rule (readValue 5), .run]),
    -- **The acceptance test, two columns.** The repro that was recorded in `MERGE.md` as
    -- a known divergence: egglog says `Hit 0`, and an append-only implementation says
    -- `Hit 1` because the superseded row is still readable.
    ("tuple-stale",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 5 1, pset "Dist" [C "A"] 3 7,
       .rule readStale, .run]),
    -- A single-column read through *congruent* keys: the row is written at `X`, read at
    -- `A`. `tuple-read-congr` covers the two-column case; this is the one-column one, and
    -- both reach `patternHoldsM`'s row scan through its key-congruence test.
    ("read-congr",
      [.decl "Dist" (dist 1), mset "Dist" [C "X"] 3,
       .action (.expr (C "A")), .action (.union (C "A") (C "X")),
       .rule readExists, .run]),
    -- The same, reading the value rather than only its existence.
    ("read-value-congr",
      [.decl "Dist" (dist 1), mset "Dist" [C "X"] 3,
       .action (.expr (C "A")), .action (.union (C "A") (C "X")),
       .rule (readValue 3), .run]),
    -- Reading a `:no-merge` function. A row atom reads any declared function, so
    -- `:no-merge` is readable too, and `nomerge-two` only ever writes one.
    ("read-nomerge",
      [.decl "Dist" (distNoMerge 1), mset "Dist" [C "A"] 3, mset "Dist" [C "B"] 5,
       .rule (readValue 3), .run]),
    -- Copying one merge function's value into another's row, which is what `read-copy`
    -- used to do from a top-level action. All reading happens in the query, so the read is
    -- `(= v (Dist k))` and the head only writes — the shape egglog requires of a rule and
    -- the model now requires everywhere (`Spec/Scope.lean`, "Reading in an action").
    ("read-copy",
      [.decl "Dist" (dist 1), .decl "Copy" (dist 1), mset "Dist" [C "A"] 3,
       .rule copyDist, .run,
       .action (.expr (.app "F" [C "A"]))]),
    -- **The `old`/`new` cases.** `(print-size)` cannot see a value, so each reads back the
    -- value egglog keeps: `Hit` is 1 exactly when the surviving output is that one. These
    -- are the four shapes that caught the model binding `old` and `new` backwards, each
    -- checked against the binary; a commutative merge cannot express any of them.
    -- Three writes at one key: egglog keeps the first, `5`.
    ("old-three",
      [.decl "Dist" (distPick 1 "old"), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       mset "Dist" [C "A"] 7, .rule (readValue 5), .run]),
    -- The same, keeping the last, `7`.
    ("new-three",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       mset "Dist" [C "A"] 7, .rule (readValue 7), .run]),
    -- Rebuild-driven: the collision arrives with the `union`, not with the `set`.
    ("old-rebuild",
      [.decl "Dist" (distPick 1 "old"), mset "Dist" [C "A"] 1, mset "Dist" [C "B"] 2,
       .action (.union (C "A") (C "B")), .rule (readValue 1), .run]),
    ("new-rebuild",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "A"] 1, mset "Dist" [C "B"] 2,
       .action (.union (C "A") (C "B")), .rule (readValue 2), .run]),
    -- Rule-head-driven, over two rounds: the head writes `9`, and the second round's read
    -- sees it only under `:merge new`. `Hit` is 0 in the `old` case, in both engines.
    ("old-rule",
      [.decl "Dist" (distPick 1 "old"), mset "Dist" [C "A"] 4,
       .rule ⟨[.expr (C "A")], [.set "Dist" [C "A"] [num 9]]⟩,
       .rule (readValue 9), .run, .run]),
    ("new-rule",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "A"] 4,
       .rule ⟨[.expr (C "A")], [.set "Dist" [C "A"] [num 9]]⟩,
       .rule (readValue 9), .run, .run]),
    -- Three rows in one key class, reached by two unions. This is the shape that says the
    -- survivor of a collision keeps the *older* row's place: merge the first two and the
    -- result must still count as older than the third.
    ("old-threeway",
      [.decl "Dist" (distPick 1 "old"), mset "Dist" [C "X"] 1, mset "Dist" [C "Y"] 2,
       mset "Dist" [C "Z"] 3, .action (.union (C "X") (C "Y")),
       .action (.union (C "Y") (C "Z")), .rule (readValue 1), .run]),
    ("new-threeway",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "X"] 1, mset "Dist" [C "Y"] 2,
       mset "Dist" [C "Z"] 3, .action (.union (C "X") (C "Y")),
       .action (.union (C "Y") (C "Z")), .rule (readValue 3), .run]),
    -- **Primitives outside a `:merge` body.** `min` in a top-level `set`'s value column.
    -- `Hit 1, Miss 0` says the model computed `3`; building the term `min(5, 3)` or getting
    -- stuck gives `0, 0` and computing `max` gives `0, 1`.
    ("prim-set-min",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [C "K"] [.app "min" [num 5, num 3]]),
       .rule (readInto "Hit" "Dist" [C "K"] 3), .rule (readInto "Miss" "Dist" [C "K"] 5),
       .run]),
    -- The same with `max`, so the two markers swap: a model computing `min` for `max`
    -- is caught here even though it passes `prim-set-min`.
    ("prim-set-max",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [C "K"] [.app "max" [num 5, num 3]]),
       .rule (readInto "Hit" "Dist" [C "K"] 5), .rule (readInto "Miss" "Dist" [C "K"] 3),
       .run]),
    -- Nested: `(min (max 5 3) 4)` is `4`, so the operand list itself has to be evaluated
    -- through `MEvalList` before the outer primitive applies. `Miss` reads `5`, the value
    -- an unevaluated inner application would have left.
    ("prim-nested",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [C "K"] [.app "min" [.app "max" [num 5, num 3], num 4]]),
       .rule (readInto "Hit" "Dist" [C "K"] 4), .rule (readInto "Miss" "Dist" [C "K"] 5),
       .run]),
    -- A primitive under a top-level `let`, so the value reaches the row through the global
    -- environment rather than directly. The `$` prefix is egglog's convention for a global
    -- and avoids its "Global `g` should start with `$`" warning.
    ("prim-let",
      [.decl "Dist" (dist 1),
       .action (.letBind "$g" (.app "min" [num 7, num 2])),
       .action (.set "Dist" [C "K"] [.var "$g"]),
       .rule (readInto "Hit" "Dist" [C "K"] 2), .rule (readInto "Miss" "Dist" [C "K"] 7),
       .run]),
    -- A primitive in a **rule head**, which is the position `Rule.noLookup` polices and so
    -- the one most likely to be rejected by mistake. Two rounds: the first fires the write,
    -- the second reads it back.
    ("prim-rule-head",
      [.decl "Dist" (dist 1), seedF,
       .rule ⟨[.expr (.app "F" [.var "a"])],
              [.set "Dist" [.var "a"] [.app "max" [num 5, num 3]]]⟩,
       .rule (readInto "Hit" "Dist" [C "A"] 5), .rule (readInto "Miss" "Dist" [C "A"] 3),
       .run, .run]),
    -- **A `:merge` body that writes.** The body logs `old` into a side table and returns
    -- `new`. `L 1` and `Log 1` say the body ran at all — both names occur nowhere else —
    -- and `Hit 1, Miss 0` say it logged `5`, the value already in the table.
    ("merge-body-set-old",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "old" "new"),
       mset "Dist" [C "K"] 5, mset "Dist" [C "K"] 3,
       .rule (readInto "Hit" "Log" [C "L"] 5), .rule (readInto "Miss" "Log" [C "L"] 3),
       .rule (readInto "Won" "Dist" [C "K"] 3), .run]),
    -- The mirror: log `new`, keep `old`. Both markers move, which is what makes the pair
    -- distinguish the two bindings rather than merely detecting that something was logged.
    ("merge-body-set-new",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "new" "old"),
       mset "Dist" [C "K"] 5, mset "Dist" [C "K"] 3,
       .rule (readInto "Hit" "Log" [C "L"] 3), .rule (readInto "Miss" "Log" [C "L"] 5),
       .rule (readInto "Won" "Dist" [C "K"] 5), .run]),
    -- A two-action body: `let`, then `set` the bound variable, then return it. Exercises
    -- the block renderer past one action and a `let`-bound value flowing into a `set`.
    ("merge-body-let-set",
      [.decl "Log" logDecl, .decl "Dist" (distLetLog 1),
       mset "Dist" [C "K"] 5, mset "Dist" [C "K"] 3,
       .rule (readInto "Hit" "Log" [C "L"] 3), .rule (readInto "Miss" "Log" [C "L"] 5),
       .rule (readInto "Won" "Dist" [C "K"] 3), .run]),
    -- The body's effect is an **equality**: `W` is seeded at `(U)` and at `(V)`, so `W 1`
    -- says the union ran and `W 2` says it did not. This is the union-find `:merge`.
    ("merge-body-union",
      [.decl "Dist" (distUnion 1 "new")] ++ seedW ++
      [mset "Dist" [C "K"] 5, mset "Dist" [C "K"] 3,
       .rule (readInto "Won" "Dist" [C "K"] 3), .run]),
    -- The same, with the collision arriving from a `union` on the *keys* during rebuild
    -- rather than from a repeated `set`, so the body runs from the merge phase.
    ("merge-body-union-rebuild",
      [.decl "Dist" (distUnion 1 "old")] ++ seedW ++
      [mset "Dist" [C "X"] 1, mset "Dist" [C "Y"] 2, .action (.union (C "X") (C "Y")),
       .rule (readInto "Won" "Dist" [C "X"] 1), .run]),
    -- A writing body driven by a rebuild collision: `Log` records `old`, which
    -- `old-rebuild` pins to the earlier write.
    ("merge-body-set-rebuild",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "old" "new"),
       mset "Dist" [C "X"] 1, mset "Dist" [C "Y"] 2, .action (.union (C "X") (C "Y")),
       .rule (readInto "Hit" "Log" [C "L"] 1), .rule (readInto "Miss" "Log" [C "L"] 2),
       .run]),
    -- **The negative control.** The same writing body, but the keys never collide, so `L`,
    -- `Log` and `W` must all report the body having *not* run. Without this a model that
    -- ran a body unconditionally would pass every other case in the family.
    ("merge-body-inert",
      [.decl "Log" logDecl, .decl "Dist" (distLog 2 "old" "new")] ++ seedW ++
      [mset "Dist" [C "A", C "B"] 1, mset "Dist" [C "B", C "A"] 2,
       .rule (readInto "Hit" "Log" [C "L"] 1), .run]),
    -- **Arity 0.** One key class, and it is the empty tuple — `congrKeys` at length zero.
    ("merge-arity0",
      [.decl "Zero" (dist 0), mset "Zero" [] 5, mset "Zero" [] 3,
       .rule (readInto "Hit" "Zero" [] 3), .rule (readInto "Miss" "Zero" [] 5), .run]),
    -- Arity 0 with a writing body, so the empty key tuple and the side table meet.
    ("merge-arity0-body",
      [.decl "Log" logDecl, .decl "Zero" (distLog 0 "old" "new"),
       mset "Zero" [] 5, mset "Zero" [] 3,
       .rule (readInto "Hit" "Log" [C "L"] 5), .rule (readInto "Miss" "Log" [C "L"] 3),
       .run]),
    -- **Arity 3**, collided on the third column through a `union`, so the key comparison
    -- has to walk two equal columns before reaching a congruent one.
    ("merge-arity3",
      [.decl "Dist" (dist 3),
       mset "Dist" [C "A", C "B", C "X"] 5, mset "Dist" [C "A", C "B", C "Y"] 3,
       .action (.union (C "X") (C "Y")),
       .rule (readInto "Hit" "Dist" [C "A", C "B", C "X"] 3),
       .rule (readInto "Miss" "Dist" [C "A", C "B", C "X"] 5), .run]),
    -- **Value width 3**, one combiner per column: `min` on 0, `max` on 1, `old` on 2. A
    -- body reading the wrong `mergeEnvIdx` index computes a different tuple, and the
    -- guarded read then stops firing.
    ("tuple-three",
      [.decl "Dist" (distTriple 1), tset "Dist" [C "A"] [5, 1, 7],
       tset "Dist" [C "A"] [3, 9, 2],
       .rule (readIntoW "Hit" "Dist" [C "A"] [3, 9, 7]),
       .rule (readIntoW "Miss" "Dist" [C "A"] [5, 1, 7]), .run]) ]

/-! ### Random `:merge` cases

The curated merge cases are only as good as whoever picked them — the caveat the
constructor cases carried until they were randomized, and the same fix. These draw a
merge function's arity and its merge spec from the same seeded stream, write rows at
generated keys, and union constructors underneath those keys, which is what makes keys
collide and so what the counts actually discriminate on.

The fragment stays the one `MERGE.md` describes, and both narrowings are justified by the
model rather than by convenience:

* **Every drawn merge is idempotent** (`min`, `max`, `old`, `new`). A non-idempotent one
  diverges under our over-approximating reads *by design* — a row collides with itself, so
  `:merge (+ old new)` derives `2v`, `3v`, … — so a difference would be the design showing,
  not a bug. Being non-*commutative* is no such excuse, and `old`/`new` are drawn: a
  commutative merge cannot tell which colliding row the model calls `old`.
* **Merge functions are written and never read** by a *body*, since a body atom reading one
  binds any recorded output where egglog binds the current one. Reading one from a rule
  body is ordinary egglog and `genMergeReadRule` does it.

`MERGE.md`'s third narrowing, "bodies are `let`-only", is **gone as a statement about the
model** — the reason it gave is wrong. A body that `set`s a side table does not fire on
self-collisions (`mergeRound` skips `r₁ == r₂`) and does not fire in both orders (once
`(r₁, r₂)` has fired, `r₁` is gone and `mergeOneWith`'s `rows.contains` test drops
`(r₂, r₁)`). The `merge-body-*` cases above generate writing bodies — `set`, `union`, and a
`let`/`set` block — and the two engines agree on all of them. `genMergeSpec` still does not
draw one, for a different and narrower reason recorded there.

Keys are eq-sorted and outputs are `i64`, as the curated cases already are.

**Three divergences this family reaches and does not currently draw.** Each was found by
widening the draw, minimized by hand against the release binary, and is held out here
rather than fixed, because two of the three are in the model's interpreter rather than in
anything this file owns.

1. **A read atom's operands are not interned before the congruence test.**
   `Impl/Merge.lean`'s `patternHoldsM` computes `cl := d.closureF` in its `.values` case and
   compares the evaluated key against each row, where its `.expr` and `.eq` cases first add
   the evaluated term (`(d.addTerm t).closureF`). A key expression the program never built
   is therefore in no congruence class and matches nothing:
   ```
   (set (Dist (G (B) (A))) 4) (union (A) (B))
   (rule ((= o (Dist (G (A) (B))))) ((Hit (A))))
   ```
   egglog flattens the fact to `G(a, b, x), Dist(x, o)` and matches through congruence,
   answering `Hit 1`; the model answers `Hit 0`. Reachable from `genMergeReadRule`'s
   free-key draw, which is how it turned up.
2. **`old`/`new` at a rebuild collision follow insertion age here and key canonicity
   there.** `mergeOneWith` takes the row that was inserted earlier as `old`. egglog takes
   the row whose key is *already canonical* as `old` and the row being re-inserted because
   its key moved as `new`. The two agree whenever the younger row sits at the younger key,
   which every curated case does, and disagree otherwise:
   ```
   (function Dist (Math) i64 :merge new)
   (A) (set (Dist (K)) 3) (set (Dist (A)) 2) (union (A) (K))
   ```
   egglog keeps `3` — the earlier write, at the younger key — and the model keeps `2`.
3. **A no-op collision**, which only a writing body can observe; see `genMergeSpec`. -/

/-- The merge specs the generator draws from: `:merge old` and `:merge new`, then `min`
and `max`, each of the latter in the expression form and in the action-block form.

`old` and `new` are the two **non-commutative** merges, and they are here because a
commutative one cannot see which of the colliding rows the model calls `old`. The model
had them backwards — `:merge old` returned what `:merge new` should — and 122 green cases
said nothing, because every merge they drew was `min` or `max`. They are still joins in
the sense that matters here (`merge v v = v`, so a pass settles), and they are exactly as
deterministic in egglog as `min` is: `old` is the value already in the table and `new` the
one being inserted.

A difference shows through `(print-size)` because `genMergeReadRule` guards on the value:
a rule reading `(= v (Dist k))` fires or does not according to which value survived the
collision, and its head's `Hit` rows are counted.

**Writing bodies are still not drawn here**, and the reason is no longer the one `MERGE.md`
gave — `merge-body-*` above generates them and they agree — but a `no-op collision`, which
only a *writing* body can observe:

```
(function Log (Math) i64 :merge (min old new))
(function Dist () i64 :merge ((set (Log (L)) old) new))
(L) (set (Dist) 2) (set (Dist) 2)
```

egglog runs the body and answers `Log 1`; this model dedups the two identical rows, so
there is no pair for `mergeRound` to fire on, and it answers `Log 0`. Worse, the row egglog
writes is keyed on a **dangling e-class**: with any other constructor around, the key prints
as that unrelated constructor, and `(extract)` reports `Unextractable root Value(2) with
sort EqSort { name: "Math" }`. Every curated case above therefore keeps its colliding values
distinct, which is a condition a random draw over keys, values and a rule head cannot be
held to. -/
private def genMergeSpec (s : Nat) : MergeSpec × Nat :=
  let (i, s) := pick 6 s
  match i with
  | 0 => (.merge [] [.var "old"], s)
  | 1 => (.merge [] [.var "new"], s)
  | k =>
    let combined : Expr := .app (if k % 2 == 0 then "min" else "max") [.var "old", .var "new"]
    if k < 4 then (.merge [] [combined], s)
    else (.merge [.letBind "s" combined] [.var "s"], s)

/-- `n` ground key expressions. Shallow: a key is a term like any other, so a deep one
inflates the term set the enumerator squares. -/
private def genKeys : Nat → Nat → List Expr × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (e, s) := genGround 1 s
    let (es, s) := genKeys k s
    (e :: es, s)

/-- `n` key expressions over `vars`, for a `set` in a rule head. A bare variable is fine
in an *argument* position — the ban is on a bare variable as a whole query fact or a whole
`expr` action, which is where egglog's grammar stops. -/
private def genKeysOver (vars : List Var) : Nat → Nat → List Expr × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (e, s) := genOver vars 1 s
    let (es, s) := genKeysOver vars k s
    (e :: es, s)

/-- A rule writing a `Dist` row, so a merge fires from a firing and not only from a
top-level action. The body is abstracted from a term the program builds, so it fires. -/
private def genMergeRule (arity : Nat) (src : Expr) (s : Nat) : Rule × Nat :=
  let (p, s) := genPattern ["a", "b"] src s
  let (ks, s) := genKeysOver p.vars arity s
  let (v, s) := pick 9 s
  (⟨[.expr p], [.set "Dist" ks [num v]]⟩, s)

/-- Reads back the value the program wrote *first*, at the key it wrote it at, and builds
`Won` if it is still there.

Drawn from nothing: every generated case gets this rule. It is what makes a merge's
**answer** observable through an oracle that only counts rows — `Won` is 1 exactly when the
first write survived the collision, so `:merge old` and `:merge new` differ by a row here
and are indistinguishable everywhere else. `genMergeReadRule` cannot do the job, because it
draws its key and value and so reports on a collision only by luck: with the model binding
`old` and `new` backwards, all 30 generated merge cases still passed.

The query is ground, so it costs one substitution and no enumeration. -/
private def witnessRule (key : List Expr) (val : Nat) : Rule where
  query := [.values [num val] "Dist" key]
  actions := [.expr (.app "Won" key)]

/-- A rule *reading* `Dist` from its body: a `Pattern.values` atom whose value column is
either a fresh variable (existence) or the literal the program wrote (the value). Its head
builds a `Hit`, so whether and how often it fired is visible in `(print-size)`.

This is the path `MERGE.md` called the fragment boundary — "merge functions are written
and never read" — and leaving it there meant the read path, reachable through `execM` from
`MValidSubst`, had **no** coverage. Reading an analysis function in a rule body is ordinary
egglog, so there was no reason for the boundary except that nothing had run the merge
implementation.

`key` and `val` are a key the program actually writes and the value it writes there, and
the draw prefers them to freshly generated ones — the same correction `genPattern` needed
and for the same reason. A freely drawn key hits a written one by luck, and a freely drawn
value matches by one chance in nine, so most reads returned nothing: with the free draw
only 6 of 30 generated cases had the read fire at all, which is coverage of the *failing*
branch of a lookup and not of a lookup. -/
private def genMergeReadRule (arity : Nat) (src : Expr) (key : List Expr) (val : Nat)
    (s : Nat) : Rule × Nat :=
  let (p, s) := genPattern ["a", "b"] src s
  let (useKey, s) := pick 3 s
  let (ks, s) := if useKey = 0 then genKeysOver p.vars arity s else (key, s)
  let (useVal, s) := pick 3 s
  let (v, s) := if useVal = 0 then pick 9 s else (val, s)
  let (shape, s) := pick 2 s
  let body : Query :=
    if shape = 0 then [.expr p, .values [.var "o"] "Dist" ks]
    else [.expr p, .values [num v] "Dist" ks]
  (⟨body, [.expr (.app "Hit" [p])]⟩, s)

private def genMergeProgram (s : Nat) : Program :=
  let (a, s) := pick 2 s
  let arity := a + 1
  let (spec, s) := genMergeSpec s
  let (g, s) := genGround 2 s
  let (k₁, s) := genKeys arity s
  -- Half the cases write the second row at the *first* row's key, which is the only way a
  -- collision is certain: two freely drawn keys are usually distinct and the `union` below
  -- only sometimes brings them together. It is also what makes `old`/`new` observable —
  -- the read rule below is over `k₁`/`v₁`, so it reports which of the two writes survived.
  let (sameKey, s) := pick 2 s
  let (k₂', s) := genKeys arity s
  let k₂ := if sameKey = 0 then k₁ else k₂'
  let (k₃, s) := genKeys arity s
  let (v₁, s) := pick 9 s
  let (v₂, s) := pick 9 s
  let (v₃, s) := pick 9 s
  let (u₁, s) := genGround 1 s
  let (u₂, s) := genGround 1 s
  let (r, s) := genMergeRule arity g s
  let (rr, s) := genMergeReadRule arity g k₁ v₁ s
  let (rounds, _) := pick 2 s
  [ .decl "Dist" { arity := arity, outArity := 1, merge := spec },
    .action (.expr g),
    .action (.set "Dist" k₁ [num v₁]),
    .action (.set "Dist" k₂ [num v₂]),
    .action (.set "Dist" k₃ [num v₃]),
    .action (.union u₁ u₂),
    .rule r, .rule rr, .rule (witnessRule k₁ v₁) ]
    ++ List.replicate (rounds + 1) Cmd.run

/-! ### Entry point -/

/-- Write one case, refusing outright to emit a program egglog would reject.

A rejected program is not a failing case but a missing one, and a generator that quietly
stops producing runnable programs is the failure this whole file is written against — so
each check is an abort, not a skip. Three rules, all raised by egglog's typechecker before
the offending command runs:

* `set`'s: `(set (f args…) v)` is legal only on a declared function, and is a type error on
  a constructor or a relation (`Program.illegalSets`);
* every use of a declared function has its declared key and value column counts
  (`Program.arityErrors`, over `Spec/Scope.lean`'s `Cmd.arityOk`);
* nothing reads a row except a `Pattern.values` atom (`Program.illegalReads`, over
  `Cmd.noLookup`) — egglog rejects this in a rule head, and the model everywhere;
* no name is used at two key arities, which the emitted `datatype` header cannot express
  (`Program.arityConflicts`). -/
private def writeCase (dir name : String) (p : Program) : IO Unit := do
  unless p.illegalSets.isEmpty do
    throw <| IO.userError
      s!"difftest: {name} sets {p.illegalSets}, which egglog rejects: only a function \
         declared with :merge or :no-merge may be set"
  unless p.arityErrors.isEmpty do
    throw <| IO.userError
      s!"difftest: {name} has commands whose column counts egglog rejects: {p.arityErrors}"
  unless p.illegalReads.isEmpty do
    throw <| IO.userError
      s!"difftest: {name} has commands that read a row outside a query atom: \
         {p.illegalReads}"
  unless p.arityConflicts.isEmpty do
    throw <| IO.userError
      s!"difftest: {name} uses {p.arityConflicts} at more than one arity, which egglog \
         rejects with \"Function already bound\""
  IO.FS.writeFile s!"{dir}/{name}.egg" p.toEgg
  IO.FS.writeFile s!"{dir}/{name}.expected" p.expectedSizes

/-- `difftest <dir> curated` writes the curated cases, `difftest <dir> merge` the curated
`:merge` ones; `difftest <dir> seed <n>` writes one random constructor case named
`rand-<n>` and `difftest <dir> mergeseed <n>` one random `:merge` case named `mrand-<n>`.
The two random families are named apart so the script can report a profile distribution
for each — a collapsing distribution is how a generator that has stopped exercising
anything shows up, and a single pooled number would hide it. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [dir, "curated"] =>
    IO.FS.createDirAll dir
    for (name, p) in curated do writeCase dir name p
    IO.println s!"wrote {curated.length} curated cases"
    return 0
  | [dir, "merge"] =>
    IO.FS.createDirAll dir
    for (name, p) in curatedMerge do writeCase dir name p
    IO.println s!"wrote {curatedMerge.length} merge cases"
    return 0
  | [dir, "seed", n] =>
    match n.toNat? with
    | none => IO.eprintln s!"difftest: bad seed {n}"; return 1
    | some k =>
      IO.FS.createDirAll dir
      writeCase dir s!"rand-{n}" (genProgram (k + 1))
      return 0
  | [dir, "mergeseed", n] =>
    match n.toNat? with
    | none => IO.eprintln s!"difftest: bad seed {n}"; return 1
    | some k =>
      IO.FS.createDirAll dir
      writeCase dir s!"mrand-{n}" (genMergeProgram (k + 1))
      return 0
  | _ =>
    IO.eprintln "usage: difftest <dir> curated | merge | seed <n> | mergeseed <n>"
    return 1
