import EgglogSemantics.Encoding.Encode
import EgglogSemantics.Encoding.Checker
import EgglogSemantics.Tests.Egg

/-!
# Differential test case generator

Writes one `.egg` file and one `.expected` file per case. `scripts/difftest.sh` runs
egglog on the former and diffs its `(print-size)` output against the latter.

Two kinds of case, over two fragments. The **curated** ones are hand-written, so they are
only as good as whoever picked them. The **random** ones are generated from a seed by a
fixed linear congruential stream, which is what removes that selection bias. Each kind
covers both the constructor fragment and M9's `:merge` functions.

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
  ruleset := ""

private def swapRule : Rule where
  query := [.expr (add (.var "a") (.var "b"))]
  actions := [.expr (add (.var "b") (.var "a"))]
  ruleset := ""

private def detectRule : Rule where
  query := [.eq (.app "Wrapper" [add (C "One") (C "Two")])
                (.app "Wrapper" [add (C "Two") (C "One")])]
  actions := [.expr (.app "Success" [])]
  ruleset := ""

private def assocRule : Rule where
  query := [.expr (add (add (.var "a") (.var "b")) (.var "c"))]
  actions := [.union (add (add (.var "a") (.var "b")) (.var "c"))
                     (add (.var "a") (add (.var "b") (.var "c")))]
  ruleset := ""

private def curated : List (String × Program) :=
  [ ("actions",
      [.action (.expr (add (C "One") (C "Two"))),
       .action (.union (C "One") (C "One")),
       .action (.letBind "$g" (add (C "Two") (C "Three"))),
       .action (.expr (.app "Wrapper" [.var "$g"]))]),
    ("swap-1", [.action (.expr (add (C "One") (C "Two"))), .rule swapRule, .run ""]),
    ("swap-2", [.action (.expr (add (C "One") (C "Two"))), .rule swapRule, .run "", .run ""]),
    ("wrapper-1",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run ""]),
    ("wrapper-2",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run "", .run ""]),
    ("wrapper-3",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run "", .run "", .run ""]),
    ("assoc-1",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))), .rule assocRule, .run ""]),
    ("assoc-2",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))),
       .rule assocRule, .run "", .run ""]),
    ("both-2",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))),
       .rule assocRule, .rule commuteRule, .run "", .run ""]),
    ("seed-2", [.rule ⟨[], [.expr (add (C "One") (C "Two"))], ""⟩, .run "", .run ""]) ]

/-! **The emitted egglog is unchanged by rulesets.** Every case here names the *unnamed*
ruleset, which a rule joins by writing no `:ruleset` and which `(run 1)` runs, so
`Cmd.toEgg` and `Rule.toEgg` render exactly what they rendered before `Rule.ruleset` and
`Cmd.run`'s argument existed, and `Program.rulesetDecls` adds no line. Pinned rather than
argued: the whole suite compares against egglog byte for byte. -/
set_option linter.hashCommand false in
#guard Program.toEgg (Program.declared
    [.action (.expr (add (C "One") (C "Two"))), .rule swapRule, .run "", .run ""])
  = "(datatype Math (One) (Two) (Add Math Math))\n\
     (Add (One) (Two))\n\
     (rule ((Add a b)) ((Add b a)))\n\
     (run 1)\n\
     (run 1)\n\
     (print-size)\n"

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
    (⟨[.expr p], [.expr a], ""⟩, s)
  | 1 =>
    -- one pattern, head unions two terms; `union` operands may be bare variables
    let (a₁, s) := genOver p.vars 2 s
    let (a₂, s) := genOver p.vars 2 s
    (⟨[.expr p], [.union a₁ a₂], ""⟩, s)
  | _ =>
    -- an equality body, so matching has to go through congruence
    let (q, s) := genPattern ["a", "b"] src s
    let (a, s) := genApp (p.vars ∪ q.vars) 2 s
    (⟨[.eq p q], [.expr a], ""⟩, s)

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
    ++ List.replicate (rounds + 1) (Cmd.run "")

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
122-for-122 green. `genMergeSpec` draws them now; the `old-*`/`new-*` cases below pin the
four shapes that caught the outright swap, and the `canon-*` cases the six that caught
*which* row the binding reads — `MERGE.md`, "`old` is the row at the canonical key".

No `:merge` **body** reads a table. An atom there would bind its variable to *any* recorded
output, where egglog binds the current one, so the model would fire more and build more;
`Impl/Check.lean`'s "Reading in an action" rejects it statically. A body may still *write*
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
    merge := some (.merge [] [.app "min" [.var "old", .var "new"]]) }

private def distMax (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [] [.app "max" [.var "old", .var "new"]]) }

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
    merge := some (.merge [.letBind "s" (.app op [.var "old", .var "new"])] [.var "s"]) }

/-- `:merge old` / `:merge new`, the two merges no commutative one can distinguish. `old`
is the value already in the table and `new` the one being inserted — which row that is, at
a collision a rebuild caused, is `Impl/Merge.lean`'s `swapForCanon`. -/
private def distPick (n : Nat) (which : String) : FnDecl :=
  { arity := n, outArity := 1, merge := some (.merge [] [.var which]) }

/-- `:no-merge`: a collision is an error rather than a resolution
(egglog panics with "Illegal merge attempted for function Dist"), so a case using it must
keep its keys distinct. Inert in the model, since `MergeStep` fires only on `.merge`. -/
private def distNoMerge (n : Nat) : FnDecl :=
  { arity := n, outArity := 1, merge := some .noMerge }

private def num (n : Int) : Expr := .lit (.int n)

private def mset (f : FnName) (args : List Expr) (v : Int) : Cmd :=
  .action (.set f args [num v])

/-- The binary constructor `commuteDist` matches on, as an expression: the key of a
`:merge` row is a term like any other, and these are the cases whose keys are compound. -/
private def gg (a b : Expr) : Expr := .app "G" [a, b]

/-- A rule that copies a `Dist` entry onto the commuted key, so a merge fires from a rule
head as well as from a top-level action. -/
private def commuteDist : Rule where
  query := [.expr (.app "G" [.var "a", .var "b"])]
  actions := [.set "Dist" [.var "b", .var "a"] [num 9]]
  ruleset := ""

/-! ### Multi-column outputs

`Database.Out`, `MergeStep` and `MergeSpec`'s result were multi-column from the start;
`Action.set` and `Pattern` were not, so a two-column entry could be created by a merge and
never written or read. Both are now widened, and these are the cases that exercise it —
egglog's `(function f (Math) (i64 i64) …)`, `(set (f k) (values a b))` and the tuple
destructure `(= (values a b) (f k))`.

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
    merge := some (.merge [] [.app "min" [.var "old0", .var "new0"],
                              .app "max" [.var "old1", .var "new1"]]) }

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
  ruleset := ""

/-! ### Reading a `:merge` function from a rule body

`MERGE.md` calls this the difftest fragment's boundary: every merge case so far *writes*
`Dist` and queries only constructors, so the read path — `Matches.values`, reachable
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
  ruleset := ""

/-- The value: fires only where the recorded output is `v`. -/
private def readValue (v : Int) : Rule where
  query := [.values [num v] "Dist" [.var "k"]]
  actions := [.expr (.app "Hit" [.var "k"])]
  ruleset := ""

/-- `distPick` at two value columns: `(values old0 old1)` or `(values new0 new1)`. The one
merge that is both **non-commutative** and **multi-column**, so it is the only shape in
which `mergeEnvIdx`'s per-column binding is observable on its own — every other multi-column
case here combines with `min`/`max`, which cannot tell the two rows apart. -/
private def distPickPair (n : Nat) (which : String) : FnDecl :=
  { arity := n, outArity := 2,
    merge := some (.merge [] [.var (which ++ "0"), .var (which ++ "1")]) }

/-- The two-column acceptance test's rule: guarded on the *pre-merge* value tuple. -/
private def readStale : Rule where
  query := [.values [num 5, num 1] "Dist" [.var "k"]]
  actions := [.expr (.app "Hit" [.var "k"])]
  ruleset := ""

/-- Copy one merge function's value into another's row. The read is a query fact binding
`v` and the head only writes, which is the only shape egglog accepts for a rule and the
only shape the model accepts anywhere. -/
private def copyDist : Rule where
  query := [.values [.var "v"] "Dist" [.var "k"]]
  actions := [.set "Copy" [.var "k"] [.var "v"]]
  ruleset := ""

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
/-- `(rule ((= v (f key…))) ((hit mark…)))`. Fires exactly when `f`'s row at `key` holds
`v`, so `hit`'s row count reports which value survived.

The marker's arguments are separate from the key because a key may be a *compound*
expression, and building it in the head would create the very term whose absence the case
is about — `read-unbuilt-key` reads at a key the program never built. -/
private def readIntoAt (hit f : FnName) (key : List Expr) (v : Int) (mark : List Expr) :
    Rule where
  query := [.values [num v] f key]
  actions := [.expr (.app hit mark)]
  ruleset := ""

/-- `readIntoAt` marking with the key itself, which is ground, so the query costs one
substitution and no enumeration. -/
private def readInto (hit f : FnName) (key : List Expr) (v : Int) : Rule :=
  readIntoAt hit f key v key

/-- `readInto` at a multi-column output. -/
private def readIntoW (hit f : FnName) (key : List Expr) (vs : List Int) : Rule where
  query := [.values (vs.map num) f key]
  actions := [.expr (.app hit key)]
  ruleset := ""

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
than *builds* (`Prim.apply` against `Expr.eval`'s constructor case), so the three ways to
get this wrong are to build the term `min(5, 3)`, to compute the wrong operation, or to
compute nothing.
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
that ran the body unconditionally would pass every other case in this family.

**A collision that leaves every value column unchanged runs no block at all**, on either
side: egglog's `MergeFn` treats it as no conflict and `Impl/Merge.lean`'s `noConflict` now
does the same. The five `merge-body-noop-*` cases below are that behaviour and its edges —
they were a recorded divergence until the model grew the skip, and they are the reason the
rest of this family keeps its two colliding values *distinct*: a case that means to observe
a body running has to give the body something to resolve. -/
/-- The side table a body writes into. `min` rather than `old`/`new` on purpose: a case
with several collisions logs several values, and the count of collisions is the one thing
the two engines are not obliged to agree on, so the *combination* has to be
order-insensitive for the value read to mean anything. -/
private def logDecl : FnDecl :=
  { arity := 1, outArity := 1,
    merge := some (.merge [] [.app "min" [.var "old", .var "new"]]) }

/-- A merge that logs one of the colliding values into `Log` and returns the other. -/
private def distLog (n : Nat) (logged kept : String) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [.set "Log" [C "L"] [.var logged]] [.var kept]) }

/-- A merge whose body is `(union (U) (V))` — the body's entire effect is an equality, as
in a union-find's. -/
private def distUnion (n : Nat) (kept : String) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [.union (C "U") (C "V")] [.var kept]) }

/-- A two-action body: `let` the combined value, log it, return it. Exercises the block
form at more than one action, and the `let`-bound variable as a `set`'s value. -/
private def distLetLog (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [.letBind "s" (.app "min" [.var "old", .var "new"]),
                           .set "Log" [C "L"] [.var "s"]] [.var "s"]) }

/-- Seeds `W` at both operands of a body's `union`, so that `W`'s row count falls from 2 to
1 exactly when the body runs. -/
private def seedW : List Cmd :=
  [.action (.expr (.app "W" [C "U"])), .action (.expr (.app "W" [C "V"]))]

/-- A **two-column** merge with a body, for the case where a collision leaves one value
column unchanged and moves the other. The skip is all-or-nothing over the whole value
tuple, so this body must still run; a model that skipped per column would report `L 0`. -/
private def distPairLog (n : Nat) : FnDecl :=
  { arity := n, outArity := 2,
    merge := some (.merge [.set "Log" [C "L"] [.var "old0"]] [.var "new0", .var "new1"]) }

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

Eq-sorted merge **outputs** are absent, and there is nothing here to widen: `FnDecl` carries
no sorts at all, and `Tests/Egg.lean`'s `FnDecl.toEgg` renders `i64` per output column, so
no program this file can build has one. Adding the sort would also want `ordering-min` to
render, and `Term.blt` is structural where egglog's is by insertion order — a known
divergence (`Tests/Egg.lean`, `FnDecl.toEgg`). Missing feature, not untested path. -/
/-- A three-column merge: a different combiner per column, so every `mergeEnvIdx` binding
is load-bearing. -/
private def distTriple (n : Nat) : FnDecl :=
  { arity := n, outArity := 3,
    merge := some (.merge [] [.app "min" [.var "old0", .var "new0"],
                              .app "max" [.var "old1", .var "new1"],
                              .var "old2"]) }

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
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run ""]),
    -- The same collapse, with `max`.
    ("max-rebuild",
      [.decl "Dist" (distMax 2),
       mset "Dist" [C "X", C "Y"] 1, mset "Dist" [C "A", C "B"] 2,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run ""]),
    -- A congruence-driven collapse: the keys become equal through `G`, not directly.
    ("min-congr",
      [.decl "Dist" (dist 1),
       .action (.expr (.app "G" [C "A", C "B"])),
       .action (.expr (.app "G" [C "X", C "Y"])),
       mset "Dist" [.app "G" [C "A", C "B"]] 4,
       mset "Dist" [.app "G" [C "X", C "Y"]] 6,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run ""]),
    -- A rule head writing a row, so the merge fires from a firing rather than an action.
    ("min-rule",
      [.decl "Dist" (dist 2),
       .action (.expr (.app "G" [C "A", C "B"])),
       .action (.expr (.app "G" [C "B", C "A"])),
       mset "Dist" [C "B", C "A"] 2,
       .rule commuteDist, .run ""]),
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
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run ""]),
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
       .rule readPair, .run ""]),
    -- The destructure through congruent keys: `A` and `X` become one class, so the row
    -- written at `X` is readable at `A`.
    ("tuple-read-congr",
      [.decl "Dist" (distPair 1), pset "Dist" [C "X"] 3 4,
       .action (.expr (C "A")), .action (.union (C "A") (C "X")),
       .rule readPair, .run ""]),
    -- A rule body *reading* a single-column `:merge` function: existence only.
    ("read-exists",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 3, mset "Dist" [C "B"] 5,
       .rule readExists, .run ""]),
    -- The same, reading the value, with the keys distinct so no merge fires.
    ("read-value",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 3, mset "Dist" [C "B"] 5,
       .rule (readValue 3), .run ""]),
    -- **The acceptance test, single column.** `5` is merged away by `min`, so egglog's
    -- table no longer holds it and the rule must not fire.
    ("read-stale",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       .rule (readValue 5), .run ""]),
    -- **The acceptance test, two columns.** The repro that was recorded in `MERGE.md` as
    -- a known divergence: egglog says `Hit 0`, and an append-only implementation says
    -- `Hit 1` because the superseded row is still readable.
    ("tuple-stale",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 5 1, pset "Dist" [C "A"] 3 7,
       .rule readStale, .run ""]),
    -- A single-column read through *congruent* keys: the row is written at `X`, read at
    -- `A`. `tuple-read-congr` covers the two-column case; this is the one-column one, and
    -- both reach `patternHolds`'s row scan through its key-congruence test.
    ("read-congr",
      [.decl "Dist" (dist 1), mset "Dist" [C "X"] 3,
       .action (.expr (C "A")), .action (.union (C "A") (C "X")),
       .rule readExists, .run ""]),
    -- The same, reading the value rather than only its existence.
    ("read-value-congr",
      [.decl "Dist" (dist 1), mset "Dist" [C "X"] 3,
       .action (.expr (C "A")), .action (.union (C "A") (C "X")),
       .rule (readValue 3), .run ""]),
    -- Reading a `:no-merge` function. A row atom reads any declared function, so
    -- `:no-merge` is readable too, and `nomerge-two` only ever writes one.
    ("read-nomerge",
      [.decl "Dist" (distNoMerge 1), mset "Dist" [C "A"] 3, mset "Dist" [C "B"] 5,
       .rule (readValue 3), .run ""]),
    -- Copying one merge function's value into another's row, which is what `read-copy`
    -- used to do from a top-level action. All reading happens in the query, so the read is
    -- `(= v (Dist k))` and the head only writes — the shape egglog requires of a rule and
    -- the model now requires everywhere (`Impl/Check.lean`, "Reading in an action").
    ("read-copy",
      [.decl "Dist" (dist 1), .decl "Copy" (dist 1), mset "Dist" [C "A"] 3,
       .rule copyDist, .run "",
       .action (.expr (.app "F" [C "A"]))]),
    -- **The `old`/`new` cases.** `(print-size)` cannot see a value, so each reads back the
    -- value egglog keeps: `Hit` is 1 exactly when the surviving output is that one. These
    -- are the four shapes that caught the model binding `old` and `new` backwards, each
    -- checked against the binary; a commutative merge cannot express any of them.
    -- Three writes at one key: egglog keeps the first, `5`.
    ("old-three",
      [.decl "Dist" (distPick 1 "old"), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       mset "Dist" [C "A"] 7, .rule (readValue 5), .run ""]),
    -- The same, keeping the last, `7`.
    ("new-three",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       mset "Dist" [C "A"] 7, .rule (readValue 7), .run ""]),
    -- Rebuild-driven: the collision arrives with the `union`, not with the `set`.
    ("old-rebuild",
      [.decl "Dist" (distPick 1 "old"), mset "Dist" [C "A"] 1, mset "Dist" [C "B"] 2,
       .action (.union (C "A") (C "B")), .rule (readValue 1), .run ""]),
    ("new-rebuild",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "A"] 1, mset "Dist" [C "B"] 2,
       .action (.union (C "A") (C "B")), .rule (readValue 2), .run ""]),
    -- Rule-head-driven, over two rounds: the head writes `9`, and the second round's read
    -- sees it only under `:merge new`. `Hit` is 0 in the `old` case, in both engines.
    ("old-rule",
      [.decl "Dist" (distPick 1 "old"), mset "Dist" [C "A"] 4,
       .rule ⟨[.expr (C "A")], [.set "Dist" [C "A"] [num 9]], ""⟩,
       .rule (readValue 9), .run "", .run ""]),
    ("new-rule",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "A"] 4,
       .rule ⟨[.expr (C "A")], [.set "Dist" [C "A"] [num 9]], ""⟩,
       .rule (readValue 9), .run "", .run ""]),
    -- Three rows in one key class, reached by two unions. This is the shape that says the
    -- survivor of a collision keeps the *older* row's place: merge the first two and the
    -- result must still count as older than the third.
    ("old-threeway",
      [.decl "Dist" (distPick 1 "old"), mset "Dist" [C "X"] 1, mset "Dist" [C "Y"] 2,
       mset "Dist" [C "Z"] 3, .action (.union (C "X") (C "Y")),
       .action (.union (C "Y") (C "Z")), .rule (readValue 1), .run ""]),
    ("new-threeway",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "X"] 1, mset "Dist" [C "Y"] 2,
       mset "Dist" [C "Z"] 3, .action (.union (C "X") (C "Y")),
       .action (.union (C "Y") (C "Z")), .rule (readValue 3), .run ""]),
    -- **`old` is the row at the canonical key, not the row written first.** Every case
    -- above writes the younger row at the younger key, where the two readings agree.
    -- These separate them: a bare `(A)` creates `A` before `K`, so `A` is the *older*
    -- key while `Dist (A)` is the *younger* row, and egglog keeps the earlier write.
    -- `Hit`/`Miss` bracket the surviving value, so a wrong binding moves both counts.
    ("canon-old",
      [.decl "Dist" (distPick 1 "old"), .action (.expr (C "A")),
       mset "Dist" [C "K"] 3, mset "Dist" [C "A"] 2,
       .action (.union (C "A") (C "K")),
       .rule (readInto "Hit" "Dist" [C "A"] 2), .rule (readInto "Miss" "Dist" [C "A"] 3),
       .run ""]),
    ("canon-new",
      [.decl "Dist" (distPick 1 "new"), .action (.expr (C "A")),
       mset "Dist" [C "K"] 3, mset "Dist" [C "A"] 2,
       .action (.union (C "A") (C "K")),
       .rule (readInto "Hit" "Dist" [C "A"] 3), .rule (readInto "Miss" "Dist" [C "A"] 2),
       .run ""]),
    -- The same, with the two keys created as the **arguments of one term** rather than by
    -- separate commands. egglog builds an application's arguments left to right, so `(P
    -- (K) (A))` makes `K` canonical and `(P (A) (K))` makes `A` canonical, and the pair
    -- of cases differs in nothing else. This is what `Term.subtermList`'s order is for.
    ("canon-arg-left",
      [.decl "Dist" (distPick 1 "new"), .action (.expr (.app "P" [C "K", C "A"])),
       mset "Dist" [C "K"] 3, mset "Dist" [C "A"] 2,
       .action (.union (C "A") (C "K")),
       .rule (readInto "Hit" "Dist" [C "A"] 2), .rule (readInto "Miss" "Dist" [C "A"] 3),
       .run ""]),
    ("canon-arg-right",
      [.decl "Dist" (distPick 1 "new"), .action (.expr (.app "P" [C "A", C "K"])),
       mset "Dist" [C "K"] 3, mset "Dist" [C "A"] 2,
       .action (.union (C "A") (C "K")),
       .rule (readInto "Hit" "Dist" [C "A"] 3), .rule (readInto "Miss" "Dist" [C "A"] 2),
       .run ""]),
    -- **Neither key canonical**, so canonicity decides nothing and age is the tie-break:
    -- `Z` is created first and carries no row, both `Dist` rows move to it, and egglog
    -- stages them in table order — the earlier write is the one the other is merged onto.
    -- This is the shape the two readings agree on, pinned so the agreement cannot rot.
    ("canon-none-old",
      [.decl "Dist" (distPick 1 "old"), .action (.expr (C "Z")),
       mset "Dist" [C "K"] 3, mset "Dist" [C "A"] 2,
       .action (.union (C "K") (C "Z")), .action (.union (C "A") (C "Z")),
       .rule (readInto "Hit" "Dist" [C "Z"] 3), .rule (readInto "Miss" "Dist" [C "Z"] 2),
       .run ""]),
    ("canon-none-new",
      [.decl "Dist" (distPick 1 "new"), .action (.expr (C "Z")),
       mset "Dist" [C "K"] 3, mset "Dist" [C "A"] 2,
       .action (.union (C "K") (C "Z")), .action (.union (C "A") (C "Z")),
       .rule (readInto "Hit" "Dist" [C "Z"] 2), .rule (readInto "Miss" "Dist" [C "Z"] 3),
       .run ""]),
    -- **`old` is the row that reached the canonical key first**, which is a fact about the
    -- *order of the unions* and not about either row's age. `A` is created first and holds
    -- no row, so neither `Dist (B)` nor `Dist (C)` is ever at a canonical key and
    -- `canonTerm` decides nothing; both `set`s happen before either `union`, so insertion
    -- age is the same in both members of each pair. What separates them is that the first
    -- `union` re-keys its row onto `A`, where the second `union` then finds it resident —
    -- `Impl/Merge.lean`'s `rebuild`. Swapping the two `union`s swaps the answer, and the
    -- `old` pair is the exact mirror of the `new` pair, which is what says the rebuild
    -- changed the *binding* rather than the value. Found by `mrand-28`.
    ("rekey-new",
      [.decl "Dist" (distPick 1 "new"), .action (.expr (C "A")),
       mset "Dist" [C "B"] 1, mset "Dist" [C "C"] 2,
       .action (.union (C "C") (C "A")), .action (.union (C "B") (C "A")),
       .rule (readInto "Hit" "Dist" [C "A"] 1), .rule (readInto "Miss" "Dist" [C "A"] 2),
       .run ""]),
    ("rekey-new-swap",
      [.decl "Dist" (distPick 1 "new"), .action (.expr (C "A")),
       mset "Dist" [C "B"] 1, mset "Dist" [C "C"] 2,
       .action (.union (C "B") (C "A")), .action (.union (C "C") (C "A")),
       .rule (readInto "Hit" "Dist" [C "A"] 2), .rule (readInto "Miss" "Dist" [C "A"] 1),
       .run ""]),
    ("rekey-old",
      [.decl "Dist" (distPick 1 "old"), .action (.expr (C "A")),
       mset "Dist" [C "B"] 1, mset "Dist" [C "C"] 2,
       .action (.union (C "C") (C "A")), .action (.union (C "B") (C "A")),
       .rule (readInto "Hit" "Dist" [C "A"] 2), .rule (readInto "Miss" "Dist" [C "A"] 1),
       .run ""]),
    ("rekey-old-swap",
      [.decl "Dist" (distPick 1 "old"), .action (.expr (C "A")),
       mset "Dist" [C "B"] 1, mset "Dist" [C "C"] 2,
       .action (.union (C "B") (C "A")), .action (.union (C "C") (C "A")),
       .rule (readInto "Hit" "Dist" [C "A"] 1), .rule (readInto "Miss" "Dist" [C "A"] 2),
       .run ""]),
    -- **Primitives outside a `:merge` body.** `min` in a top-level `set`'s value column.
    -- `Hit 1, Miss 0` says the model computed `3`; building the term `min(5, 3)` or getting
    -- stuck gives `0, 0` and computing `max` gives `0, 1`.
    ("prim-set-min",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [C "K"] [.app "min" [num 5, num 3]]),
       .rule (readInto "Hit" "Dist" [C "K"] 3), .rule (readInto "Miss" "Dist" [C "K"] 5),
       .run ""]),
    -- The same with `max`, so the two markers swap: a model computing `min` for `max`
    -- is caught here even though it passes `prim-set-min`.
    ("prim-set-max",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [C "K"] [.app "max" [num 5, num 3]]),
       .rule (readInto "Hit" "Dist" [C "K"] 5), .rule (readInto "Miss" "Dist" [C "K"] 3),
       .run ""]),
    -- Nested: `(min (max 5 3) 4)` is `4`, so the operand list itself has to be evaluated
    -- through the argument list before the outer primitive applies. `Miss` reads `5`, the value
    -- an unevaluated inner application would have left.
    ("prim-nested",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [C "K"] [.app "min" [.app "max" [num 5, num 3], num 4]]),
       .rule (readInto "Hit" "Dist" [C "K"] 4), .rule (readInto "Miss" "Dist" [C "K"] 5),
       .run ""]),
    -- A primitive under a top-level `let`, so the value reaches the row through the global
    -- environment rather than directly. The `$` prefix is egglog's convention for a global
    -- and avoids its "Global `g` should start with `$`" warning.
    ("prim-let",
      [.decl "Dist" (dist 1),
       .action (.letBind "$g" (.app "min" [num 7, num 2])),
       .action (.set "Dist" [C "K"] [.var "$g"]),
       .rule (readInto "Hit" "Dist" [C "K"] 2), .rule (readInto "Miss" "Dist" [C "K"] 7),
       .run ""]),
    -- A primitive in a **rule head**, which is the position `Rule.noLookup` polices and so
    -- the one most likely to be rejected by mistake. Two rounds: the first fires the write,
    -- the second reads it back.
    ("prim-rule-head",
      [.decl "Dist" (dist 1), seedF,
       .rule ⟨[.expr (.app "F" [.var "a"])],
              [.set "Dist" [.var "a"] [.app "max" [num 5, num 3]]], ""⟩,
       .rule (readInto "Hit" "Dist" [C "A"] 5), .rule (readInto "Miss" "Dist" [C "A"] 3),
       .run "", .run ""]),
    -- **A `:merge` body that writes.** The body logs `old` into a side table and returns
    -- `new`. `L 1` and `Log 1` say the body ran at all — both names occur nowhere else —
    -- and `Hit 1, Miss 0` say it logged `5`, the value already in the table.
    ("merge-body-set-old",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "old" "new"),
       mset "Dist" [C "K"] 5, mset "Dist" [C "K"] 3,
       .rule (readInto "Hit" "Log" [C "L"] 5), .rule (readInto "Miss" "Log" [C "L"] 3),
       .rule (readInto "Won" "Dist" [C "K"] 3), .run ""]),
    -- The mirror: log `new`, keep `old`. Both markers move, which is what makes the pair
    -- distinguish the two bindings rather than merely detecting that something was logged.
    ("merge-body-set-new",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "new" "old"),
       mset "Dist" [C "K"] 5, mset "Dist" [C "K"] 3,
       .rule (readInto "Hit" "Log" [C "L"] 3), .rule (readInto "Miss" "Log" [C "L"] 5),
       .rule (readInto "Won" "Dist" [C "K"] 5), .run ""]),
    -- A two-action body: `let`, then `set` the bound variable, then return it. Exercises
    -- the block renderer past one action and a `let`-bound value flowing into a `set`.
    ("merge-body-let-set",
      [.decl "Log" logDecl, .decl "Dist" (distLetLog 1),
       mset "Dist" [C "K"] 5, mset "Dist" [C "K"] 3,
       .rule (readInto "Hit" "Log" [C "L"] 3), .rule (readInto "Miss" "Log" [C "L"] 5),
       .rule (readInto "Won" "Dist" [C "K"] 3), .run ""]),
    -- The body's effect is an **equality**: `W` is seeded at `(U)` and at `(V)`, so `W 1`
    -- says the union ran and `W 2` says it did not. This is the union-find `:merge`.
    ("merge-body-union",
      [.decl "Dist" (distUnion 1 "new")] ++ seedW ++
      [mset "Dist" [C "K"] 5, mset "Dist" [C "K"] 3,
       .rule (readInto "Won" "Dist" [C "K"] 3), .run ""]),
    -- The same, with the collision arriving from a `union` on the *keys* during rebuild
    -- rather than from a repeated `set`, so the body runs from the merge phase.
    ("merge-body-union-rebuild",
      [.decl "Dist" (distUnion 1 "old")] ++ seedW ++
      [mset "Dist" [C "X"] 1, mset "Dist" [C "Y"] 2, .action (.union (C "X") (C "Y")),
       .rule (readInto "Won" "Dist" [C "X"] 1), .run ""]),
    -- A writing body driven by a rebuild collision: `Log` records `old`, which
    -- `old-rebuild` pins to the earlier write.
    ("merge-body-set-rebuild",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "old" "new"),
       mset "Dist" [C "X"] 1, mset "Dist" [C "Y"] 2, .action (.union (C "X") (C "Y")),
       .rule (readInto "Hit" "Log" [C "L"] 1), .rule (readInto "Miss" "Log" [C "L"] 2),
       .run ""]),
    -- **The negative control.** The same writing body, but the keys never collide, so `L`,
    -- `Log` and `W` must all report the body having *not* run. Without this a model that
    -- ran a body unconditionally would pass every other case in the family.
    ("merge-body-inert",
      [.decl "Log" logDecl, .decl "Dist" (distLog 2 "old" "new")] ++ seedW ++
      [mset "Dist" [C "A", C "B"] 1, mset "Dist" [C "B", C "A"] 2,
       .rule (readInto "Hit" "Log" [C "L"] 1), .run ""]),
    -- **The no-conflict skip.** The `merge-body-set-rebuild` program with the two values
    -- made *equal*: the keys still collide through the `union`, but the collision leaves
    -- the value column unchanged, so egglog treats it as no conflict and runs no block.
    -- `Won 1` says the collision was still resolved — one row, holding `2` — and `Miss 0`,
    -- `L 0`, `Log 0` say the body did not run. This was a recorded divergence: comparing
    -- whole *rows* rather than value columns, the model answered `L 1, Log 1`.
    ("merge-body-noop-rebuild",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "old" "new"),
       mset "Dist" [C "X"] 2, mset "Dist" [C "Y"] 2, .action (.union (C "X") (C "Y")),
       .rule (readInto "Won" "Dist" [C "X"] 2), .rule (readInto "Miss" "Log" [C "L"] 2),
       .run ""]),
    -- The same collision with a `union` body, where the skip is visible as an *equality*
    -- that was never asserted: `W` stays 2 because `(union (U) (V))` never ran. `Won 1`
    -- against `Miss 0` reports that the merge itself still happened.
    ("merge-body-noop-union",
      [.decl "Dist" (distUnion 1 "new")] ++ seedW ++
      [mset "Dist" [C "X"] 2, mset "Dist" [C "Y"] 2, .action (.union (C "X") (C "Y")),
       .rule (readInto "Won" "Dist" [C "X"] 2), .rule (readInto "Miss" "Dist" [C "X"] 3),
       .run ""]),
    -- **The skip is all-or-nothing over the value tuple.** Two value columns, the first
    -- equal at both rows and the second not, so the collision *is* a conflict and the body
    -- runs: `Hit 1` reads the logged `old0`. A model that skipped per column would leave
    -- `L 0, Log 0, Hit 0`. `Miss` reads the column the log does not hold.
    ("merge-body-noop-partial",
      [.decl "Log" logDecl, .decl "Dist" (distPairLog 1),
       pset "Dist" [C "X"] 2 1, pset "Dist" [C "Y"] 2 5,
       .action (.union (C "X") (C "Y")),
       .rule (readInto "Hit" "Log" [C "L"] 2), .rule (readInto "Miss" "Log" [C "L"] 5),
       .run ""]),
    -- **Three rows in one key class, two of them equal.** The equal pair is skipped and the
    -- odd one out is a real conflict, so the body runs — `L 1, Log 1` — and the class still
    -- collapses to one row holding `3`, which `Hit 1` against `Miss 0` reads back. This is
    -- the case that separates "drop the arriving row on a skip" from "do nothing at all".
    ("merge-body-noop-three",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "old" "new"),
       mset "Dist" [C "X"] 2, mset "Dist" [C "Y"] 2, mset "Dist" [C "Z"] 3,
       .action (.union (C "X") (C "Y")), .action (.union (C "Y") (C "Z")),
       .rule (readInto "Hit" "Dist" [C "X"] 3), .rule (readInto "Miss" "Dist" [C "X"] 2),
       .run ""]),
    -- **`old`/`new` per column, at a canonicity-decided collision.** `canon-old` and
    -- `canon-new` at two value columns: the merge is `(values old0 old1)` resp. `(values
    -- new0 new1)`, so every column's binding is `mergeEnvIdx`'s rather than `mergeEnv`'s
    -- and none of it is hidden behind a commutative combiner. `Hit`/`Miss` read the whole
    -- surviving tuple, so binding `old` and `new` backwards at *any* column moves both
    -- counts. This is the shape the random stream draws once its value width exceeds one.
    ("tuple-canon-old",
      [.decl "Dist" (distPickPair 1 "old"), .action (.expr (C "A")),
       pset "Dist" [C "K"] 3 4, pset "Dist" [C "A"] 2 6,
       .action (.union (C "A") (C "K")),
       .rule (readIntoW "Hit" "Dist" [C "A"] [2, 6]),
       .rule (readIntoW "Miss" "Dist" [C "A"] [3, 4]), .run ""]),
    ("tuple-canon-new",
      [.decl "Dist" (distPickPair 1 "new"), .action (.expr (C "A")),
       pset "Dist" [C "K"] 3 4, pset "Dist" [C "A"] 2 6,
       .action (.union (C "A") (C "K")),
       .rule (readIntoW "Hit" "Dist" [C "A"] [3, 4]),
       .rule (readIntoW "Miss" "Dist" [C "A"] [2, 6]), .run ""]),
    -- **Equal values at one key**, the other half of the no-conflict skip: the two writes
    -- are identical, so egglog's insert finds nothing to resolve and the body never runs —
    -- `L 0, Log 0` — while `Won 1` says the class still holds the value. The model reaches
    -- the same answer by a different route, `rows` being a `Set` in which the two writes
    -- are one row, so this is a control on the *agreement* rather than on the skip:
    -- `merge-body-noop-rebuild` is the same values at congruent-but-unequal keys, where the
    -- model does have two rows and does need `noConflict`.
    ("merge-body-noop-samekey",
      [.decl "Log" logDecl, .decl "Dist" (distLog 1 "old" "new"),
       mset "Dist" [C "K"] 2, mset "Dist" [C "K"] 2,
       .rule (readInto "Won" "Dist" [C "K"] 2), .run ""]),
    -- **Arity 0.** One key class, and it is the empty tuple — `congrKeys` at length zero.
    ("merge-arity0",
      [.decl "Zero" (dist 0), mset "Zero" [] 5, mset "Zero" [] 3,
       .rule (readInto "Hit" "Zero" [] 3), .rule (readInto "Miss" "Zero" [] 5), .run ""]),
    -- Arity 0 with a writing body, so the empty key tuple and the side table meet.
    ("merge-arity0-body",
      [.decl "Log" logDecl, .decl "Zero" (distLog 0 "old" "new"),
       mset "Zero" [] 5, mset "Zero" [] 3,
       .rule (readInto "Hit" "Log" [C "L"] 5), .rule (readInto "Miss" "Log" [C "L"] 3),
       .run ""]),
    -- **Arity 3**, collided on the third column through a `union`, so the key comparison
    -- has to walk two equal columns before reaching a congruent one.
    ("merge-arity3",
      [.decl "Dist" (dist 3),
       mset "Dist" [C "A", C "B", C "X"] 5, mset "Dist" [C "A", C "B", C "Y"] 3,
       .action (.union (C "X") (C "Y")),
       .rule (readInto "Hit" "Dist" [C "A", C "B", C "X"] 3),
       .rule (readInto "Miss" "Dist" [C "A", C "B", C "X"] 5), .run ""]),
    -- **Value width 3**, one combiner per column: `min` on 0, `max` on 1, `old` on 2. A
    -- body reading the wrong `mergeEnvIdx` index computes a different tuple, and the
    -- guarded read then stops firing.
    ("tuple-three",
      [.decl "Dist" (distTriple 1), tset "Dist" [C "A"] [5, 1, 7],
       tset "Dist" [C "A"] [3, 9, 2],
       .rule (readIntoW "Hit" "Dist" [C "A"] [3, 9, 7]),
       .rule (readIntoW "Miss" "Dist" [C "A"] [5, 1, 7]), .run ""]),
    -- **A read atom's operands are interned before the congruence test.** The row is
    -- written at `(G (B) (A))` and read at `(G (A) (B))`, a term the program *never
    -- builds*: egglog flattens the fact to `G(a, b, x), Dist(x, o)`, so after `(union (A)
    -- (B))` the intermediate class is found by matching. `Hit 1` says the model found it
    -- too. `Miss` reads at `(G (C) (A))`, which is equally unbuilt and congruent to
    -- nothing, so `Miss 0` is what fails if the fix over-matches by treating any
    -- hypothesized operand as present. This was a recorded divergence: `patternHolds`
    -- closed over `d.closureF` where its `.expr`/`.eq` cases close over `(d.addTerm t)`,
    -- and answered `Hit 0`.
    ("read-unbuilt-key",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [gg (C "B") (C "A")] [num 4]),
       .action (.union (C "A") (C "B")),
       .rule (readIntoAt "Hit" "Dist" [gg (C "A") (C "B")] 4 [C "A"]),
       .rule (readIntoAt "Miss" "Dist" [gg (C "C") (C "A")] 4 [C "A"]), .run ""]),
    -- The same one level deeper, so the congruence has to be rebuilt at an *inner* node
    -- before the outer one can match. `Miss` moves the outer argument instead of the inner
    -- one — `(A)` for `(C)`, which no `union` relates — so it must not fire.
    ("read-unbuilt-key-deep",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [gg (gg (C "B") (C "A")) (C "C")] [num 4]),
       .action (.union (C "A") (C "B")),
       .rule (readIntoAt "Hit" "Dist" [gg (gg (C "A") (C "B")) (C "C")] 4 [C "A"]),
       .rule (readIntoAt "Miss" "Dist" [gg (gg (C "A") (C "B")) (C "A")] 4 [C "A"]),
       .run ""]),
    -- **The over-matching control.** `Miss` reads at `(G (H (A)) (B))`, whose inner node
    -- `(H (A))` has no row at all — `H` is never applied anywhere else — so egglog's
    -- `H(a, h)` atom matches nothing and neither may the model. Interning the operands adds
    -- a *hypothetical* row for every subterm, and this is the case that says a hypothetical
    -- row cannot stand in for one the database has to hold.
    ("read-unbuilt-key-nonode",
      [.decl "Dist" (dist 1),
       .action (.set "Dist" [gg (C "B") (C "A")] [num 4]),
       .action (.union (C "A") (C "B")),
       .rule (readIntoAt "Hit" "Dist" [gg (C "A") (C "B")] 4 [C "A"]),
       .rule (readIntoAt "Miss" "Dist" [gg (.app "H" [C "A"]) (C "B")] 4 [C "A"]),
       .run ""]) ]

/-! ### Random `:merge` cases

The curated merge cases are only as good as whoever picked them — the caveat the
constructor cases carried until they were randomized, and the same fix. These draw a
merge function's arity and its merge spec from the same seeded stream, write rows at
generated keys, and union constructors underneath those keys, which is what makes keys
collide and so what the counts actually discriminate on.

The fragment stays the one `MERGE.md` describes, and both narrowings are justified by the
model rather than by convenience:

* **Every drawn merge is idempotent** (`min`, `max`, `old`, `new`, one combiner per value
  column). A non-idempotent one diverges under our over-approximating reads *by design* — a
  row collides with itself, so `:merge (+ old new)` derives `2v`, `3v`, … — so a difference
  would be the design showing, not a bug. Being non-*commutative* is no such excuse, and
  `old`/`new` are drawn: a commutative merge cannot tell which colliding row the model
  calls `old`.
* **Merge functions are written and never read** by a *body*, since a body atom reading one
  binds any recorded output where egglog binds the current one. Reading one from a rule
  body is ordinary egglog and `genMergeReadRule` does it.

`MERGE.md`'s third narrowing, "bodies are `let`-only", is **gone**, from the model and now
from the draw as well. A body that `set`s a side table does not fire on self-collisions
(`mergeRound` skips `r₁ == r₂`) and does not fire in both orders (once `(r₁, r₂)` has
fired, `r₁` is gone and `mergeOneWith`'s `rows.contains` test drops `(r₂, r₁)`).
`genMergeSpec` draws `set`, `union` and `let`/`set` bodies, and `genMergeProgram` declares
the side table and seeds the equality's operands, so that a body which runs is visible in a
row count; `genMergeSpec` carries the observability argument for each shape.

**Eq-sorted merge *output* columns stay out, and not by choice.** `FnDecl` carries no sorts
at all and `Tests/Egg.lean`'s `FnDecl.toEgg` renders `i64` per output column, so there is
nothing to draw — it is a missing feature of the fragment rather than a narrowing of it.
Keys are eq-sorted, as the curated cases already are.

**Divergences this family found.** Each turned up on widening the draw and was minimized by
hand against the release binary. Items 1 to 4 are fixed, drawn again, and pinned by a
curated case above, so a regression now fails the suite rather than waiting for the next
widening. **Item 5 is open**, and `mrand-28` is red on it.

1. **A read atom's operands were not interned before the congruence test** — *fixed*, and
   pinned by the three `read-unbuilt-key*` cases above. `patternHolds` computed
   `cl := d.closureF` in its `.values` case where its `.expr` and `.eq` cases close over
   the extended database, so a key expression the program never built was in no congruence
   class and matched nothing:
   ```
   (set (Dist (G (B) (A))) 4) (union (A) (B))
   (rule ((= o (Dist (G (A) (B))))) ((Hit (A))))
   ```
   egglog flattens the fact to `G(a, b, x), Dist(x, o)` and matches through congruence,
   answering `Hit 1`; the model answered `Hit 0`. Reachable from `genMergeReadRule`'s
   free-key draw, which is how it turned up. Both `Spec/` and `Impl/` were wrong here, and
   in the same place: `Matches.values` compared the evaluated operands with `CongList
   db`, and `Cong db` relates only terms `db` holds, so the specification could not admit
   the match either.
2. **`old`/`new` at a rebuild collision followed insertion age here and key canonicity
   there** — *fixed*, and pinned by the six `canon-*` cases above. `mergeOneWith` took the
   row that was inserted earlier as `old`; egglog takes the row whose key is *already
   canonical* as `old` and the row re-inserted because its key moved as `new`, falling back
   on age only when no key moved or when no row holds the canonical key. The two agree
   whenever the younger row sits at the younger key, which every curated case did, and
   disagree otherwise:
   ```
   (function Dist (Math) i64 :merge new)
   (A) (set (Dist (K)) 3) (set (Dist (A)) 2) (union (A) (K))
   ```
   egglog keeps `3` — the earlier write, at the older key — and the model kept `2`.
   Reachable from `genKeys`: nothing stops a drawn key from being built before the row
   written at it. `Impl/Merge.lean`'s `canonTerm` is the fix and `MERGE.md`'s "`old` is the
   row at the canonical key" is the evidence, including what it still does not model.
3. **egglog resolved a body's nested call with the enclosing column's `old`** — *fixed in
   the Rust* (issue #59), and pinned by `merge-body-noop-partial` above.
   `ResolvedMergeFn::run` carried a shortcut returning `cur` whenever the column's own old
   and new values agreed (egraphs-good/egglog#287), and `run` runs at *every* node of a
   merge expression — including the `(L)` inside a body's `(set (Log (L)) old0)`, whose
   sort has nothing to do with the column's. At a collision agreeing on column 0 the
   shortcut handed that column's `i64` back as `(L)`'s e-class id, and the `Log` row was
   keyed on a class no term had:
   ```
   (function Log (Math) i64 :merge new)
   (function Dist (Math) (i64 i64) :merge ((set (Log (L)) old0) (values new0 new1)))
   (set (Dist (X)) (values 2 1)) (set (Dist (Y)) (values 2 5)) (union (X) (Y)) (run 1)
   ```
   `run_result` is the fix: the shortcut now applies once per value column's *result*
   expression and never to a nested call. Upstream has the same defect and returns a wrong
   `i64` from it (egraphs-good/egglog#987); only a `:merge` action block lets a nested call
   carry an eq-sort, which is what made it a dangling class here. Reachable the moment a
   writing body is drawn, which is the first of the two reasons `genMergeSpec` did not draw
   one.
4. **A value-preserving collision at congruent keys** — *fixed*, and pinned by the four
   `merge-body-noop-*` cases above. egglog skips a `:merge` **action block** outright when
   the collision leaves every value column unchanged (`egglog-bridge/src/lib.rs`, `MergeFn`'s
   `unchanged_width`), comparing the two rows' *values* and saying nothing about their keys,
   where `mergeRound` skipped an identical *row*. Two rows at congruent but unequal keys
   holding the same value were therefore a no-op collision there and a firing pair here:
   ```
   (function Log (Math) i64 :merge new)
   (function Dist (Math) i64 :merge ((set (Log (L)) old) new))
   (set (Dist (X)) 2) (set (Dist (Y)) 2) (union (X) (Y)) (run 1)
   ```
   egglog answered `L 0, Log 0` and the model `L 1, Log 1`; a `union` body answered `W 2`
   there and `W 1` here. `Impl/Merge.lean`'s `noConflict` is the fix — `mergeOneOriented`
   declines when the body is non-empty and `r₁.out == r₂.out`. Reachable from `genKeys` and
   `genMergeRule` the moment a writing body is drawn, which was the second reason; both
   reasons are gone and `genMergeSpec` draws writing bodies now.
5. **Which colliding row is resident, when a class is built up by *successive* unions** —
   **open**, and the reason `mrand-28` is red. `mergeOneWith` falls back on insertion age
   whenever neither colliding key is canonical, on the reading that egglog re-inserts both
   rows and stages them in table order. egglog does that only when both keys move in *one*
   rebuild. A key unioned into the class by an **earlier** command has already been
   rewritten to the canonical key, so its row is the resident one — `cur`, hence `old` —
   however recently it was written:
   ```
   (function Dist (Math) i64 :merge new)
   (A) (set (Dist (B)) 1) (set (Dist (C)) 2) (union (C) (A)) (union (B) (A))
   ```
   `A` is canonical, `C`'s row is rewritten onto it by the first union, and `B`'s row is
   merged onto that by the second, so egglog keeps `1` — the *older* row's value, under
   `:merge new` — where the model keeps `2`. Swapping the two `union` commands makes the two
   agree, and `:merge old` mirrors it exactly, so the trigger is "the younger row's key is
   canonicalized first" and nothing else. `canon-none-old` and `canon-none-new` are the
   shape where the two readings agree, and they agree only because the older row's key
   happens to be unioned first.

   `MERGE.md` records the residual — "when neither colliding key is canonical, egglog's
   survivor sits at the canonical key and this model's sits at the older row's key" — but
   calls it invisible "until a row appears at that third key later". It is not: a
   non-commutative merge and two `union` commands suffice, with no third row anywhere. The
   model cannot currently state the fix either, since it never re-keys a row and so has
   nowhere to record that one of the pair *reached* the canonical key first. Reachable from
   `genMergeProgram`'s column-wise key unions, which is how it turned up. -/

/-- The value-column variables a `:merge` body sees at column `i` of a width-`w` output.
`mergeEnv` binds egglog's unindexed `old`/`new` at one value column and `old0`/`new0`/…
above, so the naming is a function of the width rather than a choice. -/
private def oldAt (w i : Nat) : Expr := .var (if w == 1 then "old" else "old" ++ toString i)

/-- `oldAt`'s counterpart, the arriving row's column `i`. -/
private def newAt (w i : Nat) : Expr := .var (if w == 1 then "new" else "new" ++ toString i)

/-- One value column's combiner, over that column's own `old`/`new` pair. -/
private def genCombiner (w i : Nat) (s : Nat) : Expr × Nat :=
  let (j, s) := pick 4 s
  match j with
  | 0 => (oldAt w i, s)
  | 1 => (newAt w i, s)
  | k => (.app (if k == 2 then "min" else "max") [oldAt w i, newAt w i], s)

/-- A combiner per value column of a width-`w` output — columns `w - k` through `w - 1`,
so a call at `k = w` fills the whole tuple from column 0. -/
private def genCombiners (w : Nat) : Nat → Nat → List Expr × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (e, s) := genCombiner w (w - (k + 1)) s
    let (es, s) := genCombiners w k s
    (e :: es, s)

/-- A merge specification for a width-`w` output: one combiner per value column, under a
body that is empty half the time and **writes** in three draws of eight.

**The combiners** are `old`, `new`, `min` and `max`, drawn per column. `old` and `new` are
the two **non-commutative** merges, and they are here because a commutative one cannot see
which of the colliding rows the model calls `old`. The model had them backwards — `:merge
old` returned what `:merge new` should — and 122 green cases said nothing, because every
merge they drew was `min` or `max`. They are still joins in the sense that matters here
(`merge v v = v`, so a pass settles), and they are exactly as deterministic in egglog as
`min` is: `old` is the value already in the table and `new` the one being inserted. Drawing
each column independently is what makes `mergeEnvIdx`'s indexing load-bearing above width
one — a body reading `old0` where the column is `old1` computes a different tuple, and the
guarded reads stop firing.

**The bodies**, and what a row count sees of each:

* `(set (Log (L)) …)` — `L` and `Log` occur nowhere else in a generated program, so both
  counts are 0 if the body never ran and 1 if it did, which separates "runs the body" from
  "ignores it" with no rule at all. `genMergeProgram`'s `Kept`/`Lost` rules then read
  `Log`'s value against the two colliding column-0 values, so the pair also reports *which*
  of the two rows the model called `old` from inside a body. This draw is also what puts
  **two** merge functions in one program, the second written from the first's body.
* `(union (U) (V))` — `genMergeProgram` seeds `W` at both operands, so `W` is 2 if the body
  never ran and 1 if it did. The body's whole effect is an equality, and an equality is
  exactly what a row count can see. This is egglog's union-find `:merge` in miniature.
* a `let` and a `set` of the bound variable, which is the block form past one action and a
  `let`-bound value flowing into both a `set` and the result tuple.

The `let`-only draw writes nothing, and it takes egglog's no-op skip unobservably: its
result is `min v v = v` either way.

**Why a writing body could not be drawn before**, and it was never a fragment question:
two successive divergences, both recorded above. egglog keyed the side table's row on a
dangling e-class whenever the collision left the body's column unchanged (3), and once the
Rust was fixed the model fired the body at congruent-but-unequal keys holding the same
value, where egglog skips (4). A writing body is precisely the observer for both, which is
why widening the draw is what found them. -/
private def genMergeSpec (w : Nat) (s : Nat) : MergeSpec × Nat :=
  let (res, s) := genCombiners w w s
  let (logged, s) := genCombiner w 0 s
  let (shape, s) := pick 8 s
  match shape with
  | 4 => (.merge [.letBind "s" logged] (.var "s" :: res.tail), s)
  | 5 => (.merge [.set "Log" [C "L"] [logged]] res, s)
  | 6 => (.merge [.union (C "U") (C "V")] res, s)
  | 7 => (.merge [.letBind "s" logged, .set "Log" [C "L"] [.var "s"]]
            (.var "s" :: res.tail), s)
  | _ => (.merge [] res, s)

/-- Whether a drawn body writes the side table, which the program then has to declare —
`writeCase`'s `illegalSets` guard is what an omission would trip. -/
private def specSetsLog (m : MergeSpec) : Bool := m.setTargets.contains "Log"

/-- Whether a drawn body asserts an equality, which only `seedW` makes observable. -/
private def specUnions : MergeSpec → Bool
  | .merge body _ => body.any fun a => match a with
    | .union _ _ => true
    | _ => false
  | _ => false

/-- One value column: a literal, or `min`/`max` applied to two of them, together with the
integer it denotes.

This is where the random stream gets a primitive **outside** a `:merge` body — a value
column of a top-level `set` and of a rule head's, which is where `tests/interval.egg` puts
one too. `min` and `max` are the one place the model *computes* rather than *builds*
(`Prim.apply` against `Expr.eval`'s constructor case), and returning the denotation beside
the expression is what makes that observable: `witnessRule` reads the row back at the
literal the primitive must produce, so a model that built the term `min(5, 3)`, computed
the other operation, or got stuck writes something the read cannot find and `Won` falls to
0. Getting stuck is louder still — `expectedSizes` prints `STUCK`. -/
private def genValue (s : Nat) : Expr × Int × Nat :=
  let (i, s) := pick 4 s
  let (a, s) := pick 9 s
  let x : Int := a
  if i < 2 then (num x, x, s)
  else
    let (b, s) := pick 9 s
    let y : Int := b
    if i == 2 then (.app "min" [num x, num y], min x y, s)
    else (.app "max" [num x, num y], max x y, s)

/-- `n` value columns, each with the integer it denotes. -/
private def genValues : Nat → Nat → List (Expr × Int) × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (e, v, s) := genValue s
    let (es, s) := genValues k s
    ((e, v) :: es, s)

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
top-level action. The body is abstracted from a term the program builds, so it fires, and
the value columns are `genValue`'s, so a primitive is applied in a **rule head** — the
position `Rule.noLookup` polices and so the one most likely to be rejected by mistake. -/
private def genMergeRule (arity w : Nat) (src : Expr) (s : Nat) : Rule × Nat :=
  let (p, s) := genPattern ["a", "b"] src s
  let (ks, s) := genKeysOver p.vars arity s
  let (vs, s) := genValues w s
  (⟨[.expr p], [.set "Dist" ks (vs.map Prod.fst)], ""⟩, s)

/-- Reads back the value tuple the program wrote *first*, at the key it wrote it at, and
builds `Won` if it is still there.

Drawn from nothing: every generated case gets this rule. It is what makes a merge's
**answer** observable through an oracle that only counts rows — `Won` is 1 exactly when the
first write survived the collision, so `:merge old` and `:merge new` differ by a row here
and are indistinguishable everywhere else. `genMergeReadRule` cannot do the job, because it
draws its key and value and so reports on a collision only by luck: with the model binding
`old` and `new` backwards, all 30 generated merge cases still passed.

Above width one the tuple is read whole, so a per-column combiner drawn from the wrong
`mergeEnvIdx` binding also moves it; and the values are `genValue`'s **denotations**, so a
primitive the model built instead of computing moves it too.

The query is ground, so it costs one substitution and no enumeration. -/
private def witnessRule (key : List Expr) (vals : List Int) : Rule where
  query := [.values (vals.map num) "Dist" key]
  actions := [.expr (.app "Won" key)]
  ruleset := ""

/-- A rule *reading* `Dist` from its body: a `Pattern.values` atom whose value column is
either a fresh variable (existence) or the literal the program wrote (the value). Its head
builds a `Hit`, so whether and how often it fired is visible in `(print-size)`.

This is the path `MERGE.md` called the fragment boundary — "merge functions are written
and never read" — and leaving it there meant the read path, reachable through `execM` from
`ValidSubst`, had **no** coverage. Reading an analysis function in a rule body is ordinary
egglog, so there was no reason for the boundary except that nothing had run the merge
implementation.

`key` and `val` are a key the program actually writes and the value it writes there, and
the draw prefers them to freshly generated ones — the same correction `genPattern` needed
and for the same reason. A freely drawn key hits a written one by luck, and a freely drawn
value matches by one chance in nine, so most reads returned nothing: with the free draw
only 6 of 30 generated cases had the read fire at all, which is coverage of the *failing*
branch of a lookup and not of a lookup.

The existence shape binds **one** fresh variable, in column 0, and pins the remaining
columns at literals. `matchQuery` enumerates `|terms| ^ |vars|`, so a fresh variable per
column would cost a width-3 read two more factors of the term set and time the case out —
and a timeout is a case the suite *loses*, not a case it runs. -/
private def genMergeReadRule (arity w : Nat) (src : Expr) (key : List Expr)
    (vals : List Int) (s : Nat) : Rule × Nat :=
  let (p, s) := genPattern ["a", "b"] src s
  let (useKey, s) := pick 3 s
  let (ks, s) := if useKey = 0 then genKeysOver p.vars arity s else (key, s)
  let (useVal, s) := pick 3 s
  let (vs, s) :=
    if useVal = 0 then
      let (fresh, s) := genValues w s
      (fresh.map Prod.snd, s)
    else (vals, s)
  let (shape, s) := pick 2 s
  let cols : List Expr :=
    if shape = 0 then .var "o" :: (vs.map num).tail else vs.map num
  (⟨[.expr p, .values cols "Dist" ks], [.expr (.app "Hit" [p])], ""⟩, s)

/-- One random `:merge` case.

The **key arity** is drawn from 0 to 3 and the **value width** from 1 to 3, so the two
column counts that had never varied now do. Arity 0 is the empty key tuple — `congrKeys` at
length zero, with one key class for the whole table — and arity 3 makes the key comparison
walk two columns before reaching the one a `union` moved. Width above one is what gives
`mergeEnvIdx`'s indexed bindings anything to get wrong.

The side table and the equality seeds are conditional on what `genMergeSpec` drew, because
neither is inert: `Log` has to be declared *before* `Dist`, whose body writes it, and `W`'s
two rows are what turn a body's `union` into a row count. -/
private def genMergeProgram (s : Nat) : Program :=
  let (arity, s) := pick 4 s
  let (w, s) := pick 3 s
  let width := w + 1
  let (spec, s) := genMergeSpec width s
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
  let (v₁, s) := genValues width s
  -- And half write the second row with the *first* row's values. Two colliding rows that
  -- agree on every value column are a collision egglog resolves by running **no** body at
  -- all, and the model's `noConflict` has to agree; drawing the columns independently
  -- reaches that at roughly one chance in `9 ^ width`, which is to say never. With
  -- `sameKey` this is the equal-values-at-one-key shape, and with the key union below it is
  -- the congruent-but-unequal-keys one — the two shapes the writing-body divergences
  -- turned on.
  let (sameVal, s) := pick 2 s
  let (v₂', s) := genValues width s
  let v₂ := if sameVal = 0 then v₁ else v₂'
  let (v₃, s) := genValues width s
  let (u₁, s) := genGround 1 s
  let (u₂, s) := genGround 1 s
  let (r, s) := genMergeRule arity width g s
  let (rr, s) := genMergeReadRule arity width g k₁ (v₁.map Prod.snd) s
  let (uShape, s) := pick 2 s
  let (rounds, _) := pick 2 s
  -- The `union`s. Two freely drawn ground terms relate the program's own keys only by
  -- luck, so half the cases instead union `k₁` and `k₂` **column by column**, which is what
  -- makes their rows collide during the rebuild rather than at the `set`. That collision is
  -- the shape `canon-*`, the `old`/`new` binding and the no-conflict skip all turn on, and
  -- unioning one column would not produce it above arity 1 — congruence is pointwise, so
  -- every column has to move. At arity 0 there is no column to union and the drawn pair is
  -- the only option; the key class is the empty tuple, which collides on its own.
  let unions : List Cmd :=
    if uShape = 0 || arity = 0 then [.action (.union u₁ u₂)]
    else (k₁.zip k₂).map fun p => .action (.union p.1 p.2)
  -- `Log` and `L` report *whether* the body ran, in their own row counts and with no rule.
  -- `Kept`/`Lost` read the logged value against the two colliding column-0 values, which
  -- is what reports which row the body called `old`; a single marker would confuse "the
  -- wrong value" with "no value at all".
  let logDecls : Program := if specSetsLog spec then [.decl "Log" logDecl] else []
  let logReads : Program :=
    if specSetsLog spec then
      [.rule (readInto "Kept" "Log" [C "L"] ((v₁.map Prod.snd).headD 0)),
       .rule (readInto "Lost" "Log" [C "L"] ((v₂.map Prod.snd).headD 0))]
    else []
  logDecls
    ++ [ .decl "Dist" { arity := arity, outArity := width, merge := some spec } ]
    ++ (if specUnions spec then seedW else [])
    ++ [ .action (.expr g),
         .action (.set "Dist" k₁ (v₁.map Prod.fst)),
         .action (.set "Dist" k₂ (v₂.map Prod.fst)),
         .action (.set "Dist" k₃ (v₃.map Prod.fst)) ]
    ++ unions
    ++ [ .rule r, .rule rr, .rule (witnessRule k₁ (v₁.map Prod.snd)) ]
    ++ logReads
    ++ List.replicate (rounds + 1) (Cmd.run "")

/-! ### The whole corpus

The cases `scripts/difftest.sh` runs, as data rather than as files, so that a harness which
does not go through egglog can reuse them. The two random families are drawn at the script's
default `RANDOM_CASES` and `MERGE_CASES`, and the seed is `k + 1` exactly as `main`'s
`seed`/`mergeseed` modes compute it. -/

/-- The 60 random constructor-fragment cases. -/
private def randomCases : List (String × Program) :=
  (List.range 60).map fun k => (s!"rand-{k}", genProgram (k + 1))

/-- The 30 random `:merge` cases. -/
private def randomMergeCases : List (String × Program) :=
  (List.range 30).map fun k => (s!"mrand-{k}", genMergeProgram (k + 1))

/-- Every case the difftest runs, in the order the script writes them. -/
private def allCases : List (String × Program) :=
  curated ++ curatedMerge ++ randomCases ++ randomMergeCases

set_option linter.hashCommand false in
#guard curated.length = 10
set_option linter.hashCommand false in
#guard curatedMerge.length = 66
set_option linter.hashCommand false in
#guard allCases.length = 166

/-! Three cases small enough to pin the encoding's behaviour at compile time. None has a
rule, so none runs the enumerator, whose cost is `|terms| ^ |vars|`. -/

/-- One construction and nothing else. -/
private def buildCase : Program := [.action (.expr (add (C "One") (C "Two")))]

/-- Two applications made congruent by a `union`, and nothing else — the smallest program
whose encoded view holds a stale key. -/
private def unionCase : Program :=
  [.action (.expr (add (C "One") (C "Two"))),
   .action (.expr (add (C "Two") (C "One"))),
   .action (.union (C "One") (C "Two"))]

/-- `unionCase` under a `Wrapper`, so the congruence the `union` creates has to travel
**up** a level. The harness's negative control: it is the same three commands and it does
not agree. -/
private def upCase : Program :=
  [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
   .action (.expr (.app "Wrapper" [add (C "Two") (C "One")])),
   .action (.union (C "One") (C "Two"))]

/-- `upCase` with unary constructors throughout: the same two-level shape, and the smallest
program in which the congruence has anywhere to travel. Cheaper only because the enumerator
is exponential in a rule's variable count and a unary view's rebuild rule has one fewer. -/
private def upThinCase : Program :=
  [.action (.expr (.app "H" [.app "F" [C "A"]])),
   .action (.expr (.app "H" [.app "F" [C "B"]])),
   .action (.union (C "A") (C "B"))]

/-- The probes, reachable from `difftest encode <fuel> <name>` by name. The `-run` variants
append one empty round, which is what makes `encode` emit a `Cmd.saturate rebuildRuleset` and
so the only way to ask whether the rebuild repairs the gap `upCase` shows. They are out of
the guards because running a rebuild is far too slow to sit in a build. -/
private def probeCases : List (String × Program) :=
  [("build", buildCase), ("union", unionCase),
   ("up", upCase), ("up-run", upCase ++ [.run ""]),
   ("up-thin", upThinCase), ("up-thin-run", upThinCase ++ [.run ""])]

namespace Egglog
/-! ### The proof encoding, by tuple count

`Encoding/Encode.lean`'s `encode` is parked M11 material and nothing had ever run it on a
program. This runs it over the corpus above and compares the encoded database's tuple counts
against the source run's.

It is a **self-consistency** check inside the model and deliberately not one against the
binary. egglog mints a fresh id per construction and lets the view merge dedup them, where
the ids here are structural, so against egglog "the induced equivalence is the same; the
entry counts are not" (`Encode.lean`, "Fresh ids"). Against our own source run they should
be.

#### Which two numbers

The source side is `Impl/Merge.lean`'s `keyRowCount f`: one class per congruence class of
`f`'s key tuples, which is `(print-size)`'s quantity and the one the whole difftest is
stated in. `Impl/Interp.lean`'s `rowCount` agrees with it on a constructor, so the source
side could use either; `keyRowCount` is chosen because it reads the same index the target
side has to.

The target side is `@fView`, and *neither* count is right there unadjusted:

* `rowCount (viewName f)` reads applications out of `terms`. `@fView` is a `.merge`
  function, so its entry term is `@fView(children…, eclass)` and this would count classes of
  the key-and-value pair; and `terms` never shrinks, so it would also count every entry a
  merge or a rebuild has since superseded. Its own docstring says "Constructors only".
* `keyRowCount (viewName f)` reads the index, which is the right table and the right
  key/value split — but it quotients by `closureF`, and on an encoded program `closureF` is
  the **identity**. `encodeAction` turns a source `union` into `.set @UF …`, so the encoded
  program contains no `Action.union` at all, `eqs` stays empty, and the congruence closure
  collapses to the diagonal. Quotienting by it quotients by nothing.

That is not a defect in `keyRowCount`; it is the encoding working. Equality on the target is
*only* what `@UF` and the views record (`Encode.lean`, "Reading the target"), so the
equivalence to quotient `@fView`'s keys by is `UFLeader`, not `Cong`. `viewClassCount` below
is `keyRowCount`'s shape with `closureF` replaced by that — a computable `ViewReprList`
composed with `UFLeader`, which is exactly the correspondence `SameClass` is stated over.

`viewEntryCount` — the raw `keyRowCount (viewName f)` — is reported beside it, because the
gap between the two is a documented property of this encoder rather than noise: the rebuild
rules re-key an entry by *adding* one at the leader's key and there is no `delete` to remove
the stale one, so "a half-rewritten entry is an extra entry rather than a lost one"
(`rebuildRules`). The class count is the claim; the entry count is the price.

The two numbers really do come apart, and the guards below pin the smallest case where they
do: `unionCase` is one source key class, one view class and **three** view entries. A harness
that had reached for `keyRowCount` on both sides would have reported a mismatch there and
been wrong about it.

#### What is actually runnable

Encoding a query multiplies the e-matcher's exponent: one view read per subterm, each
binding an id variable **and a proof variable**, so `Program.widestRule` goes from 0–3 across
the in-domain corpus to 5–23, and `matchQuery` is `|valueTerms| ^ that`. `difftest
encode-cost` prints both exponents per case, which is the number to look at before waiting on
one — though it is only half the answer, since `|valueTerms|` varies as much as the exponent
does, and the proof column moves that too: a proof node is an ordinary constructor term, so
every proof the rebuild composes joins the candidate universe.

`Impl/Interp.lean`'s "Pruning the candidate cross product" is what keeps the second variable
per read from multiplying the whole search rather than its own atom's block. It was not
enough on its own — 12 of 70 at a 60 s budget — and "Joining over the row index" is what
followed it. **63 of the 70 in-domain cases finish** at 60 s and 65 at 300 s, all reporting
`AGREE`, against 58 and 64 *before* the proof column: the enumerator now more than pays for
the column it was struggling under. Nothing regressed — every case that finished under the
older enumerators is faster, `union` 6 min 5 s → 1.3 s and `actions` 253 s → 1.1 s.

Where it goes is measured, and it is e-matching and not the merge phase: on `unionCase`'s
last rebuild the round costs 207 s, of which the congruence closure is 106 ms, one merge
pass 1 ms and the whole merge saturation 322 ms. The rest is `execRunRules`. Two things
multiply there and neither is the encoder's shape: the view read's proof variable adds a
`|valueTerms|` factor **inside its own atom's block**, which pruning cannot remove because
the atom is not decided until its last column is bound; and every proof the rebuild composes
is an ordinary constructor term, so it joins `valueTerms` and raises the base. What that
needs is the enumeration replaced by a join over the index — bind a value column *from the
rows* rather than guess it — which pruning approximates and does not replace.
-/

/-! #### `encode`'s domain, decided

`Program.EncodeDomain` as a `Bool`, with the equivalence proved, so that the census below
and the hypothesis a theorem would carry cannot drift apart. -/
/-- `EncodeDomain.ctorsOnly` at one command. -/
def Cmd.ctorDeclB : Cmd → Bool
  | .decl _ d => d.merge.isNone
  | _ => true

theorem Cmd.ctorDeclB_iff (c : Cmd) :
    c.ctorDeclB = true ↔ ∀ f d, c = Cmd.decl f d → d.merge = none := by
  cases c <;> simp [Cmd.ctorDeclB, Option.isNone_iff_eq_none]

/-- `Action.NoSet`, computed. -/
def Action.noSetB : Action → Bool
  | .set _ _ _ => false
  | _ => true

theorem Action.noSetB_iff (a : Action) : a.noSetB = true ↔ a.NoSet := by
  cases a <;> simp [Action.noSetB, Action.NoSet]

/-- `Pattern.NoValues`, computed. -/
def Pattern.noValuesB : Pattern → Bool
  | .values _ _ _ => false
  | _ => true

theorem Pattern.noValuesB_iff (p : Pattern) : p.noValuesB = true ↔ p.NoValues := by
  cases p <;> simp [Pattern.noValuesB, Pattern.NoValues]

/-- `Cmd.NoSet`, computed. -/
def Cmd.noSetB : Cmd → Bool
  | .action a => a.noSetB
  | .rule r => r.actions.all Action.noSetB && r.query.all Pattern.noValuesB
  | _ => true

theorem Cmd.noSetB_iff (c : Cmd) : c.noSetB = true ↔ c.NoSet := by
  cases c <;>
    simp [Cmd.noSetB, Cmd.NoSet, Action.noSetB_iff, Pattern.noValuesB_iff, List.all_eq_true]

/-- `Program.EncodeDomain`, computed. -/
def Program.encodeDomainB (p : Program) : Bool :=
  p.all Cmd.ctorDeclB && p.all Cmd.noSetB
    && p.ctors.all (fun fk => (Prim.ofName fk.1).isNone)
    && p.ctors.all (fun fk => !"@".isPrefixOf fk.1)
    && p.vars.all (fun v => !"@".isPrefixOf v)

/-- **The census below counts exactly `EncodeDomain`.** -/
theorem Program.encodeDomainB_iff (p : Program) :
    p.encodeDomainB = true ↔ p.EncodeDomain := by
  simp only [Program.encodeDomainB, Bool.and_eq_true, List.all_eq_true, Cmd.ctorDeclB_iff,
    Cmd.noSetB_iff, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.eq_false_iff, ne_eq]
  exact ⟨fun h => ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩,
    fun h => ⟨⟨⟨⟨h.ctorsOnly, h.noSet⟩, h.noPrim⟩, h.noAt⟩, h.noAtVar⟩⟩

/-! #### Running the encoded program

`encode` emits `Cmd.saturate rebuildRuleset` after every run, so an encoded program is
outside `Program.NoSaturate` and `execM` reaches `runSaturateM`, which is fuel-bounded and
answers `none` on exhaustion. `execAt` takes the fuel as an argument so that "the rebuild
did not settle" and "a command got stuck" are different answers rather than the same
`none`; everything but `.saturate` is `execCmdM` unchanged, so `execAt runFuel` is `execM`.
-/
/-- `execM` with the `.saturate` fuel supplied by the caller. -/
def execAt (fuel : Nat) (d : FDatabase) : Program → Option FDatabase
  | [] => some d
  | .saturate R :: cs => (d.runSaturateM R fuel).bind fun d' => execAt fuel d' cs
  | c :: cs => (d.execCmdM c).bind fun d' => execAt fuel d' cs

/-- **At `runFuel` it is `execM`**, so raising the fuel is the only thing the parameter
does and a run that finishes is a run `execM` would have finished. -/
theorem execAt_runFuel (d : FDatabase) (p : Program) :
    execAt runFuel d p = d.execProgramM p := by
  induction p generalizing d with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp [execAt, FDatabase.execProgramM, FDatabase.execCmdM, ih]

/-- The first command of `p` that does not step, with its position. `none` is a run that
finished. -/
def stuckAt (fuel : Nat) (d : FDatabase) (i : Nat) : Program → Option (Nat × Cmd)
  | [] => none
  | .saturate R :: cs =>
      match d.runSaturateM R fuel with
      | none => some (i, .saturate R)
      | some d' => stuckAt fuel d' (i + 1) cs
  | c :: cs =>
      match d.execCmdM c with
      | none => some (i, c)
      | some d' => stuckAt fuel d' (i + 1) cs

/-- The exponent the e-matcher runs at: the most free variables any one rule's query has.
`matchQuery` assigns a query's free variables all at once from `valueTerms`, so a case costs
`|valueTerms| ^ this`, and encoding multiplies it — one view read per subterm binds an id
variable for each. An upper bound, since a global would already be bound; it is a cost proxy
and nothing reads it but the report. -/
def Program.widestRule (p : Program) : Nat :=
  (p.filterMap fun c => match c with
    | .rule r => some (Query.freeVars r.query []).length
    | _ => none).foldl max 0

/-! #### Reading the encoded database

`UFLeader`, computed. `@UF` is a `.merge` function of one key column, so the index holds at
most one row per key term and following it is a walk. The walk terminates because
`mergeBody` only ever writes `@UF (ordering-max x y) ↦ ordering-min x y`, so every edge
strictly descends `Term.blt`; the fuel is `rows.length`, which bounds any descending walk
through the index, and `ufLeader` is only ever called with it.

A self-loop is an ordinary entry rather than the absence of one — `UFEdge` carries `p ≠ t`
for that reason — so the walk stops at an edge that does not move. -/
/-- `@UF`'s recorded parent for `t`, if it moves. The proof column is read past: which
justification an edge carries is not what being an edge means (`Encode.lean`, `UFEdge`). -/
def ufParent (d : FDatabase) (t : Term) : Option Term :=
  (d.rows.find? fun r => r.fn == ufName && r.args == [t]).bind fun r =>
    match r.out with
    | [p, _] => if p == t then none else some p
    | _ => none

/-- `t`'s union-find leader. -/
def ufLeader (d : FDatabase) : Nat → Term → Term
  | 0, t => t
  | n + 1, t => match ufParent d t with
    | none => t
    | some p => ufLeader d n p

/-- `ufLeader` at the fuel that bounds any walk through the index. -/
def ufLeaderOf (d : FDatabase) (t : Term) : Term := ufLeader d d.rows.length t

/-- **The target-side count.** `@fView`'s key tuples, each mapped to its children's
union-find leaders, deduplicated: one per e-class tuple the view holds an entry for. This is
`keyRowCount` with the encoded program's own equality — `UFLeader` — in place of `closureF`,
which on an encoded program is the identity. -/
def viewClassCount (d : FDatabase) (f : FnName) : Nat :=
  ((d.keyLists (viewName f)).map fun ks => ks.map (ufLeaderOf d)).dedup.length

/-- The entries `@fView` actually holds, unquotiented. Reported beside `viewClassCount`
because the difference is what the missing `delete` costs: a rebuild adds the re-keyed entry
and cannot remove the stale one. -/
def viewEntryCount (d : FDatabase) (f : FnName) : Nat :=
  d.keyRowCount (viewName f)

/-! #### One case -/
/-- What running one case reports. -/
inductive EncOutcome where
  /-- Not in `Program.EncodeDomain`, so `encode` says nothing about it. -/
  | outOfDomain
  /-- The **source** run did not finish, so there is nothing to compare against. -/
  | sourceStuck (at? : Option (Nat × Cmd))
  /-- The encoded run did not finish; the command it stopped at says which hazard. -/
  | encodedStuck (at? : Option (Nat × Cmd))
  /-- Per source constructor: source key classes, target view classes, target view
  entries. -/
  | counts (rows : List (FnName × Nat × Nat × Nat))

/-- Run one source program against its encoding. `fuel` is `.saturate`'s. -/
def encodeCompare (fuel : Nat) (p₀ : Program) : EncOutcome :=
  let p := p₀.declared
  if !p.encodeDomainB then .outOfDomain
  else
    match execAt fuel FDatabase.empty p with
    | none => .sourceStuck (stuckAt fuel FDatabase.empty 0 p)
    | some d =>
      let q := encode p
      match execAt fuel FDatabase.empty q with
      | none => .encodedStuck (stuckAt fuel FDatabase.empty 0 q)
      | some e =>
        .counts (p.ctors.map fun fk =>
          (fk.1, d.keyRowCount fk.1, viewClassCount e fk.1, viewEntryCount e fk.1))

/-- Whether every source constructor's class count survived the encoding. **The claim.** -/
def EncOutcome.agrees : EncOutcome → Bool
  | .counts rows => rows.all fun r => r.2.1 == r.2.2.1
  | _ => false

/-- Whether the *entry* counts agree too. Strictly stronger, and expected to fail wherever a
rebuild has re-keyed an entry: there is no `delete` to retire the stale one. -/
def EncOutcome.entriesAgree : EncOutcome → Bool
  | .counts rows => rows.all fun r => r.2.1 == r.2.2.2
  | _ => false

/-- One line per case, for the report: `f:source/classes/entries` per source
constructor. -/
def EncOutcome.render (o : EncOutcome) : String :=
  match o with
  | .outOfDomain => "out-of-domain"
  | .sourceStuck none => "source-stuck (no command)"
  | .sourceStuck (some (i, c)) => s!"source-stuck at #{i} {c.toEgg}"
  | .encodedStuck none => "encoded-stuck (no command)"
  | .encodedStuck (some (i, c)) => s!"encoded-stuck at #{i} {c.toEgg}"
  | .counts rows =>
    (if o.agrees then "AGREE  " else "DIFFER ") ++
      String.intercalate " "
        (rows.map fun r => s!"{r.1}:{r.2.1}/{r.2.2.1}/{r.2.2.2}")

/-! #### The proofs the encoding writes, checked

`Encoding/Checker.lean` reads the **source** program and nothing else; the encoded run is
what writes the proofs. This runs one against the other — `difftest check <fuel> [case…]`.

The two were written in parallel and disagreed in three places, every one of them with the
checker on the wrong side of a shape the encoder had measured its way to: `@Congr` at one
name where the encoding writes the family `@Congr_k`, `@Rule_i` counting source patterns
where the encoding counts view reads, and `@Fiat` reading only the top-level actions. The
first two are visible on the syntax, and the theorems below are what keeps them fixed; the
third took running this to see, and is the last paragraph here.

**What a merge records is refused by design.** Both rows a collision settles keep the
resident row's proof (`Encode.lean`'s `mergeResult`), which proves `k = old0` and not the
`old0 = new0` the edge claims — egglog's `MergeFn`, the sixth justification `CHECKER.md`'s
minimal subset excludes. The report counts those apart from proofs that justify nothing.

**Measured.** `difftest check 64` at a 3600 s budget per case, run 76-way parallel: 75 of the
76 — the 70 in-domain corpus cases and the six probes — finish, and over them **724 of 824
recorded equalities check, 93 are merge-displaced, and 7 are unjustified**. `rand-19` is the
one that does not. `both-2` accounts for 14 of the 93 and `rand-43` for 13; `rand-15`,
`rand-18`, `rand-45`, `up-thin` and `up-thin-run` have four apiece, `up`, `up-run` and
`rand-59` three, five cases two, and 27 one. Seventy-seven of the 93 carry `(@Fiat)`. The 7
unjustified are three in `rand-57`, two in `rand-45`, and one each in `rand-33` and `both-2`.
The budget bounds the sweep and not the checker: `check 64 union` is 1.0 s where `encode 64
union` is 1.3 s, and the difference is the source run `encodeCompare` does and this does not —
reading and checking every proof is inside the noise of producing them.

**What running it found** was a third disagreement, and this was the only thing that could:
`@Fiat` reads the top-level actions of the source, but `encodeBuild` writes its view entry
`f(c…) = f(c…)` under `@Fiat` *whatever context the build is in*, so a term a **rule head**
constructs has no action to point at. egglog's `Fiat` has the other disjunct for exactly
this — `lhs == rhs && reflexive_value_term lhs` (`CHECKER.md`, "Node kinds") — and the
checker did not. It accounted for every rejection in the first sweep and nothing else did:
`seed-2` checked 0 of 3, `swap-1` 3 of 4, and both are 3 of 3 and 4 of 4 with
`Proof.reflProps` in. A corpus of *top-level* builds could not have seen it. -/

/-! ##### The two flattenings agree

`props` accepts `@Rule_i` at `Proof.premiseCount` premises and `encode` declares it at
`ruleProofArity`. They are computed on opposite sides — the source query flattened, and the
encoded query's view reads counted — so nothing but a proof keeps them equal. -/

/-- The generated variable is the same one on both sides. -/
theorem flatVar_eq_freshVar : Proof.flatVar = freshVar := rfl

mutual

/-- One application, flattened: the same e-class expression, the same premise count, and the
same next variable. -/
theorem flatExpr_agrees (e : Expr) (n : Nat) :
    (Proof.flatExpr e n).1 = (encodeQueryExpr e n).1 ∧
    ((Proof.flatExpr e n).2.1.filter Prod.snd).length
      = (queryProofs (encodeQueryExpr e n).2.1).length ∧
    (Proof.flatExpr e n).2.2 = (encodeQueryExpr e n).2.2 := by
  match e with
  | .lit l => simp [Proof.flatExpr, encodeQueryExpr, queryProofs]
  | .var v => simp [Proof.flatExpr, encodeQueryExpr, queryProofs]
  | .app f args =>
    obtain ⟨h1, h2, h3⟩ := flatArgs_agrees args n
    rcases hf : Proof.flatArgs args n with ⟨es, qs, n₁⟩
    rcases hg : encodeQueryArgs args n with ⟨es', ps, n₁'⟩
    rw [hf, hg] at h1 h2 h3
    simp only at h1 h2 h3
    subst h1; subst h3
    simp only [Proof.flatExpr, encodeQueryExpr, hf, hg]
    refine ⟨rfl, ?_, trivial⟩
    simp [queryProofs, List.filter_append, List.filterMap_append] at h2 ⊢
    omega

/-- `flatExpr_agrees` over an argument list. -/
theorem flatArgs_agrees (es : List Expr) (n : Nat) :
    (Proof.flatArgs es n).1 = (encodeQueryArgs es n).1 ∧
    ((Proof.flatArgs es n).2.1.filter Prod.snd).length
      = (queryProofs (encodeQueryArgs es n).2.1).length ∧
    (Proof.flatArgs es n).2.2 = (encodeQueryArgs es n).2.2 := by
  match es with
  | [] => simp [Proof.flatArgs, encodeQueryArgs, queryProofs]
  | e :: es =>
    obtain ⟨h1, h2, h3⟩ := flatExpr_agrees e n
    rcases hf : Proof.flatExpr e n with ⟨x, qs, n₁⟩
    rcases hg : encodeQueryExpr e n with ⟨x', ps, n₁'⟩
    rw [hf, hg] at h1 h2 h3
    simp only at h1 h2 h3
    subst h1; subst h3
    obtain ⟨k1, k2, k3⟩ := flatArgs_agrees es n₁
    rcases hf' : Proof.flatArgs es n₁ with ⟨ys, qs2, n₂⟩
    rcases hg' : encodeQueryArgs es n₁ with ⟨ys', ps2, n₂'⟩
    rw [hf', hg'] at k1 k2 k3
    simp only at k1 k2 k3
    subst k1; subst k3
    simp only [Proof.flatArgs, encodeQueryArgs, hf, hg, hf', hg']
    refine ⟨trivial, ?_, trivial⟩
    simp [queryProofs, List.filter_append, List.filterMap_append] at h2 k2 ⊢
    omega

end

/-- One source pattern. The entry atom carries a premise proof on both sides exactly when it
has two value columns, which under `EncodeDomain` no source pattern has. -/
theorem flatPattern_agrees (p : Pattern) (n : Nat) :
    ((Proof.flatPattern p n).1.filter Prod.snd).length
      = (queryProofs (encodePattern p n).1).length ∧
    (Proof.flatPattern p n).2 = (encodePattern p n).2 := by
  match p with
  | .values vs f as =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
      simp [Proof.flatPattern, encodePattern, queryProofs]
  | .expr e =>
    obtain ⟨_, h2, h3⟩ := flatExpr_agrees e n
    rcases hf : Proof.flatExpr e n with ⟨x, qs, n₁⟩
    rcases hg : encodeQueryExpr e n with ⟨x', ps, n₁'⟩
    rw [hf, hg] at h2 h3
    simp only at h2 h3
    subst h3
    simp only [Proof.flatPattern, encodePattern, hf, hg]
    exact ⟨h2, trivial⟩
  | .eq e₁ e₂ =>
    obtain ⟨_, h2, h3⟩ := flatExpr_agrees e₁ n
    rcases hf : Proof.flatExpr e₁ n with ⟨x, qs, n₁⟩
    rcases hg : encodeQueryExpr e₁ n with ⟨x', ps, n₁'⟩
    rw [hf, hg] at h2 h3
    simp only at h2 h3
    subst h3
    obtain ⟨_, k2, k3⟩ := flatExpr_agrees e₂ n₁
    rcases hf' : Proof.flatExpr e₂ n₁ with ⟨y, qs2, n₂⟩
    rcases hg' : encodeQueryExpr e₂ n₁ with ⟨y', ps2, n₂'⟩
    rw [hf', hg'] at k2 k3
    simp only at k2 k3
    subst k3
    simp only [Proof.flatPattern, encodePattern, hf, hg, hf', hg']
    refine ⟨?_, trivial⟩
    simp [queryProofs, List.filter_append, List.filterMap_append] at h2 k2 ⊢
    omega

/-- A whole query. -/
theorem flatQuery_agrees (q : Query) (n : Nat) :
    ((Proof.flatQuery q n).1.filter Prod.snd).length
      = (queryProofs (encodeQuery q n).1).length ∧
    (Proof.flatQuery q n).2 = (encodeQuery q n).2 := by
  match q with
  | [] => simp [Proof.flatQuery, encodeQuery, queryProofs]
  | p :: ps =>
    obtain ⟨h2, h3⟩ := flatPattern_agrees p n
    rcases hf : Proof.flatPattern p n with ⟨qs, n₁⟩
    rcases hg : encodePattern p n with ⟨rs, n₁'⟩
    rw [hf, hg] at h2 h3
    simp only at h2 h3
    subst h3
    obtain ⟨k2, k3⟩ := flatQuery_agrees ps n₁
    rcases hf' : Proof.flatQuery ps n₁ with ⟨qs2, n₂⟩
    rcases hg' : encodeQuery ps n₁ with ⟨rs2, n₂'⟩
    rw [hf', hg'] at k2 k3
    simp only at k2 k3
    subst k3
    simp only [Proof.flatQuery, encodeQuery, hf, hg, hf', hg']
    refine ⟨?_, trivial⟩
    simp [queryProofs, List.filter_append, List.filterMap_append] at h2 k2 ⊢
    omega

/-- **The arity the checker demands is the arity the encoding declares.** `props` refuses an
`@Rule_i` whose argument list is not `premiseCount` long, and `proofDecls` declares it at
`ruleProofArity`; a program `encode` writes can therefore never be refused for its premise
count. -/
theorem premiseCount_eq_ruleProofArity (r : Rule) :
    Proof.premiseCount r = ruleProofArity r := (flatQuery_agrees r.query 0).1

/-! ##### Reading the proofs out of the final state -/

mutual

/-- A term as egglog writes it. `Expr.toEgg` prints the syntax; this prints what it
evaluates to, which is what a row holds. -/
def Term.toEgg : Term → String
  | .lit (.int i) => toString i
  | .app f args => "(" ++ f ++ Term.toEggArgs args ++ ")"

/-- `Term.toEgg` over an argument list, each preceded by a space. -/
def Term.toEggArgs : List Term → String
  | [] => ""
  | t :: ts => " " ++ t.toEgg ++ Term.toEggArgs ts

end

/-- Every equality the encoded database records, with the proof it was recorded with:
`@UF (t) ↦ (p, pf)` is `pf : t = p` and `@fView (c…) ↦ (e, pf)` is `pf : f(c…) = e`, both
read key-to-value (`Encode.lean`, "Proof terms").

Those are the only two tables with a proof column. `@fTerm` has one value column and the
proof terms' own rows — a proof node is an ordinary constructor application, so `addTerm`
indexes it — have none, so matching on two value columns picks out exactly the claims. -/
def proofRows (p : Program) (d : FDatabase) : List (Term × Term × Term) :=
  d.rows.filterMap fun r =>
    match r.out with
    | [b, pf] =>
        if r.fn == ufName then
          match r.args with
          | [t] => some (t, b, pf)
          | _ => none
        else (p.ctors.find? fun fk => viewName fk.1 == r.fn).map fun fk =>
          (.app fk.1 r.args, b, pf)
    | _ => none

/-- How one recorded equality came out. -/
inductive Verdict where
  /-- The proof justifies the equality its row claims. -/
  | checks
  /-- The proof is a **copy**: another row records the same proof term for a claim it does
  justify, carried here. That is what a merge leaves — both rows a collision settles keep
  the *resident* row's `old1` (`Encode.lean`, `mergeResult`), which proves `k = old0` and
  not the `old0 = new0` the edge then claims, and the row it was taken from survives because
  a merge in this model displaces rather than deletes. A classifier and not a provenance:
  `@Fiat` is written by every build, so the witness row this finds need not be the one the
  merge read. Both claims are printed, so the reading is the reader's. -/
  | displaced (a b : Term)
  /-- It justifies nothing, and no other row records it either. -/
  | unjustified
  deriving DecidableEq

/-- The verdict is `checks`. -/
def Verdict.isChecks : Verdict → Bool
  | .checks => true
  | _ => false

/-- The verdict is `displaced`. -/
def Verdict.isDisplaced : Verdict → Bool
  | .displaced _ _ => true
  | _ => false

/-- The claim some other row records this proof for and which it does justify, if there is
one. A row ending where this claim ends is preferred, since that is where a merge's `old1`
came from — `old0` is one of the two endpoints of the edge `mergeBody` writes. `ChecksAt` is
asked only of rows carrying the same proof term, so the scan is cheap. -/
def displacedBy (C : Proof.Ctx) (rows : List (Term × Term × Term))
    (cl : Term × Term × Term) : Option (Term × Term) :=
  let ok := fun (r : Term × Term × Term) =>
    r.2.2 == cl.2.2 && !((r.1, r.2.1) == (cl.1, cl.2.1)) && Proof.ChecksAt C r.2.2 r.1 r.2.1
  let hit : Option (Term × Term × Term) :=
    match rows.find? fun (r : Term × Term × Term) =>
        (r.2.1 == cl.1 || r.2.1 == cl.2.1) && ok r with
    | some r => some r
    | none => rows.find? ok
  hit.map fun r => (r.1, r.2.1)

/-- One row's verdict. -/
def verdictOf (C : Proof.Ctx) (rows : List (Term × Term × Term))
    (cl : Term × Term × Term) : Verdict :=
  if Proof.ChecksAt C cl.2.2 cl.1 cl.2.1 then .checks
  else match displacedBy C rows cl with
    | some (a, b) => .displaced a b
    | none => .unjustified

/-- What checking one case reports. -/
inductive CheckOutcome where
  /-- Not in `Program.EncodeDomain`, so `encode` says nothing about it. -/
  | outOfDomain
  /-- The encoded run did not finish, so there is no final state to read. -/
  | encodedStuck (at? : Option (Nat × Cmd))
  /-- Every recorded equality, with its verdict. -/
  | verdicts (vs : List (Verdict × Term × Term × Term))

/-- Encode one case, run it, and check every proof the final state holds against the
**source** program. `fuel` is `.saturate`'s, as in `encodeCompare`. -/
def encodeCheck (fuel : Nat) (p₀ : Program) : CheckOutcome :=
  let p := p₀.declared
  if !p.encodeDomainB then .outOfDomain
  else
    let q := encode p
    match execAt fuel FDatabase.empty q with
    | none => .encodedStuck (stuckAt fuel FDatabase.empty 0 q)
    | some e =>
      let C := Proof.ctxOf p
      let rows := proofRows p e
      .verdicts (rows.map fun cl => (verdictOf C rows cl, cl))

/-- One line per case, plus one per equality the checker does not accept. -/
def CheckOutcome.render (o : CheckOutcome) : String :=
  match o with
  | .outOfDomain => "out-of-domain"
  | .encodedStuck none => "encoded-stuck (no command)"
  | .encodedStuck (some (i, c)) => s!"encoded-stuck at #{i} {c.toEgg}"
  | .verdicts vs =>
    let nc := (vs.filter fun p => p.1.isChecks).length
    let nd := (vs.filter fun p => p.1.isDisplaced).length
    let bad := (vs.filter fun p => !p.1.isChecks).map fun p =>
      let claim := p.2.1.toEgg ++ " = " ++ p.2.2.1.toEgg ++ " by " ++ p.2.2.2.toEgg
      match p.1 with
      | .displaced a b =>
        "\n  displaced   " ++ claim ++ ", which proves " ++ a.toEgg ++ " = " ++ b.toEgg
      | _ => "\n  unjustified " ++ claim
    (if vs.length == nc + nd then "CHECKS " else "REJECT ")
      ++ s!"{nc} checked, {nd} merge-displaced, \
            {vs.length - nc - nd} unjustified of {vs.length}"
      ++ String.join bad

/-! #### What the harness pins

The census. `encode`'s fragment is the constructor one, so the in-domain cases are exactly
the two constructor families and none of the `:merge` ones — which is 70 of 166, and the
reason a green sweep here is a statement about 42% of the suite. -/
set_option linter.hashCommand false in
#guard (allCases.filter fun c => (c.2.declared).encodeDomainB).map Prod.fst
  = curated.map Prod.fst ++ randomCases.map Prod.fst
set_option linter.hashCommand false in
#guard (allCases.filter fun c => (c.2.declared).encodeDomainB).length = 70

/-! And they are out for the one reason `MERGE.md` calls permanent rather than a gap: every
one of the 96 declares a `:merge` function, so it is `EncodeDomain.ctorsOnly` that fails and
not a generated-name clash or a shadowed primitive. -/
set_option linter.hashCommand false in
#guard (allCases.filter fun c => !(c.2.declared).encodeDomainB).all fun c =>
  !((c.2.declared).all Cmd.ctorDeclB)

/-! **`encode` runs.** It did not while `encodeBuild` read its view back to get the
canonical member: `(let x (@fView c…))` is a lookup, which `Program.illegalReads` rejects
statically and `Expr.eval` has no rule for at all, so the interpreter stopped at the first
one — command 18 of the one-construction program, before any count existed. The skolem
`.app f es` names the class as well as the canonical member does, since equality on the
target is only what `@UF` records, so the read-back was an optimization and dropping it
leaves a head with no read in it.

The four front-end checks are static analysis and stay compile-time. Anything that *runs* a
program does not: a rebuild now follows every writing command, so executing an encoded
program saturates a ruleset once per action, and doing that during elaboration made
`lake build difftest` exceed fifteen minutes. Those moved to `encodeSelfTests`, run by
`difftest encode-selftest`. -/
set_option linter.hashCommand false in
#guard (encode buildCase.declared).illegalReads.isEmpty
set_option linter.hashCommand false in
#guard (encode buildCase.declared).illegalSets.isEmpty
set_option linter.hashCommand false in
#guard (encode buildCase.declared).arityErrors.isEmpty
set_option linter.hashCommand false in
#guard (encode buildCase.declared).arityConflicts.isEmpty

/-! **The class count is the claim; the entry count is the price.** `unionCase` builds
`Add(One, Two)` and `Add(Two, One)` and unions the leaves, so the source has one key class.
The encoded view holds three entries — the two the builds wrote, `[One, Two]` and
`[Two, One]`, and the `[One, One]` the rebuild re-keyed them both onto — and there is no
`delete` to retire the two stale ones, so `viewEntryCount` is 3 where `viewClassCount` is 1.
This is the smallest case where the two target-side numbers come apart, and it is the whole
reason the harness reports both. -/
/-- The checks that have to **run** a program. Compile-time `#guard`s cannot carry these:
each encoded action is followed by a saturating rebuild, so elaborating them ran the
e-matcher tens of times. `difftest encode-selftest` executes them and reports failures. -/
def encodeSelfTests : List (String × (Unit → Bool)) :=
  [ ("encode buildCase runs", fun _ => (execM (encode buildCase.declared)).isSome),
    ("encode buildCase never sticks", fun _ =>
      stuckAt runFuel FDatabase.empty 0 (encode buildCase.declared) = none),
    ("buildCase agrees", fun _ =>
      (encodeCompare runFuel buildCase).render = "AGREE  Add:1/1/1 One:1/1/1 Two:1/1/1"),
    ("unionCase agrees on classes", fun _ => (encodeCompare runFuel unionCase).agrees),
    ("unionCase entries exceed classes", fun _ =>
      !(encodeCompare runFuel unionCase).entriesAgree),
    -- The regression test for the rebuild-after-action fix: the congruence a top-level
    -- `union` creates has to travel up a level, and did not until `encodeCmd` emitted a
    -- rebuild after an action. `upCase` is the same shape at binary `Add` and is what stood
    -- here, reporting `DIFFER Wrapper:1/2/2` before the fix. **The proof column retired
    -- it**: 1.1 s before, about 1 h 50 m after, which was the whole of this selftest's two
    -- hours — the enumerator costs `|valueTerms| ^ |vars|` and a binary view's rebuild rule
    -- has one variable more than a unary one. `upThinCase` is that unary shape, `AGREE
    -- H:1/1/2 F:1/1/2 A:1/1/1 B:1/1/1` in 98 s, and it fails the same way for the same
    -- reason. The swap takes the whole list to 7 min 3 s, which is a gate again.
    ("upThinCase agrees on classes", fun _ => (encodeCompare runFuel upThinCase).agrees) ]

/-! **The negative control, and a defect it exposes.** Put `unionCase`'s two applications
under a `Wrapper` and the congruence has to travel up a level: the source says one `Wrapper`
key class, the encoding says two. The two `Add` ids are unioned only when the rebuild
re-keys both view entries onto the leaders and the merge collides them — and `encodeCmd`
emits `Cmd.saturate rebuildRuleset` **only after a `run` or a `saturate`**, so a source
program made of top-level actions gets no rebuild at all and the target simulates no
congruence above the columns a `union` names directly.

That is a defect in `encode` rather than in the correspondence, and it is not an artefact of
the skolem ids: egglog's `set-if-empty` would mint the same two distinct ids for the two
`Add` shapes, so the two `Wrapper` entries sit at distinct keys under either reading. The
source's congruence is a closure and holds the moment the `union` lands; the target's is a
ruleset, and `execCmdM` runs a merge phase after every top-level action but nothing runs the
rebuild.

**One empty round repaired it**, which is what said the rebuild was the missing piece and
nothing else was: the `up-thin-run` probe is `upThinCase ++ [.run ""]`, whose source counts
are unchanged and whose encoded counts then agreed. **`encodeCmd` now emits
`Cmd.saturate rebuildRuleset` after a top-level action too**, which is where egglog puts it
— after every command but a function, rule or sort declaration. `upThinCase` is kept as the
regression test for that, in `encodeSelfTests` rather than as a `#guard`, because running
the rebuild after each action costs a saturation per action.

It is also what makes the corpus result readable: the curated `actions` case was action-only
too, and agreed only because the congruence it asserts is `One = One`. Every other in-domain
case ends in a `run`, so every other one got a rebuild even before the fix — which is why the
corpus could not see this and a probe was needed. -/

/-! And `actions` is the only in-domain case the gap can reach, because it is the only one
with no `run` in it — so the corpus cannot see this defect and a probe was needed. -/
set_option linter.hashCommand false in
#guard ((allCases.filter fun c => (c.2.declared).encodeDomainB).filter fun c =>
    !c.2.any fun cmd => match cmd with | .run _ => true | _ => false).map Prod.fst
  = ["actions"]

end Egglog

/-! ### Entry point -/

/-- Write one case, refusing outright to emit a program egglog would reject.

**The constructors are declared first** (`Program.declared`). Declaration is required, so a
program that applies an undeclared name gets stuck in `Expr.eval`; the generators below
write uses and not declarations, exactly as the `datatype` header this file emits is read
off the uses, so the declarations are derived here rather than threaded through every
generator. They render as nothing on the egglog side — a constructor declaration is the
header — so the two engines see the same file they always did.

A rejected program is not a failing case but a missing one, and a generator that quietly
stops producing runnable programs is the failure this whole file is written against — so
each check is an abort, not a skip. Three rules, all raised by egglog's typechecker before
the offending command runs:

* `set`'s: `(set (f args…) v)` is legal only on a declared function, and is a type error on
  a constructor or a relation (`Program.illegalSets`);
* every use of a declared function has its declared key and value column counts
  (`Program.arityErrors`, over `Impl/Check.lean`'s `Cmd.arityOk`);
* nothing reads a row except a `Pattern.values` atom (`Program.illegalReads`, over
  `Cmd.noLookup`) — egglog rejects this in a rule head, and the model everywhere;
* no name is used at two key arities, which the emitted `datatype` header cannot express
  (`Program.arityConflicts`). -/
private def writeCase (dir name : String) (p₀ : Program) : IO Unit := do
  let p := p₀.declared
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

/-- One line of the encoding report. -/
private def encodeLine (fuel : Nat) (c : String × Program) : String :=
  s!"{c.1}: {(Egglog.encodeCompare fuel c.2).render}"

/-- `difftest <dir> curated` writes the curated cases, `difftest <dir> merge` the curated
`:merge` ones; `difftest <dir> seed <n>` writes one random constructor case named
`rand-<n>` and `difftest <dir> mergeseed <n>` one random `:merge` case named `mrand-<n>`.
The two random families are named apart so the script can report a profile distribution
for each — a collapsing distribution is how a generator that has stopped exercising
anything shows up, and a single pooled number would hide it.

`difftest encode-domain` prints how much of the corpus `encode` is defined on,
`difftest encode <fuel> [case…]` runs the tuple-count comparison — every case, or the named
ones — and `difftest check <fuel> [case…]` runs the encoded program and checks every proof
its final state records against the source program (`Egglog.encodeCheck`). These write
nothing and never invoke egglog; the comparison is between the model and itself. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["encode-domain"] =>
    let inDom := allCases.filter fun c => (c.2.declared).encodeDomainB
    IO.println s!"{inDom.length} of {allCases.length} cases are in encode's domain"
    IO.println (String.intercalate " " (inDom.map Prod.fst))
    return 0
  | ["encode-cost"] =>
    -- `name source-width encoded-width`: the enumerator's exponent before and after.
    for (name, p₀) in allCases do
      let p := p₀.declared
      if p.encodeDomainB then
        IO.println s!"{name} {p.widestRule} {(Egglog.encode p).widestRule}"
    return 0
  | ["encode-selftest"] =>
    let mut bad := 0
    for (name, t) in encodeSelfTests do
      if t () then IO.println s!"ok   {name}"
      else do IO.println s!"FAIL {name}"; bad := bad + 1
    IO.println s!"encode-selftest: {encodeSelfTests.length - bad} passed, {bad} failed"
    return (if bad == 0 then 0 else 1)
  | "encode" :: fuel :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n =>
      let cases := if names.isEmpty then allCases
        else (allCases ++ probeCases).filter fun c => names.contains c.1
      for c in cases do IO.println (encodeLine n c)
      return 0
  | "check" :: fuel :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n =>
      let cases := if names.isEmpty then allCases
        else (allCases ++ probeCases).filter fun c => names.contains c.1
      for c in cases do IO.println s!"{c.1}: {(Egglog.encodeCheck n c.2).render}"
      return 0
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
    IO.eprintln "       difftest encode-domain | encode-cost | encode-selftest"
    IO.eprintln "       difftest encode <fuel> [case…] | check <fuel> [case…]"
    return 1
