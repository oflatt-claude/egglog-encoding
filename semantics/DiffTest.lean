import EgglogSemantics.Tests.Congruence
import EgglogSemantics.Provenance.Extract
import EgglogSemantics.Resugar.Export
import EgglogSemantics.Tests.Egg
import EgglogSemantics.Tests.Parse
import EgglogSemantics.Tests.Render

/-!
# Differential tests

Curated and seeded programs cover constructors and merge functions. Each invocation
writes a `.egg` program and expected row counts; `scripts/difftest.sh` runs egglog with
a per-case timeout. Emission checks reject unsupported programs.

Nullary constructors stand in for literals where Rust requires distinct sorts.
Additional modes run the congruence, provenance, and resugar gates and export certificates.
The hand-written programs under `tests/` join every gate, and `difftest egg` snapshots
their encodings and lifted proofs.
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


private def wrapAtRule (key : Expr) : Rule where
  query := [.expr (.app "Wrapper" [key])]
  actions := [.expr (C "Hit")]
  ruleset := ""


private def wrapHeadRule : Rule where
  query := [.expr (.app "Wrapper" [.var "x"])]
  actions := [.expr (.app "Hit" [.var "x"])]
  ruleset := ""

/-- The same query with a `union` head, so what a failure to fire costs is an *equality*
between two terms both databases hold rather than an e-node. -/
private def wrapUnionAtRule (key : Expr) : Rule where
  query := [.expr (.app "Wrapper" [key])]
  actions := [.union (.app "Wrapper" [key]) (C "Hit")]
  ruleset := ""


private def addAtRule (key : Expr) : Rule where
  query := [.expr (add (key) (.var "b"))]
  actions := [.expr (.app "Mark" [.var "b"])]
  ruleset := ""


private def nestedAtRule (key : Expr) : Rule where
  query := [.expr (.app "Wrapper" [.app "Wrapper" [key]])]
  actions := [.expr (C "Hit")]
  ruleset := ""

/-! #### A source `saturate`

The `sat-*` family. A source `Cmd.saturate` runs rounds of a ruleset until nothing changes,
and a rule of a *later* round has to see the equalities an earlier round asserted. egglog
instruments the schedule node by node — its `Run` case becomes `(seq <run> <rebuild>)` and its
`Saturate` case recurses into the loop body (`egglog/src/proofs/proof_encoding.rs:1969`,
`:1978-1980`) — so `(run-schedule (saturate R))` rebuilds after **every** iteration. `encode`
now joins the maintenance rules to `R` as well, which is the same fixpoint; before that it
emitted `[.saturate R, .saturate @rebuild]` and rebuilt once, after `R` had already settled,
so `sat-hit` lost the source's `(Hit)` outright — target `@HitView` 0 against source `Hit` 1.

`sat-hit` is that program; `sat-hit-late` puts a round of delay before the `union`, so the
rule that needs it has already sat through rounds it could not fire in. With `genProgram`'s
`genCollapseRules` tail these are the corpus's only reading of the `saturate` schedule: back
the repair out and the sweep reports 13 LOST across the 13 cases that run one. -/

/-- Round 1's rule: asserts the `union` a later round's rule needs. -/
private def unionOnAaRule : Rule where
  query := [.expr (C "Aa")]
  actions := [.union (C "Zz") (C "Aa")]
  ruleset := ""

/-- The rule that needs it. `(Wrapper (Zz))` is the only `Wrapper` the program builds, so
this matches only through the equality the rule above asserts. -/
private def wrapAaHitRule : Rule where
  query := [.expr (.app "Wrapper" [C "Aa"])]
  actions := [.expr (C "Hit")]
  ruleset := ""

/-- A round of delay: `(Kk)` builds `(Mm)`, and only then is the `union` asserted. -/
private def kkMmRule : Rule where
  query := [.expr (C "Kk")]
  actions := [.expr (C "Mm")]
  ruleset := ""

@[inherit_doc kkMmRule]
private def mmUnionRule : Rule where
  query := [.expr (C "Mm")]
  actions := [.union (C "Zz") (C "Aa")]
  ruleset := ""


private def variableFreshCase : Program :=
  [.rule (wrapAtRule (.var "x")),
   .action (.expr (C "Zz")),
   .action (.expr (.app "Wrapper" [C "Bb"])),
   .run ""]


private def variableCase : Program :=
  [.rule (wrapAtRule (.var "x")),
   .action (.expr (C "Zz")),
   .action (.expr (.app "Wrapper" [C "Aa"])),
   .action (.union (C "Zz") (C "Aa")),
   .run ""]


private def variableHeadCase : Program :=
  [.rule wrapHeadRule,
   .action (.expr (C "Zz")),
   .action (.expr (.app "Wrapper" [C "Bb"])),
   .run ""]

/-- The same with a `union` head, so what a missing firing costs is an **equality** between
two terms both databases hold — the shape `Database.UnionsJoined` is stated in. -/
private def variableEqCase : Program :=
  [.rule (wrapUnionAtRule (.var "x")),
   .action (.expr (C "Zz")),
   .action (.expr (.app "Wrapper" [C "Aa"])),
   .action (.expr (C "Hit")),
   .action (.union (C "Zz") (C "Aa")),
   .run ""]

private def curated : List (String × Program) :=
  [ ("actions",
      [.action (.expr (add (C "One") (C "Two"))),
       .action (.union (C "One") (C "One")),
       .action (.expr (add (C "Two") (C "Three"))),
       .action (.expr (.app "Wrapper" [add (C "Two") (C "Three")]))]),
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
    ("seed-2", [.rule ⟨[], [.expr (add (C "One") (C "Two"))], ""⟩, .run "", .run ""]),
    -- through congruence, the target has no row to read.
    ("ground-lost",
      [.action (.expr (C "Zz")),
       .action (.expr (.app "Wrapper" [C "Aa"])),
       .action (.union (C "Zz") (C "Aa")),
       .rule (wrapAtRule (C "Zz")), .run ""]),
    -- The same, with the `union` after a run the rule already sat through.
    ("ground-lost-after",
      [.action (.expr (C "Zz")),
       .action (.expr (.app "Wrapper" [C "Aa"])),
       .rule (wrapAtRule (C "Zz")), .run "",
       .action (.union (C "Zz") (C "Aa")), .run ""]),
    -- The head is a `union` and both its terms are built up front, so what a missing firing
    -- costs is an equality between two terms both sides hold.
    ("ground-lost-eq",
      [.action (.expr (C "Zz")),
       .action (.expr (.app "Wrapper" [C "Aa"])),
       .action (.expr (C "Hit")),
       .action (.union (C "Zz") (C "Aa")),
       .rule (wrapUnionAtRule (C "Zz")), .run ""]),
    ("ground-lost-add",
      [.action (.expr (C "Zz")),
       .action (.expr (add (C "Aa") (C "Cc"))),
       .action (.union (C "Zz") (C "Aa")),
       .rule (addAtRule (C "Zz")), .run ""]),
    ("ground-lost-nested",
      [.action (.expr (C "Zz")),
       .action (.expr (.app "Wrapper" [.app "Wrapper" [C "Aa"]])),
       .action (.union (C "Zz") (C "Aa")),
       .rule (nestedAtRule (C "Zz")), .run ""]),
    -- nullary partner because `Term.blt` compares arity first.
    ("ground-lost-app",
      [.action (.expr (add (C "Zz") (C "Cc"))),
       .action (.expr (.app "Wrapper" [C "Aa"])),
       .action (.union (add (C "Zz") (C "Cc")) (C "Aa")),
       .rule (wrapAtRule (add (C "Zz") (C "Cc"))), .run ""]),
    -- row is an extra row rather than a moved one, so the original survives.
    ("ground-keyed",
      [.action (.expr (C "Zz")),
       .action (.expr (.app "Wrapper" [C "Zz"])),
       .action (.expr (.app "Wrapper" [C "Aa"])),
       .action (.union (C "Zz") (C "Aa")),
       .rule (wrapAtRule (C "Zz")), .run ""]),
    -- rebuild's column rules carry rows in.
    ("ground-leader",
      [.action (.expr (C "Aa")),
       .action (.expr (.app "Wrapper" [C "Zz"])),
       .action (.union (C "Zz") (C "Aa")),
       .rule (wrapAtRule (C "Aa")), .run ""]),
    -- A source `saturate`: the `union` lands in round 1 and the rule that needs it fires in
    -- round 2, so the rebuild has to run *between* the rounds.
    ("sat-hit",
      [.action (.expr (.app "Wrapper" [C "Zz"])),
       .action (.expr (C "Aa")),
       .rule unionOnAaRule, .rule wrapAaHitRule, .saturate ""]),
    -- The same, with the `union` discovered a round later: `wrapAaHitRule` sits through
    -- rounds it cannot fire in before the equality it needs exists at all.
    ("sat-hit-late",
      [.action (.expr (.app "Wrapper" [C "Zz"])),
       .action (.expr (C "Aa")),
       .action (.expr (C "Kk")),
       .rule kkMmRule, .rule mmUnionRule, .rule wrapAaHitRule, .saturate ""]),
    -- The congruence has to travel up a `Wrapper` between rounds: `commuteRule` asserts the
    -- equality and `detectRule` reads it one level above. `wrapper-3` is the same program
    -- run three times.
    ("sat-wrapper",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .saturate ""]),
    -- rule was registered: `ground-lost-after`'s shape on the saturating schedule.
    ("sat-ground",
      [.action (.expr (C "Zz")),
       .action (.expr (.app "Wrapper" [C "Aa"])),
       .rule (wrapAtRule (C "Zz")),
       .action (.union (C "Zz") (C "Aa")), .saturate ""]),
    -- A `run` and a `saturate` in one program, so the maintenance rules the encoding joins
    -- to the unnamed ruleset fire in a plain round too.
    ("sat-after-run",
      [.action (.expr (add (C "One") (C "Two"))),
       .rule swapRule, .rule commuteRule, .run "", .saturate ""]),
    ("variable-fresh", variableFreshCase),
    ("variable-head", variableHeadCase),
    -- readings of the query match and only the *encoding* can lose the firing.
    ("variable", variableCase),
    -- The same with a `union` head, so what a missing firing costs is an equality between two
    -- terms both databases hold — the shape `Database.UnionsJoined` is stated in.
    ("variable-eq", variableEqCase) ]

/-! **The emitted egglog is unchanged by rulesets.** Every case here names the *unnamed*
ruleset, which a rule joins by writing no `:ruleset` and which `(run 1)` runs, so
`Cmd.toEgg` and `Rule.toEgg` render exactly what they rendered before `Rule.ruleset` and
`Cmd.run`'s argument existed, and `Program.rulesetDecls` adds no line. Pinned rather than
argued: the whole suite compares against egglog byte for byte. -/
set_option linter.hashCommand false in
#guard Program.toEgg (Program.declared
    [.action (.expr (add (C "One") (C "Two"))), .rule swapRule, .run "", .run ""])
  = "(sort Math)\n\
     (constructor One () Math)\n\
     (constructor Two () Math)\n\
     (constructor Add (Math Math) Math)\n\
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

/-- The ruleset the generated `saturate` runs, and the only named one the corpus uses.

**Named, and joined only by `genCollapseRules`.** A `Cmd.saturate` runs rounds until nothing
changes, so a ruleset holding a head that builds a deeper term than it matched has no
fixpoint and neither engine would ever return; `genRule` draws exactly such heads. The two
rules below add two nullary terms between them and nothing after that, so the ruleset they
join reaches a fixpoint whatever the seed — which is why the `saturate` runs them and not the
seed's own. -/
private def collapseRuleset : RulesetName := "collapse"

/-- Generate a terminating saturation test from the root's first argument.
The first rule unions a match with `(Sat)`; the second builds `(Hit)` using that equality
in a later round. A single variable bounds enumeration cost. Leaves return `none`. -/
private def genCollapseRules : Expr → Option (List Rule)
  | .app f (_ :: args) =>
    some [⟨[.expr (.app f (.var "a" :: args))], [.union (.var "a") (C "Sat")], collapseRuleset⟩,
          ⟨[.expr (.app f (C "Sat" :: args))], [.expr (C "Hit")], collapseRuleset⟩]
  | _ => none

private def genProgram (s : Nat) : Program :=
  let (g₁, s) := genGround 2 s
  let (g₂, s) := genGround 3 s
  let (g₃, s) := genGround 3 s
  let (r₁, s) := genRule g₂ s
  let (r₂, s) := genRule g₃ s
  let (rounds, s) := pick 3 s
  -- **Sometimes a source `saturate`**, drawn after everything else so that the rest of a
  -- seed's program is what it was. `encodeCmd` gives a `Cmd.saturate` a schedule of its own,
  -- and nothing else in the corpus but the `sat-*` cases reaches it.
  let (wantSat, s) := pick 2 s
  let sat := match wantSat, genCollapseRules g₂ with
    | 0, some rs => rs.map Cmd.rule ++ [Cmd.saturate collapseRuleset]
    | _, _ => []
  -- The model keeps rules in a `Set` and so ignores a repeat; egglog panics on one.
  -- Compare the rendered form, there being no decidable equality on `Rule`.
  let rules := if r₁.toEgg (fun _ => none) = r₂.toEgg (fun _ => none) then
      [Cmd.rule r₁] else [Cmd.rule r₁, Cmd.rule r₂]
  [.action (.expr g₁), .action (.expr g₂), .action (.expr g₃)] ++ sat ++ rules
    ++ List.replicate (rounds + 1) (Cmd.run "")

/-! ### Merge cases

Idempotent merges avoid unbounded derivations from self-collisions in the specification.
The `old-*`, `new-*`, and `canon-*` cases test noncommutative merges and resident-row
selection. Merge bodies write entries; queries read them. `min-rebuild` tests a union
of keys that makes two rows collide. See `MERGE.md` for the model's limits. -/

private def dist (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [] [.app "min" [.var "old", .var "new"]]) }

private def distMax (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [] [.app "max" [.var "old", .var "new"]]) }


/-- A block with an observable execution marker and a primitive result. -/
private def distBlock (n : Nat) (op : FnName) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [.union (C "Tick") (C "Tick")]
      [.app op [.var "old", .var "new"]]) }

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
  .action (.expr (.app f (args ++ [num v])))

/-- The binary constructor `commuteDist` matches on, as an expression: the key of a
`:merge` row is a term like any other, and these are the cases whose keys are compound. -/
private def gg (a b : Expr) : Expr := .app "G" [a, b]

/-- A rule that copies a `Dist` entry onto the commuted key, so a merge fires from a rule
head as well as from a top-level action. -/
private def commuteDist : Rule where
  query := [.expr (.app "G" [.var "a", .var "b"])]
  actions := [.expr (.app "Dist" [.var "b", .var "a", num 9])]
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
  .action (.expr (.app f (args ++ [num v, num w])))

/-- Reads a two-column row and builds a term from its *key*, gated on both value columns
being the literals written. Whether the rule fired is therefore visible in `Hit`'s row
count, which is what makes the value columns observable through `(print-size)`.

The keys are kept distinct so no merge fires on the guarded row. These cases isolate
reading two columns from collision behavior; the `tuple-read` cases below separately
check that the executable index removes superseded outputs. -/
private def readPair : Rule where
  query := [.expr (.app "Dist" [.var "k", num 3, num 4])]
  actions := [.expr (.app "Hit" [.var "k"])]
  ruleset := ""

/-! ### Reading a `:merge` function from a rule body

These cases read `Dist` through `Pattern.values` and `execM`, covering the path that
constructor-only queries do not exercise. Guarding on the returned values also detects
a merge that computes the wrong result without changing the number of rows.

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
  query := [.expr (.app "Dist" [.var "k", .var "o"])]
  actions := [.expr (.app "Hit" [.var "k"])]
  ruleset := ""

/-- The value: fires only where the recorded output is `v`. -/
private def readValue (v : Int) : Rule where
  query := [.expr (.app "Dist" [.var "k", num v])]
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
  query := [.expr (.app "Dist" [.var "k", num 5, num 1])]
  actions := [.expr (.app "Hit" [.var "k"])]
  ruleset := ""

/-- Copy one merge function's value into another's row. The read is a query fact binding
`v` and the head only writes, which is the only shape egglog accepts for a rule and the
only shape the model accepts anywhere. -/
private def copyDist : Rule where
  query := [.expr (.app "Dist" [.var "k", .var "v"])]
  actions := [.expr (.app "Copy" [.var "k", .var "v"])]
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
  query := [.expr (.app f (key ++ [num v]))]
  actions := [.expr (.app hit mark)]
  ruleset := ""

/-- `readIntoAt` marking with the key itself, which is ground, so the query costs one
substitution and no enumeration. -/
private def readInto (hit f : FnName) (key : List Expr) (v : Int) : Rule :=
  readIntoAt hit f key v key

/-- `readInto` at a multi-column output. -/
private def readIntoW (hit f : FnName) (key : List Expr) (vs : List Int) : Rule where
  query := [.expr (.app f (key ++ (vs.map num)))]
  actions := [.expr (.app hit key)]
  ruleset := ""

/-! ### Primitives outside a `:merge` body

Every primitive application in the suite used to sit inside a `:merge` body, and that was
not a choice about coverage — the emitter could not render one anywhere else. `fnArities`
declared every applied name as a constructor, so a program applying `min` in an action
emitted `(constructor min (Math Math) Math)` and egglog answered `Primitive min already
declared.` before running a line of it. None of `writeCase`'s four guards caught it, since
none of them is about the declarations.

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
    merge := some (.merge [.expr (.app "Log" [C "L", .var logged])] [.var kept]) }

/-- A merge whose body is `(union (U) (V))` — the body's entire effect is an equality, as
in a union-find's. -/
private def distUnion (n : Nat) (kept : String) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [.union (C "U") (C "V")] [.var kept]) }


private def distInlineLog (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := some (.merge [.expr (.app "Log" [C "L", .app "min" [.var "old", .var "new"]])]
                         [.app "min" [.var "old", .var "new"]]) }

/-- Seeds `W` at both operands of a body's `union`, so that `W`'s row count falls from 2 to
1 exactly when the body runs. -/
private def seedW : List Cmd :=
  [.action (.expr (.app "W" [C "U"])), .action (.expr (.app "W" [C "V"]))]

/-- A **two-column** merge with a body, for the case where a collision leaves one value
column unchanged and moves the other. The skip is all-or-nothing over the whole value
tuple, so this body must still run; a model that skipped per column would report `L 0`. -/
private def distPairLog (n : Nat) : FnDecl :=
  { arity := n, outArity := 2,
    merge := some (.merge [.expr (.app "Log" [C "L", .var "old0"])] [.var "new0", .var "new1"]) }

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
  .action (.expr (.app f (args ++ (vs.map num))))

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
    -- **The acceptance test, two columns.** egglog says `Hit 0`; an index that keeps
    -- superseded rows says `Hit 1` because the old row is still readable.
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
       .rule ⟨[.expr (C "A")], [.expr (.app "Dist" [C "A", num 9])], ""⟩,
       .rule (readValue 9), .run "", .run ""]),
    ("new-rule",
      [.decl "Dist" (distPick 1 "new"), mset "Dist" [C "A"] 4,
       .rule ⟨[.expr (C "A")], [.expr (.app "Dist" [C "A", num 9])], ""⟩,
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
       .action (.expr (.app "Dist" [C "K", .app "min" [num 5, num 3]])),
       .rule (readInto "Hit" "Dist" [C "K"] 3), .rule (readInto "Miss" "Dist" [C "K"] 5),
       .run ""]),
    -- The same with `max`, so the two markers swap: a model computing `min` for `max`
    -- is caught here even though it passes `prim-set-min`.
    ("prim-set-max",
      [.decl "Dist" (dist 1),
       .action (.expr (.app "Dist" [C "K", .app "max" [num 5, num 3]])),
       .rule (readInto "Hit" "Dist" [C "K"] 5), .rule (readInto "Miss" "Dist" [C "K"] 3),
       .run ""]),
    -- Nested: `(min (max 5 3) 4)` is `4`, so the operand list itself has to be evaluated
    -- through the argument list before the outer primitive applies. `Miss` reads `5`, the value
    -- an unevaluated inner application would have left.
    ("prim-nested",
      [.decl "Dist" (dist 1),
       .action (.expr (.app "Dist" [C "K", .app "min" [.app "max" [num 5, num 3], num 4]])),
       .rule (readInto "Hit" "Dist" [C "K"] 4), .rule (readInto "Miss" "Dist" [C "K"] 5),
       .run ""]),
    -- and avoids its "Global `g` should start with `$`" warning.
    ("prim-repeat",
      [.decl "Dist" (dist 1),
       .action (.expr (.app "min" [num 7, num 2])),
       .action (.expr (.app "Dist" [C "K", .app "min" [num 7, num 2]])),
       .rule (readInto "Hit" "Dist" [C "K"] 2), .rule (readInto "Miss" "Dist" [C "K"] 7),
       .run ""]),
    -- A primitive in a **rule head**, which is the position `Rule.noLookup` polices and so
    -- the one most likely to be rejected by mistake. Two rounds: the first fires the write,
    -- the second reads it back.
    ("prim-rule-head",
      [.decl "Dist" (dist 1), seedF,
       .rule ⟨[.expr (.app "F" [.var "a"])],
              [.expr (.app "Dist" [.var "a", .app "max" [num 5, num 3]])], ""⟩,
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
    ("merge-body-inline-set",
      [.decl "Log" logDecl, .decl "Dist" (distInlineLog 1),
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
       .action (.expr (.app "Dist" [gg (C "B") (C "A"), num 4])),
       .action (.union (C "A") (C "B")),
       .rule (readIntoAt "Hit" "Dist" [gg (C "A") (C "B")] 4 [C "A"]),
       .rule (readIntoAt "Miss" "Dist" [gg (C "C") (C "A")] 4 [C "A"]), .run ""]),
    -- The same one level deeper, so the congruence has to be rebuilt at an *inner* node
    -- before the outer one can match. `Miss` moves the outer argument instead of the inner
    -- one — `(A)` for `(C)`, which no `union` relates — so it must not fire.
    ("read-unbuilt-key-deep",
      [.decl "Dist" (dist 1),
       .action (.expr (.app "Dist" [gg (gg (C "B") (C "A")) (C "C"), num 4])),
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
       .action (.expr (.app "Dist" [gg (C "B") (C "A"), num 4])),
       .action (.union (C "A") (C "B")),
       .rule (readIntoAt "Hit" "Dist" [gg (C "A") (C "B")] 4 [C "A"]),
       .rule (readIntoAt "Miss" "Dist" [gg (.app "H" [C "A"]) (C "B")] 4 [C "A"]),
       .run ""]) ]


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


private def genMergeSpec (w : Nat) (s : Nat) : MergeSpec × Nat :=
  let (res, s) := genCombiners w w s
  let (logged, s) := genCombiner w 0 s
  let (shape, s) := pick 8 s
  match shape with
  | 4 => (.merge [.union (C "U") (C "U")] (logged :: res.tail), s)
  | 5 => (.merge [.expr (.app "Log" [C "L", logged])] res, s)
  | 6 => (.merge [.union (C "U") (C "V")] res, s)
  | 7 => (.merge [.expr (.app "Log" [C "L", logged])]
            (logged :: res.tail), s)
  | _ => (.merge [] res, s)

/-- Whether a drawn body writes the side table, which the program then has to declare —
`writeCase`'s `illegalSets` guard is what an omission would trip. -/
private def specSetsLog (m : MergeSpec) : Bool := m.fnArities.any (fun fa => fa.1 == "Log")

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
  (⟨[.expr p], [.expr (.app "Dist" (ks ++ (vs.map Prod.fst)))], ""⟩, s)

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
  query := [.expr (.app "Dist" (key ++ (vals.map num)))]
  actions := [.expr (.app "Won" key)]
  ruleset := ""

/-- A rule *reading* `Dist` from its body: a `Pattern.values` atom whose value column is
either a fresh variable (existence) or the literal the program wrote (the value). Its head
builds a `Hit`, so whether and how often it fired is visible in `(print-size)`.

This exercises reads of merge outputs, which constructor-only queries do not cover.

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
  (⟨[.expr p, .expr (.app "Dist" (ks ++ cols))], [.expr (.app "Hit" [p])], ""⟩, s)

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
         .action (.expr (.app "Dist" (k₁ ++ (v₁.map Prod.fst)))),
         .action (.expr (.app "Dist" (k₂ ++ (v₂.map Prod.fst)))),
         .action (.expr (.app "Dist" (k₃ ++ (v₃.map Prod.fst)))) ]
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
#guard curated.length = 27
set_option linter.hashCommand false in
#guard curatedMerge.length = 66
set_option linter.hashCommand false in
#guard allCases.length = 183

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

/-! **The literal probes are model-only.** Every case in the corpus proper uses nullary
constructors, because egglog's `i64` is a distinct primitive sort and `(Add 1 2)` would not
typecheck there, while `Term.lit` shares a sort with applications here. These two are the
only way to ask what `ViewRepr`'s literal clause does when a literal is a *source* term — a
literal in a key column, which is the only place a source literal can be — so they live among
the probes, which `writeCase` never sees. -/

/-- A literal the encoding also mints (`unitE` is `0`) is absent from this source. -/
private def litCase : Program := [.action (.expr (add (.lit (.int 1)) (.lit (.int 2))))]

/-- The same, with `0` among the source's own literals. -/
private def litZeroCase : Program := [.action (.expr (add (.lit (.int 0)) (.lit (.int 1))))]

/-! ### The union-find probes

`CorrReport.viaUF` counts the pairs the sweep joins whose two terms share no e-class
outright, so that the join had to go through a `@UF` edge. It is the number that says
whether a `UFLeader` walk carries any weight, and it is zero on every case in the corpus —
which is why `Encode.lean`'s `SameClass` is the **flat** relation, one id both terms read
to, with the walk kept here as a control rather than in the definition.

These are the programs written to make it non-zero: a three-link chain built in each
direction, endpoints at different term depths, a congruence that has to climb three levels,
a leader that `ordering-min` puts *below* its class, unions a rule makes across rounds, and
a `union` between two terms neither of which has a view entry.

They are probes rather than corpus cases because the literal family is model-only —
egglog's `i64` is a distinct sort where `Term.lit` shares one with applications — and
because the constructor-only ones answer a question the congruence gate asks and
`scripts/difftest.sh` does not.
-/

/-- `Wrapper` applied `n` times. -/
private def wrap : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => .app "Wrapper" [wrap n e]

/-- A three-link union chain under two wrappers, with **no** `run`: the only rebuild is the
one `encodeCmd` appends to each action. `Term.blt` orders nullary constructors by name, so
`A` is the leader and the edges the `union`s write are `D → C`, `C → B`, `B → A` — each
landing above the standing leader, which is the order that makes the walk longest. -/
private def chainCase : Program :=
  [.action (.expr (.app "Wrapper" [C "A"])),
   .action (.expr (.app "Wrapper" [C "D"])),
   .action (.union (C "C") (C "D")),
   .action (.union (C "B") (C "C")),
   .action (.union (C "A") (C "B"))]

/-- The same chain in the opposite order, so each `union` lands below the standing leader
and every edge already recorded has to be re-pointed. -/
private def chainDownCase : Program :=
  [.action (.expr (.app "Wrapper" [C "A"])),
   .action (.expr (.app "Wrapper" [C "D"])),
   .action (.union (C "A") (C "B")),
   .action (.union (C "B") (C "C")),
   .action (.union (C "C") (C "D"))]

/-- Endpoints at different term depths: a leaf `union`ed with a one-level application, both
ways round, so the column re-keying and the leader walk interleave. A nullary constructor
sorts below a unary application in `Term.blt`, so the leaf is the leader both times and the
application's own view is what moves. -/
private def depthCase : Program :=
  [.action (.expr (wrap 2 (C "A"))),
   .action (.expr (wrap 2 (C "B"))),
   .action (.union (C "A") (.app "Wrapper" [C "B"])),
   .action (.union (C "B") (.app "Wrapper" [C "A"]))]

/-- A three-level tower over a `union`ed leaf. Each level's views collide only once the
level below has been re-keyed, so the merge writes `@UF` edges in later rebuild rounds than
the `union` did: new edges arriving after the earlier ones were compressed, made by the
maintenance rules rather than by a source rule. -/
private def towerCase : Program :=
  [.action (.expr (wrap 3 (C "A"))),
   .action (.expr (wrap 3 (C "B"))),
   .action (.union (C "A") (C "B"))]

/-- A `union` whose leader is the *deeper* term: `Term.blt` compares argument count first,
so `(Wrapper Z)` sorts below `(Add A B)` and `ordering-min` puts the leader one level down.
The second `union` then moves the leader's own child. -/
private def orderCase : Program :=
  [.action (.expr (.app "Wrapper" [C "Z"])),
   .action (.expr (add (C "A") (C "B"))),
   .action (.union (.app "Wrapper" [C "Z"]) (add (C "A") (C "B"))),
   .action (.union (C "Z") (C "A"))]

/-- `(Wrapper (Add a b)) = (Wrapper (One))` off a commuted `Add`: the premise holds only
after `commuteRule` has fired, so this `union`'s `@UF` edge lands a round later, on a
union-find the previous round's rebuild already compressed. -/
private def liftRule : Rule where
  query := [.eq (add (.var "a") (.var "b")) (add (.var "b") (.var "a"))]
  actions := [.union (.app "Wrapper" [add (.var "a") (.var "b")])
                     (.app "Wrapper" [C "One"])]
  ruleset := ""

/-- `liftRule` over a wrapped `Add`, run twice. -/
private def roundCase : Program :=
  [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
   .action (.expr (.app "Wrapper" [C "One"])),
   .rule commuteRule, .rule liftRule, .run "", .run ""]

/-- `unionCase` with literals in place of the nullary constructors, which would be the one
shape whose `SameClass` the views cannot decide: `encodeBuild` emits no action for a
literal, so neither `1` nor `2` has a view entry for the rebuild to re-key and the `@UF`
edge would be the only record of their equality.

**It is not a program.** `execAction` refuses a `union` with a literal operand, so the
source run sticks at the third command and `Cong src` never relates a literal to anything
but itself. This probe is that refusal, run. -/
private def litUnionCase : Program :=
  [.action (.expr (add (.lit (.int 1)) (.lit (.int 2)))),
   .action (.expr (add (.lit (.int 2)) (.lit (.int 1)))),
   .action (.union (.lit (.int 1)) (.lit (.int 2)))]

/-- One literal operand is refused too, not just two, which is what keeps every `@UF` key
an application. -/
private def litMixCase : Program :=
  [.action (.expr (add (.lit (.int 1)) (C "One"))),
   .action (.union (.lit (.int 1)) (add (.lit (.int 1)) (C "One")))]

/-- The probes, reachable from `difftest encode <fuel> <name>` by name. The `-run` variants
append one empty round, which is what makes `encode` emit a `Cmd.saturate rebuildRuleset` and
so the only way to ask whether the rebuild repairs the gap `upCase` shows. They are out of
the guards because running a rebuild is far too slow to sit in a build. -/
private def probeCases : List (String × Program) :=
  [("build", buildCase), ("union", unionCase),
   ("up", upCase), ("up-run", upCase ++ [.run ""]),
   ("up-thin", upThinCase), ("up-thin-run", upThinCase ++ [.run ""]),
   ("lit", litCase), ("lit-zero", litZeroCase),
   ("chain", chainCase), ("chain-run", chainCase ++ [.run ""]),
   ("chain-down", chainDownCase), ("depth", depthCase),
   ("tower", towerCase), ("order", orderCase), ("round", roundCase),
   ("lit-union", litUnionCase), ("lit-mix", litMixCase)]

namespace Egglog
/-! ### The correspondence domain, decided

`Program.EncodeDomain` as a `Bool`, with the equivalence proved, so that the corpus gates
and the hypothesis the theorem carries cannot drift apart. -/
/-- `Cmd.CtorDecl`, computed: `EncodeDomain.ctorsOnly` at one command. -/
def Cmd.ctorDeclB : Cmd → Bool
  | .decl _ d => d.merge.isNone
  | _ => true

theorem Cmd.ctorDeclB_iff (c : Cmd) : c.ctorDeclB = true ↔ c.CtorDecl := by
  cases c <;> simp [Cmd.ctorDeclB, Cmd.CtorDecl, Option.isNone_iff_eq_none]

/-- `Pattern.Scoped`, computed: a fact is an application. -/
def Pattern.scopedB : Pattern → Bool
  | .expr (.app _ _) => true
  | .expr _ => false
  | .eq _ _ => true

theorem Pattern.scopedB_iff (p : Pattern) : p.scopedB = true ↔ p.Scoped := by
  cases p with
  | expr e => cases e <;> simp [Pattern.scopedB, Pattern.Scoped, Expr.IsApp]
  | eq _ _ => simp [Pattern.scopedB, Pattern.Scoped]

/-- A bare literal, computed. -/
def Expr.isLitB : Expr → Bool
  | .lit _ => true
  | _ => false

theorem Expr.isLitB_eq_false_iff (e : Expr) : e.isLitB = false ↔ ∀ l, e ≠ .lit l := by
  cases e <;> simp [Expr.isLitB]

/-- `Pattern.Grounded`, computed. -/
def Pattern.groundedB : Pattern → Bool
  | .expr e => !e.isLitB
  | .eq e₁ e₂ => !e₁.isLitB || !e₂.isLitB

theorem Pattern.groundedB_iff (p : Pattern) : p.groundedB = true ↔ p.Grounded := by
  cases p <;>
    simp [Pattern.groundedB, Pattern.Grounded, ← Expr.isLitB_eq_false_iff]

/-- `Expr.var v ∈ args`, computed: `Expr` carries no `BEq`. -/
def Expr.memVarB (v : Var) : List Expr → Bool
  | [] => false
  | .var w :: es => w == v || Expr.memVarB v es
  | _ :: es => Expr.memVarB v es

theorem Expr.memVarB_iff (v : Var) : ∀ args : List Expr,
    Expr.memVarB v args = true ↔ Expr.var v ∈ args
  | [] => by simp [Expr.memVarB]
  | .lit _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es
  | .var w :: es => by
      simp only [Expr.memVarB, Bool.or_eq_true, beq_iff_eq, List.mem_cons, Expr.var.injEq,
        Expr.memVarB_iff v es]
      exact or_congr_left eq_comm
  | .app _ _ :: es => by simpa [Expr.memVarB] using Expr.memVarB_iff v es

mutual

/-- `Expr.ArgVar`, computed. -/
def Expr.argVarB (v : Var) : Expr → Bool
  | .lit _ => false
  | .var _ => false
  | .app _ args => Expr.memVarB v args || Expr.argVarListB v args

/-- `Expr.ArgVarList`, computed. -/
def Expr.argVarListB (v : Var) : List Expr → Bool
  | [] => false
  | e :: es => Expr.argVarB v e || Expr.argVarListB v es

end

mutual

theorem Expr.argVarB_iff (v : Var) : ∀ e : Expr, Expr.argVarB v e = true ↔ Expr.ArgVar v e
  | .lit _ => by simp [Expr.argVarB, Expr.ArgVar]
  | .var _ => by simp [Expr.argVarB, Expr.ArgVar]
  | .app _ args => by
      simp only [Expr.argVarB, Expr.ArgVar, Bool.or_eq_true, Expr.memVarB_iff,
        Expr.argVarListB_iff v args]

theorem Expr.argVarListB_iff (v : Var) : ∀ es : List Expr,
    Expr.argVarListB v es = true ↔ Expr.ArgVarList v es
  | [] => by simp [Expr.argVarListB, Expr.ArgVarList]
  | e :: es => by
      simp only [Expr.argVarListB, Expr.ArgVarList, Bool.or_eq_true, Expr.argVarB_iff v e,
        Expr.argVarListB_iff v es]

end

/-- `Pattern.ArgVar`, computed. -/
def Pattern.argVarB (v : Var) : Pattern → Bool
  | .expr e => e.argVarB v
  | .eq e₁ e₂ => e₁.argVarB v || e₂.argVarB v

theorem Pattern.argVarB_iff (v : Var) (p : Pattern) :
    p.argVarB v = true ↔ Pattern.ArgVar v p := by
  cases p <;>
    simp [Pattern.argVarB, Pattern.ArgVar, Expr.argVarB_iff, Expr.argVarListB_iff]

/-- `Query.VarsKeyed`, computed. -/
def Query.varsKeyedB (q : Query) : Bool :=
  (Query.vars q).all fun v => q.any fun p => Pattern.argVarB v p

theorem Query.varsKeyedB_iff (q : Query) : q.varsKeyedB = true ↔ Query.VarsKeyed q := by
  simp [Query.varsKeyedB, Query.VarsKeyed, List.all_eq_true, List.any_eq_true,
    Pattern.argVarB_iff]

/-- `Cmd.QueryEncodable`, computed. -/
def Cmd.queryEncodableB : Cmd → Bool
  | .rule r =>
      r.query.all (fun p => p.groundedB && p.scopedB) && Query.varsKeyedB r.query
  | _ => true

theorem Cmd.queryEncodableB_iff (c : Cmd) : c.queryEncodableB = true ↔ c.QueryEncodable := by
  cases c <;>
    simp [Cmd.queryEncodableB, Cmd.QueryEncodable, List.all_eq_true, Pattern.groundedB_iff,
      Pattern.scopedB_iff, Query.varsKeyedB_iff]

/-- `Program.EncodeDomain`, computed. `EncodeDomain.setLegal`, `EncodeDomain.headsDeclared`
and `EncodeDomain.headsScoped` are `Spec/Scope.lean` checks with `Decidable` instances, so
those three conjuncts are `decide` of the clause itself; `EncodeDomain.noLitUnion` is `Bool`
at the source. -/
def Program.encodeDomainB (p : Program) : Bool :=
  p.all Cmd.ctorDeclB && decide (Program.SetLegal p (fun _ => none))
    && p.ctors.all (fun fk => (Prim.ofName fk.1).isNone)
    && p.names.all (fun n => !"@".isPrefixOf n)
    && p.all Cmd.queryEncodableB
    && (p.all Cmd.ruleUnionFreeB || p.all Cmd.litFreeB)
    && decide (Program.HeadsDeclared p (fun _ => none))
    && p.arityConflicts.isEmpty
    && decide p.HeadsScoped

/-- **The census below counts exactly `EncodeDomain`.** -/
theorem Program.encodeDomainB_iff (p : Program) :
    p.encodeDomainB = true ↔ p.EncodeDomain := by
  simp only [Program.encodeDomainB, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    Cmd.ctorDeclB_iff, Cmd.queryEncodableB_iff, Option.isNone_iff_eq_none,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.eq_false_iff, ne_eq, decide_eq_true_eq,
    List.isEmpty_iff]
  exact ⟨fun h => ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2,
      h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩,
    fun h => ⟨⟨⟨⟨⟨⟨⟨⟨h.ctorsOnly, h.setLegal⟩, h.noPrim⟩, h.noAt⟩, h.queryEncodable⟩,
      h.noLitUnion⟩, h.headsDeclared⟩, h.aritiesAgree⟩, h.headsScoped⟩⟩

/-! #### Running the compiled program

`Congruence.encode` emits `Cmd.saturate rebuildRuleset` after every run, so a compiled program is
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

end Egglog

/-! ### Entry point -/


private def writeCase (dir name : String) (p₀ : Program) : IO Unit := do
  let p := p₀.declared
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

/-! ### Egg files

Hand-written programs under `tests/`, in egglog syntax. Each is a corpus case for every
gate, and `difftest egg` snapshots its congruence encoding, its provenance encoding, and
its lifted source proofs next to it. -/

private def eggDir : System.FilePath := "tests"

private def eggSnapshots : List String := ["congruence.egg", "provenance.egg", "proofs.txt"]

/-- The `.egg` programs under `tests/`, by file stem, in name order. -/
private def fileCases : IO (List (String × Program)) := do
  if !(← eggDir.pathExists) then return []
  let entries ← eggDir.readDir
  let stems := entries.filterMap fun e =>
    let name := e.fileName
    if name.endsWith ".egg" && !(eggSnapshots.any fun s => name.endsWith ("." ++ s)) then
      some (String.ofList (name.toList.take (name.length - 4)))
    else none
  (stems.qsort (fun a b => decide (a < b))).toList.mapM fun stem => do
    let src ← IO.FS.readFile (eggDir / s!"{stem}.egg")
    match Program.ofEgg src with
    | .ok p => pure (stem, p)
    | .error e => throw (IO.userError s!"tests/{stem}.egg: {e}")

/-- Run the target with structural equality and the corpus's saturation fuel. -/
private def relationalExecAt (fuel : Nat) (d : FDatabase) : Program → Option FDatabase
  | [] => some d
  | .saturate R :: cs => (Relational.runSaturate R fuel d).bind fun e => relationalExecAt fuel e cs
  | c :: cs => (Relational.execCmd d c).bind fun e => relationalExecAt fuel e cs

/-- Compare the compiled program's reading of every pair of source terms against source
congruence, and its execution with and without equality reasoning. -/
private def congruenceCheck (fuel : Nat) (p : Program) : List String := Id.run do
  let compiled := Congruence.compile p
  let q : Program := compiled.map Congruence.Command.command
  let mut errors : List String := []
  if !q.arityErrors.isEmpty then errors := errors ++ ["invalid target column counts"]
  if !q.illegalReads.isEmpty then errors := errors ++ ["illegal target function lookup"]
  if !q.arityConflicts.isEmpty then errors := errors ++ ["conflicting target arities"]
  -- Every emitted rule has an origin; no non-rule carries a rule origin.
  if !(compiled.all fun c => match c.command, c.ruleOrigin with
      | .rule _, some _ => true
      | .rule _, none => false
      | _, none => true
      | _, some _ => false) then errors := errors ++ ["missing or misplaced rule origin"]
  match execAt fuel FDatabase.empty p, execAt fuel FDatabase.empty q with
  | some src, some tgt =>
    match relationalExecAt fuel FDatabase.empty q with
    | none => errors := errors ++ ["relational target stuck or exhausted fuel"]
    | some plain =>
      if !plain.sameData tgt then
        errors := errors ++ ["target depends on implicit equality reasoning"]
    if !tgt.eqsReflB || !tgt.subtermClosedB then
      errors := errors ++ ["target violates reader assumptions"]
    let cl := src.closureF
    let readings := src.terms.map fun t => (t, Congruence.viewReprsF tgt t)
    if readings.any (fun (a, ids) => readings.any fun (b, js) =>
        decide ((a, b) ∈ cl) != ids.any js.contains) then
      errors := errors ++ ["source equality mismatch"]
  | none, _ => errors := errors ++ ["source stuck or exhausted fuel"]
  | _, none => errors := errors ++ ["congruence target stuck or exhausted fuel"]
  return errors

private def runCongruenceChecks (fuel : Nat) (names : List String) : IO UInt32 := do
  let files ← fileCases
  let available := allCases ++ files ++ probeCases
  let unknown := names.filter fun name => !(available.any fun c => c.1 == name)
  unless unknown.isEmpty do
    IO.eprintln s!"unknown cases: {String.intercalate ", " unknown}"
    return 1
  let cases := if names.isEmpty then allCases ++ files else available.filter fun c => names.contains c.1
  let mut tested := 0
  let mut failed := 0
  let mut skipped := 0
  for (name, p₀) in cases do
    let p := p₀.declared
    if !p.encodeDomainB then
      skipped := skipped + 1
      continue
    tested := tested + 1
    let errors := congruenceCheck fuel p
    unless errors.isEmpty do
      failed := failed + 1
      IO.println s!"FAIL {name}: {String.intercalate "; " errors}"
  IO.println s!"congruence: {tested} tested, {failed} failures, {skipped} outside domain"
  return if failed == 0 && tested > 0 then 0 else 1

private def provenanceCheck (fuel : Nat) (p : Program) (liftProofs : Bool) : List String := Id.run do
  let q := Congruence.encode p
  let some C := SourceProof.contextOf q | return ["invalid congruence program"]
  let some encoded := Provenance.encode q | return ["provenance pass rejected input"]
  let some original := relationalExecAt fuel FDatabase.empty q |
    return ["congruence program stuck or exhausted fuel"]
  let some annotated := relationalExecAt fuel FDatabase.empty encoded |
    return ["instrumented program stuck or exhausted fuel"]
  let mut errors : List String := []
  if !Provenance.unionFree encoded then errors := errors ++ ["provenance introduced union"]
  let rows := annotated.rows.filterMap (Provenance.eraseRow C.sig)
  if rows.toFinset != original.rows.toFinset then
    errors := errors ++ ["projected live rows differ"]
  let terms := annotated.terms.filterMap (Provenance.eraseFact C.sig)
  if terms.toFinset != original.terms.toFinset then
    errors := errors ++ ["projected retained facts differ"]
  let proofs := Provenance.retainedRows C.sig annotated.terms
  let bad := proofs.filter fun r =>
    if liftProofs then (Resugar.extractRow p r).isNone else (Provenance.extractRow q r).isNone
  if !bad.isEmpty then
    errors := errors ++ [s!"{bad.length}/{proofs.length} retained proofs failed"]
  return errors

private def runProvenanceChecks (fuel : Nat) (names : List String)
    (liftProofs : Bool := false) : IO UInt32 := do
  let files ← fileCases
  let available := allCases ++ files ++ probeCases
  let unknown := names.filter fun name => !(available.any fun c => c.1 == name)
  unless unknown.isEmpty do
    IO.eprintln s!"unknown cases: {String.intercalate ", " unknown}"
    return 1
  let cases := if names.isEmpty then allCases ++ files else available.filter fun c => names.contains c.1
  let mut tested := 0
  let mut failed := 0
  let mut skipped := 0
  for (name, p₀) in cases do
    let p := p₀.declared
    if !p.encodeDomainB then
      skipped := skipped + 1
      continue
    tested := tested + 1
    let errors := provenanceCheck fuel p liftProofs
    unless errors.isEmpty do
      failed := failed + 1
      IO.println s!"FAIL {name}: {String.intercalate "; " errors}"
  let label := if liftProofs then "resugar" else "provenance"
  IO.println s!"{label}: {tested} tested, {failed} failures, {skipped} outside domain"
  return if failed == 0 && tested > 0 then 0 else 1

private def firstDifference (expected actual : String) : String :=
  let es := expected.splitOn "\n"
  let as := actual.splitOn "\n"
  match (List.range (max es.length as.length)).find? fun i => es[i]? != as[i]? with
  | some i =>
    s!"line {i + 1}: expected `{(es[i]?).getD "<end>"}`, got `{(as[i]?).getD "<end>"}`"
  | none => "identical"

/-- Check the parser against the emitter on the whole corpus. -/
private def parseRoundTrip : List String :=
  allCases.filterMap fun c =>
    let src := c.2.declared.toEgg
    match Program.ofEgg src with
    | .ok p => if p.toEgg == src then none else some c.1
    | .error e => some s!"{c.1} ({e})"

/-- Snapshot the encodings and lifted proofs of every program under `tests/`, or rewrite
the snapshots when `update` is set, and run the corpus gates on each. -/
private def runEggChecks (fuel : Nat) (update : Bool) (names : List String) : IO UInt32 := do
  let files ← fileCases
  let unknown := names.filter fun name => !(files.any fun c => c.1 == name)
  unless unknown.isEmpty do
    IO.eprintln s!"unknown cases: {String.intercalate ", " unknown}"
    return 1
  let selected := if names.isEmpty then files else files.filter fun c => names.contains c.1
  let mut failed := 0
  unless parseRoundTrip.isEmpty do
    failed := failed + 1
    IO.println s!"FAIL parse round trip: {String.intercalate ", " parseRoundTrip}"
  for (name, p) in selected do
    let mut errors : List String := []
    if !p.encodeDomainB then errors := ["outside the correspondence domain"]
    else
      let congruence := Congruence.encode p
      let snapshots : List (String × Option String) :=
        [("congruence.egg", some congruence.render),
         ("provenance.egg", (Provenance.encode congruence).map Program.render),
         ("proofs.txt", (Resugar.certificates (relationalExecAt fuel FDatabase.empty) p).map
           Resugar.renderProofs)]
      for (suffix, text) in snapshots do
        let path := eggDir / s!"{name}.{suffix}"
        match text with
        | none => errors := errors ++ [s!"{suffix} not produced"]
        | some text =>
          if update then IO.FS.writeFile path text
          else if !(← path.pathExists) then errors := errors ++ [s!"{suffix} missing"]
          else
            let expected ← IO.FS.readFile path
            if expected != text then
              errors := errors ++ [s!"{suffix} differs, {firstDifference expected text}"]
      errors := errors ++ congruenceCheck fuel p ++ provenanceCheck fuel p false ++
        (provenanceCheck fuel p true).map ("lifting: " ++ ·)
    unless errors.isEmpty do
      failed := failed + 1
      IO.println s!"FAIL {name}: {String.intercalate "; " errors}"
  IO.println s!"egg: {selected.length} tested, {failed} failures"
  return if failed == 0 && selected.length > 0 then 0 else 1

/-- Write the curated fixtures and every in-domain case's lifted certificates as one JSON
array, for `egglog/tests/lean_certificates.rs`. The fixtures alone go to `path` when
`fixturesOnly` is set. -/
private def exportCertificates (fuel : Nat) (path : String) (names : List String)
    (fixturesOnly : Bool) : IO UInt32 := do
  let some fixtures := Resugar.Export.fixtures |
    IO.eprintln "difftest: a fixture program does not lift"; return 1
  let mut cases := fixtures
  unless fixturesOnly do
    let files ← fileCases
    let available := allCases ++ files ++ probeCases
    let unknown := names.filter fun name => !(available.any fun c => c.1 == name)
    unless unknown.isEmpty do
      IO.eprintln s!"unknown cases: {String.intercalate ", " unknown}"
      return 1
    let selected := if names.isEmpty then allCases ++ files else available.filter fun c => names.contains c.1
    for (name, p₀) in selected do
      let p := p₀.declared
      if !p.encodeDomainB then continue
      let some cs := Resugar.certificates (relationalExecAt fuel FDatabase.empty) p |
        IO.eprintln s!"difftest: {name} does not lift"; return 1
      let some json := Resugar.Export.caseJson name p cs |
        IO.eprintln s!"difftest: {name} is outside the source checker's fragment"; return 1
      cases := cases ++ [json]
  let json := Lean.Json.arr cases.toArray
  IO.FS.writeFile path ((if fixturesOnly then json.pretty else json.compress) ++ "\n")
  IO.println s!"wrote {cases.length} cases to {path}"
  return 0

/-- `difftest <dir> curated` writes the curated cases, `difftest <dir> merge` the curated
`:merge` ones; `difftest <dir> seed <n>` writes one random constructor case named
`rand-<n>` and `difftest <dir> mergeseed <n>` one random `:merge` case named `mrand-<n>`.
The two random families are named apart so the script can report a profile distribution
for each — a collapsing distribution is how a generator that has stopped exercising
anything shows up, and a single pooled number would hide it.

`difftest encode-domain` prints how much of the corpus the correspondence domain covers.
`difftest congruence`, `provenance` and `resugar` run the corpus gates at a saturation fuel,
`egg` checks the snapshots under `tests/`, and `export-fixtures` and `export-certificates`
write source certificates for Rust egglog.
These write nothing and never invoke egglog; the comparison is between the model and
itself. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "resugar" :: fuel :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n => runProvenanceChecks n names true
  | ["export-fixtures", path] => exportCertificates 0 path [] true
  | "export-certificates" :: fuel :: path :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n => exportCertificates n path names false
  | "provenance" :: fuel :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n => runProvenanceChecks n names
  | "egg" :: fuel :: rest =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n =>
      match rest with
      | "update" :: names => runEggChecks n true names
      | names => runEggChecks n false names
  | "congruence" :: fuel :: names =>
    match fuel.toNat? with
    | none => IO.eprintln s!"difftest: bad fuel {fuel}"; return 1
    | some n => runCongruenceChecks n names
  | ["encode-domain"] =>
    let inDom := allCases.filter fun c => (c.2.declared).encodeDomainB
    IO.println s!"{inDom.length} of {allCases.length} cases are in encode's domain"
    IO.println (String.intercalate " " (inDom.map Prod.fst))
    return 0
  | [dir, "curated"] =>
    IO.FS.createDirAll dir
    let files ← fileCases
    for (name, p) in curated ++ files do writeCase dir name p
    IO.println s!"wrote {curated.length + files.length} curated cases"
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
    IO.eprintln "       difftest encode-domain"
    IO.eprintln "       difftest congruence <fuel> [case…]"
    IO.eprintln "       difftest provenance <fuel> [case…]"
    IO.eprintln "       difftest resugar <fuel> [case…]"
    IO.eprintln "       difftest egg <fuel> [update] [case…]"
    IO.eprintln "       difftest export-fixtures <path>"
    IO.eprintln "       difftest export-certificates <fuel> <path> [case…]"
    return 1
