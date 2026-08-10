import EgglogSemantics.Impl.Check
import EgglogSemantics.Proofs.Interp

/-!
# Worked examples, as Lean proofs

One small example per notion the semantics defines — scope, congruence, e-matching,
running actions, running a rule — meant to be read as documentation. Each `example` is a
closed proof, so this file compiling *is* the test run; the `#guard`s at the end run
whole programs through the interpreter instead.

Every hand-built database below holds the terms its equalities mention. A state with
equalities but no terms is unreachable — a `union` always inserts its operands — so
there is nothing to check about one.

Checks about what a `run` does *not* produce need `ValidSubst` inversion, which is
`PLAN.md`'s M8; the `run` example below is the forward direction only. Randomly
generated programs, checked against the real egglog binary, are `DiffTest.lean`.
-/

namespace Egglog.Examples

/-- An integer term. -/
private def num (n : Int) : Term := .lit (.int n)

/-- An integer expression. -/
private def eNum (n : Int) : Expr := .lit (.int n)

/-- The empty signature. -/
private abbrev noSig : Signature := fun _ => none

/-- `(datatype S (c x…))` at `n` argument columns.

Declaration is required, so every program below that *builds* a term declares its
constructors first, and every hand-built database declares the ones its terms use. -/
private def ctorDecl (n : Nat) : FnDecl := { arity := n, outArity := 1, merge := none }

/-! ### Scope checking -/

/-- A bare `v1` as the whole program: nothing binds it, and an action must be an
application besides. -/
example : ¬ WellScoped [.action (.expr (.var "v1"))] := by
  simp [WellScoped, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped]

/-- `(let v1 2)` then `(cwrap v1)`: a top-level `let` is in scope for a later command. -/
example : WellScoped
    [.action (.letBind "v1" (eNum 2)), .action (.expr (.app "cwrap" [.var "v1"]))] := by
  simp [WellScoped, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped, Expr.IsApp,
    Cmd.bind, Action.bind, eNum]

/-- The same program with a bare `v1` as the second action is rejected. `v1` is in scope,
but egglog has no such action — `parse error: expected command` at top level and
`parse error: expected action` in a rule head — so `Action.Scoped` requires an
application. -/
example : ¬ WellScoped [.action (.letBind "v1" (eNum 2)), .action (.expr (.var "v1"))] := by
  simp [WellScoped, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.IsApp]

/-- Likewise for a query fact, where egglog answers `parse error: expected fact`. -/
example : ¬ Rule.Scoped ⟨[.expr (.var "a")], []⟩ [] := by
  simp [Rule.Scoped, Pattern.Scoped, Expr.IsApp]

/-- `(rule ((= v1 2)) ((cadd v1 v2)))` with no globals: `v2` is bound by neither the
query nor the globals. -/
example : ¬ Rule.Scoped
    ⟨[.eq (.var "v1") (eNum 2)], [.expr (.app "cadd" [.var "v1", .var "v2"])]⟩ [] := by
  simp [Rule.Scoped, Pattern.Scoped, Actions.Scoped, Action.Scoped, Expr.Scoped,
    Expr.IsApp, Query.bind, Pattern.vars, eNum]

/-- The same rule with `v2` a global: it does scope. -/
example : Rule.Scoped
    ⟨[.eq (.var "v1") (eNum 2)], [.expr (.app "cadd" [.var "v1", .var "v2"])]⟩ ["v2"] := by
  simp [Rule.Scoped, Pattern.Scoped, Actions.Scoped, Action.Scoped, Expr.Scoped,
    Expr.IsApp, Query.bind, Pattern.vars, eNum]

/-! ### Evaluability

Scope and evaluability are separate judgments, and `(min 1 2)` is what separates them:
a legal egglog action, well-scoped here, and not `Evaluable`, because this model has no
sorts and so cannot tell it from the type error `(min (A) (B))`. -/

private def minProgram : Program := [.action (.expr (.app "min" [eNum 1, eNum 2]))]

example : WellScoped minProgram := by
  simp [WellScoped, minProgram, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped,
    Expr.IsApp, eNum]

example : ¬ Program.Evaluable minProgram noSig := by
  simp [minProgram, Program.Evaluable, Cmd.Evaluable, Action.Evaluable, Expr.Evaluable,
    Expr.fns, Expr.fnsList, Prim.ofName, eNum]

/-! ### Congruence

`1 = 2` and `2 = 3` over `{1, 2, 3}` puts all three terms in one class — all nine
pairs. -/

/-- `1 = 2` and `2 = 3` asserted over `{1, 2, 3}`. -/
private def chain : Database where
  sig := noSig
  terms := {num 1, num 2, num 3}
  rows := Database.ctorRowsOf {num 1, num 2, num 3}
  eqs := {(num 1, num 2), (num 2, num 3)}
  env := []
  rules := ∅

private theorem chain_wf : chain.WF where
  subtermClosed := by
    intro t ht
    simp only [chain, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl <;> simp [chain, num]
  eqsInTerms := by
    intro p hp
    simp only [chain, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> simp [chain]
  envInTerms := by simp [chain]

example : Cong chain (num 1) (num 3) :=
  .trans (b := num 2) (.assert (by simp [chain])) (.assert (by simp [chain]))

example : Cong chain (num 3) (num 1) :=
  .symm (.trans (b := num 2) (.assert (by simp [chain])) (.assert (by simp [chain])))

example : Cong chain (num 2) (num 2) := .refl (by simp [chain])

/-- The closure relates nothing to a term the database does not hold, which follows
from reflexivity being restricted to `db.terms`. -/
example : ¬ Cong chain (num 1) (num 4) := by
  intro h
  have hm : num 4 ∈ chain.terms := h.mem_right chain_wf
  simp [chain, num] at hm

/-- `1 = 2` over `{1, 2, (wrapper 1), (wrapper 2)}` derives `(wrapper 1) = (wrapper 2)`:
congruence propagating under `wrapper`. -/
private def wrapped : Database where
  sig := noSig
  terms := {num 1, num 2, .app "wrapper" [num 1], .app "wrapper" [num 2]}
  rows := Database.ctorRowsOf {num 1, num 2, .app "wrapper" [num 1], .app "wrapper" [num 2]}
  eqs := {(num 1, num 2)}
  env := []
  rules := ∅

example : Cong wrapped (.app "wrapper" [num 1]) (.app "wrapper" [num 2]) :=
  .congr (by simp [wrapped]) (by simp [wrapped])
    (.cons (.assert (by simp [wrapped])) .nil)

/-- Congruence derives nothing beyond what is asserted. Over `{1, 4, 7}` with only
`4 = 7`, the term `1` stays alone — proved by exhibiting a congruence containing the
assertions that `(1, 4)` is not in (`Cong.le`). -/
private def separate : Database where
  sig := noSig
  terms := {num 1, num 4, num 7}
  rows := Database.ctorRowsOf {num 1, num 4, num 7}
  eqs := {(num 4, num 7)}
  env := []
  rules := ∅

example : ¬ Cong separate (num 1) (num 4) := by
  intro h
  have hR := h.le (R := fun a b => a = b ∨ (a = num 4 ∧ b = num 7) ∨ (a = num 7 ∧ b = num 4))
    (fun a b hm => by simp only [separate, Set.mem_singleton_iff, Prod.mk.injEq] at hm
                      exact Or.inr (Or.inl ⟨hm.1, hm.2⟩))
    (fun _ _ => Or.inl rfl)
    (by rintro a b (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp)
    (by rintro a b c (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (rfl | ⟨h1, rfl⟩ | ⟨h1, rfl⟩) <;>
          simp_all [num])
    (fun f as bs hm _ _ => by simp [separate, num] at hm)
  simp [num] at hR

/-! ### E-matching

Over `{1, 2, (wrapper 2)}` with `1 = 2`, the pattern `(wrapper 1)` matches under the
empty substitution even though the database holds no such term, because `1 = 2` makes
it congruent to `(wrapper 2)`.

This is the witness mechanism. The instance `(wrapper 1)` is added to the database
before `Cong` is asked; the witness `(wrapper 2)` is drawn from the terms the
database held beforehand, which is what stops the pattern from matching in a database
that knows nothing about it. -/

/-- `1 = 2` over `{1, 2, (wrapper 2)}`. -/
private def preWrapped : Database where
  sig := Function.update noSig "wrapper" (some (ctorDecl 1))
  terms := {num 1, num 2, .app "wrapper" [num 2]}
  rows := Database.ctorRowsOf {num 1, num 2, .app "wrapper" [num 2]}
  eqs := {(num 1, num 2)}
  env := []
  rules := ∅

example : ValidSubst preWrapped (.expr (.app "wrapper" [eNum 1])) [] :=
  .expr (w := .app "wrapper" [num 2]) (t := .app "wrapper" [num 1])
    ⟨by simp [eNum], by simp⟩
    (by simp [preWrapped])
    (by rw [Expr.eval_app_ctor (show Prim.ofName "wrapper" = none from rfl)
          (show Signature.IsCtor preWrapped.sig "wrapper" from ⟨ctorDecl 1, rfl, rfl⟩)]
        rfl)
    (.congr (by simp [preWrapped]) (by simp [preWrapped])
      (.cons (.symm (.assert (by simp [preWrapped]))) .nil))

/-- Over the database holding just `1`, the substitution `v1 ↦ 1` is a valid
environment for `v1`. -/
example : ValidEnv ["v1"]
    { sig := noSig, terms := {num 1}, rows := Database.ctorRowsOf {num 1}, eqs := ∅,
      env := [], rules := ∅ } [("v1", num 1)] := by
  refine ⟨by simp, ?_⟩
  intro b hb
  rw [List.mem_singleton] at hb
  simp [hb]

/-! ### Running a program of actions

`(let v (b 1))`, `(union 7 7)`, `(union v 4)` gives terms `{(b 1), 4, 7, 1}` and,
after closure, `(b 1) = 4`. -/

private def b1 : Term := .app "b" [num 1]

private def actionsProgram : Program :=
  [.decl "b" (ctorDecl 1),
   .action (.letBind "v" (.app "b" [eNum 1])),
   .action (.union (eNum 7) (eNum 7)),
   .action (.union (.var "v") (eNum 4))]

example : WellScoped actionsProgram := by
  simp [WellScoped, actionsProgram, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped,
    Cmd.bind, Action.bind, eNum]

example : ∃ db, run actionsProgram = some db ∧
    db.terms = {b1, num 1, num 7, num 4} ∧
    db.eqs = {(num 7, num 7), (b1, num 4)} ∧
    Env.lookup "v" db.env = some b1 ∧
    Cong db (num 4) b1 := by
  refine ⟨_, rfl, ?_, ?_, rfl, ?_⟩
  · ext t; simp [b1, num]; tauto
  · ext p; simp [b1, num]; tauto
  · exact .symm (.assert (by simp [b1, num]))

/-! ### Running a rule

`(Add 1 2)`, `(rule ((Add a b)) ((Add b a)))`, `(run)` produces `(Add 2 1)`.
Only the forward direction is shown: the substitution `a ↦ 1, b ↦ 2` satisfies the
query and its actions build `(Add 2 1)`. That nothing *else* is produced needs
`ValidSubst` inversion (`PLAN.md`, M8). -/

private def add12 : Term := .app "Add" [num 1, num 2]

private def add21 : Term := .app "Add" [num 2, num 1]

private def swapRule : Rule where
  query := [.expr (.app "Add" [.var "a", .var "b"])]
  actions := [.expr (.app "Add" [.var "b", .var "a"])]

private def ruleProgram : Program :=
  [.decl "Add" (ctorDecl 2), .action (.expr (.app "Add" [eNum 1, eNum 2])),
   .rule swapRule, .run]

example : WellScoped ruleProgram := by
  simp [WellScoped, ruleProgram, Program.Scoped, Cmd.Scoped, Action.Scoped, Expr.Scoped,
    Expr.IsApp, Cmd.bind, Action.bind, Rule.Scoped, Pattern.Scoped, Actions.Scoped,
    Query.bind, Pattern.vars, swapRule, eNum]

/-- The database just before the `(run)`: `(Add 1 2)` with its children, plus the rule. -/
private def preRun : Database where
  sig := Function.update noSig "Add" (some (ctorDecl 2))
  terms := add12.subterms
  rows := add12.ctorRows
  eqs := ∅
  env := []
  rules := insert swapRule ∅

private theorem preRun_eq :
    runProgram Database.empty [.decl "Add" (ctorDecl 2),
      .action (.expr (.app "Add" [eNum 1, eNum 2])), .rule swapRule] = some preRun := by
  simp [runProgram, stepCmd, evalAction, Expr.eval, Expr.evalList, Database.empty, preRun,
    eNum, num, add12, Database.addTerm, Prim.ofName, Signature.IsCtor, ctorDecl]

private theorem run_ruleProgram : run ruleProgram = some (runRules preRun) := by
  change runProgram Database.empty
    ([.decl "Add" (ctorDecl 2), .action (.expr (.app "Add" [eNum 1, eNum 2])),
      .rule swapRule] ++ [Cmd.run]) = _
  rw [runProgram_append, preRun_eq]
  simp [stepCmd]

/-- The one firing of the rule: `a ↦ 1`, `b ↦ 2`, witnessed by `(Add 1 2)` itself. -/
private theorem swap_matches :
    ValidQuerySubst preRun swapRule.query [("a", num 1), ("b", num 2)] := by
  refine ⟨[[("a", num 1), ("b", num 2)]], .cons ?_ .nil, .single _⟩
  refine ValidSubst.expr (w := add12) (t := add12) ⟨?_, ?_⟩ ?_ ?_ (.refl ?_)
  · simp [Env.dom, preRun]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [preRun, add12, num]
  · simp [preRun, add12]
  · simp [Expr.eval, Expr.evalList, Env.lookup, preRun, add12, num, Prim.ofName,
      Signature.IsCtor, ctorDecl]
  · simp [preRun, add12]

/-- Running that firing adds `(Add 2 1)` and its children. -/
private theorem swap_fires :
    evalLocalActions preRun swapRule.actions [("a", num 1), ("b", num 2)]
      = some { preRun with terms := preRun.terms ∪ add21.subterms,
                           rows := preRun.rows ∪ add21.ctorRows } := by
  simp [evalLocalActions, evalActions, evalAction, Expr.eval, Expr.evalList, Env.lookup,
    swapRule, preRun, add21, num, Database.addTerm, Prim.ofName, Signature.IsCtor,
    ctorDecl]

/-- `(Add 2 1)` is in the database after the run. -/
example : ∃ db, run ruleProgram = some db ∧ add21 ∈ db.terms := by
  refine ⟨runRules preRun, run_ruleProgram, ?_⟩
  have hmem : ({ preRun with terms := preRun.terms ∪ add21.subterms,
                             rows := preRun.rows ∪ add21.ctorRows } : Database) ∈
      {d | ∃ r ∈ preRun.rules, d ∈ ruleResults preRun r} :=
    ⟨swapRule, by simp [preRun], _, swap_matches, swap_fires⟩
  exact Or.inr (Set.mem_biUnion hmem (Or.inr add21.self_mem_subterms))

/-! ### The closure, computed

The two closures above again, computed rather than proved: `Closure.closure` writes out
the closed set of pairs in full. `#guard` is checked at compile time
and, being a command rather than a proof, puts nothing into any proof term; `closure`
is well-founded recursion and so sealed against the kernel, which `unseal` lifts where
a real proof wants it. -/

section Computed
set_option linter.hashCommand false

/-- `{1, 2, 3}` with `1 = 2` and `2 = 3`: all nine pairs. -/
private def chainTerms : Finset Term := {num 1, num 2, num 3}

private def chainEqs : Finset (Term × Term) := {(num 1, num 2), (num 2, num 3)}

private theorem chainEqs_sub : chainEqs ⊆ candidates chainTerms := by decide

#guard (closure chainTerms chainEqs chainEqs_sub).card = 9

/-- `{1, 2, (wrapper 1), (wrapper 2)}` with `1 = 2`: the eight pairs of the two classes
`{1, 2}` and `{(wrapper 1), (wrapper 2)}` — congruence
propagating under `wrapper`, and nothing across the two classes. -/
private def wrappedTerms : Finset Term :=
  {num 1, num 2, .app "wrapper" [num 1], .app "wrapper" [num 2]}

private def wrappedEqs : Finset (Term × Term) := {(num 1, num 2)}

private theorem wrappedEqs_sub : wrappedEqs ⊆ candidates wrappedTerms := by decide

#guard (closure wrappedTerms wrappedEqs wrappedEqs_sub).card = 8

#guard decide ((Term.app "wrapper" [num 1], Term.app "wrapper" [num 2])
  ∈ closure wrappedTerms wrappedEqs wrappedEqs_sub)

#guard decide ((num 1, Term.app "wrapper" [num 1])
  ∈ closure wrappedTerms wrappedEqs wrappedEqs_sub) = false

-- `closure` is well-founded recursion, so it is sealed against kernel reduction;
-- `unseal` lets `decide` through for the example below.
unseal closure

/-- The computation transfers to the spec: `mem_closure_iff` turns a decidable
membership into a `Cong` derivation, which is what an executable interpreter will lean
on throughout. -/
example : Cong chain (num 1) (num 3) := by
  refine (mem_closure_iff (terms := chainTerms) (rel := chainEqs) ?_ ?_ chainEqs_sub).mp
    (by decide)
  · simp [chain, chainTerms]
  · simp [chain, chainEqs]

/-! ### Running programs

Whole programs, run by the interpreter rather than proved. This includes the two-round
`Wrapper` case, which needs `ValidSubst` inversion to state as a theorem and so has no
hand proof. -/

/- `(Add 1 2)`, `(rule ((Add a b)) ((Add b a)))`, `(run)`: terms
`{(Add 1 2), 1, 2, (Add 2 1)}`. `Add` holds two rows — `1` and `2` are not equal, so the
two argument lists are not congruent. -/
#guard (exec ruleProgram).map (fun d => d.terms.toFinset.card) = some 4

#guard (exec ruleProgram).map (fun d => decide (add21 ∈ d.terms)) = some true

#guard (exec ruleProgram).map (fun d => d.rowCount "Add") = some 2

/-- `(Wrapper (Add 1 2))`, `(rule ((Add a b)) ((union (Add a b) (Add b a))))`,
`(rule ((= (Wrapper (Add 1 2)) (Wrapper (Add 2 1)))) ((success)))`, `(run)`, `(run)`: the
second rule fires only because `(Wrapper (Add 2 1))` is *congruent* to a term the database
holds, not because that term was ever built — the witness mechanism, end to end. -/
private def commuteRule : Rule where
  query := [.expr (.app "Add" [.var "a", .var "b"])]
  actions := [.union (.app "Add" [.var "a", .var "b"]) (.app "Add" [.var "b", .var "a"])]

private def detectRule : Rule where
  query := [.eq (.app "Wrapper" [.app "Add" [eNum 1, eNum 2]])
                (.app "Wrapper" [.app "Add" [eNum 2, eNum 1]])]
  actions := [.expr (.app "success" [])]

private def wrapperDecls : Program :=
  [.decl "Add" (ctorDecl 2), .decl "Wrapper" (ctorDecl 1), .decl "success" (ctorDecl 0)]

private def wrapperProgram : Program :=
  wrapperDecls ++
    [.action (.expr (.app "Wrapper" [.app "Add" [eNum 1, eNum 2]])),
     .rule commuteRule, .rule detectRule, .run, .run]

#guard (exec wrapperProgram).map (fun d => decide (Term.app "success" [] ∈ d.terms))
  = some true

/- One round is not enough: the union has to happen before the second rule can match. -/
#guard (exec (wrapperDecls ++
    [.action (.expr (.app "Wrapper" [.app "Add" [eNum 1, eNum 2]])),
     .rule commuteRule, .rule detectRule, .run])).map
  (fun d => decide (Term.app "success" [] ∈ d.terms)) = some false

#guard (exec wrapperProgram).map (fun d => d.rowCounts ["Add", "Wrapper", "success"])
  = some [("Add", 2), ("Wrapper", 1), ("success", 1)]

end Computed

/-! ## Arity

`Impl/Check.lean`'s `Program.arityOk` mirrors what egglog's typechecker does with column
counts. Every rejection below was run against the release binary first, and the quoted text
is what it printed; the accompanying acceptances are what keep the check from being
vacuous — a predicate that rejected everything would satisfy the rejections alone. -/
namespace Arity
set_option linter.hashCommand false

private def emptySig : Signature := fun _ => none

/- `(function Dist (Math) i64 :merge 0)`. -/
private def one : FnDecl :=
  { arity := 1, outArity := 1, merge := some (.merge [] [eNum 0]) }

/- `(function Dist (Math) (i64 i64) :merge (values 0 1))`. -/
private def two : FnDecl :=
  { arity := 1, outArity := 2, merge := some (.merge [] [eNum 0, eNum 1]) }

private def A : Expr := .app "A" []

private def prog (d : FnDecl) (cs : List Cmd) : Program := .decl "Dist" d :: cs

private def accepts (d : FnDecl) (cs : List Cmd) : Bool := (prog d cs).arityOk emptySig

/-! ### One value column -/

#guard accepts one [.action (.set "Dist" [A] [eNum 3])]
#guard accepts one [.rule ⟨[.expr (.app "Dist" [.var "k"])], []⟩]
#guard accepts one [.rule ⟨[.eq (eNum 3) (.app "Dist" [.var "k"])], []⟩]
#guard accepts one [.action (.letBind "x" (.app "Dist" [A]))]

/- "Arity mismatch, expected 1 args: (Dist @A @A1)" — too many key columns. -/
#guard !accepts one [.action (.set "Dist" [A, A] [eNum 3])]

/- "Arity mismatch, expected 1 args: (Dist @A 3)" — `(set (Dist (A)) (values 3 4))`
flattens to three columns where the table has two. -/
#guard !accepts one [.action (.set "Dist" [A] [eNum 3, eNum 4])]

/- The row atom at one value column, which is how a single-column read is written since
`Expr.eval` does not look up. `Tests/Egg.lean` renders it `(= v (Dist k))`: writing
`(= (values v) (Dist k))` instead is "Unbound function values", because `values` is
recognized only for a tuple output. -/
#guard accepts one [.rule ⟨[.values [.var "v"] "Dist" [.var "k"]], []⟩]

/- "Arity mismatch, expected 1 args: (Dist a b)" — in a query fact too. -/
#guard !accepts one [.rule ⟨[.expr (.app "Dist" [.var "a", .var "b"])], []⟩]

/-! ### Two value columns -/

#guard accepts two [.action (.set "Dist" [A] [eNum 3, eNum 4])]
#guard accepts two [.rule ⟨[.values [.var "v", .var "w"] "Dist" [.var "k"]], []⟩]

/- "Arity mismatch, expected 2 args: (Dist @A)" — a bare value on a two-column table. -/
#guard !accepts two [.action (.set "Dist" [A] [eNum 3])]

/- "Arity mismatch, expected 2 args: (Dist @A2)" — a tuple-output function cannot be
evaluated as an expression: only one output variable is appended. -/
#guard !accepts two [.action (.letBind "x" (.app "Dist" [A]))]

/- "Arity mismatch, expected 2 args: (Dist k)" — nor read as a bare query fact, for the
same reason. A read of any width is `Pattern.values`. -/
#guard !accepts two [.rule ⟨[.expr (.app "Dist" [.var "k"])], []⟩]

/- "Arity mismatch, expected 2 args: (Dist k v)" — the destructure binds every value
column or none. -/
#guard !accepts two [.rule ⟨[.values [.var "v"] "Dist" [.var "k"]], []⟩]

/-! ### The declaration itself -/

/- "The :merge of tuple-output function Dist has 1 columns but the function has 2 output
columns." -/
#guard !accepts { two with merge := some (.merge [] [eNum 0]) } []

/- "Function F has a tuple output, which is only allowed for plain functions (not
constructors, relations, or view tables)." -/
#guard !Program.arityOk [.decl "F" { arity := 1, outArity := 2, merge := none }] emptySig

/- `:no-merge` has no result to check, and a tuple output is legal on one. -/
#guard Program.arityOk
  [.decl "F" { arity := 1, outArity := 2, merge := some .noMerge }] emptySig

/- A merge body is checked against the signature the declaration itself installs, so it
may write the function's own table — `(function Dist (Math) i64 :merge ((set (Dist (A)) 1)
(min old new)))` runs. A forward reference is instead "Unbound function". -/
#guard accepts { one with merge := some (.merge [.set "Dist" [A] [eNum 1]] [eNum 0]) } []

/- …and its arity is checked there too: "Arity mismatch, expected 1 args:
(Dist @A @A1)". -/
#guard !accepts
  { one with merge := some (.merge [.set "Dist" [A, A] [eNum 1]] [eNum 0]) } []

/-! ### Undeclared names are unconstrained

`Program.arityOk` reads `Signature` and nothing else, so a name with no entry has no
declared column counts to disagree with and the check passes a name used at two arities.
That a program must declare before it uses is `Program.Evaluable`'s business, not this
one's; that the *emitted* `datatype` header cannot express two arities is
`Tests/Egg.lean`'s `Program.arityConflicts`. -/
#guard Program.arityOk [.action (.expr (.app "F" [A])), .action (.expr (.app "F" [A, A]))]
  emptySig

end Arity

/-! ## Reading

`Impl/Check.lean`'s `Program.noLookup`: applying a non-constructor is a *read*, and the
only place a program may read is the query atom `Pattern.values`. egglog enforces this in
a rule head — "Value lookup of non-constructor function function in rule is disallowed" —
and this model everywhere, which is what makes `Expr.eval` deterministic. The three
places egglog is more permissive are each marked below.

Acceptances matter as much as rejections here: a predicate that rejected everything would
satisfy the rejections on its own. -/
namespace Reading
set_option linter.hashCommand false

private def emptySig : Signature := fun _ => none

/- `(function Dist (Math) i64 :merge (min old new))` and a second like it. -/
private def dist : FnDecl :=
  { arity := 1, outArity := 1,
    merge := some (.merge [] [.app "min" [.var "old", .var "new"]]) }

/-- The constructors the cases below apply, declared: `noLookup` asks for a *declared*
constructor or a primitive, so an undeclared name would be rejected for the wrong
reason. -/
private def decls : Program :=
  [.decl "A" (ctorDecl 0), .decl "F" (ctorDecl 1), .decl "G" (ctorDecl 2),
   .decl "Dist" dist, .decl "Copy" dist]

private def A : Expr := .app "A" []

private def ok (cs : List Cmd) : Bool := (decls ++ cs).noLookup emptySig

/-! ### A rule head — egglog rejects these too -/

/- "Value lookup of non-constructor function function in rule is disallowed." -/
#guard !ok [.rule ⟨[.values [.var "v"] "Dist" [.var "k"]],
                   [.set "Copy" [.var "k"] [.app "Dist" [.var "k"]]]⟩]

/- The same read nested inside a constructor application, and inside a `union`. -/
#guard !ok [.rule ⟨[], [.expr (.app "F" [.app "Dist" [A]])]⟩]
#guard !ok [.rule ⟨[], [.union (.app "Dist" [A]) A]⟩]

/- The query binds the value and the head only writes: this is the shape egglog wants. -/
#guard ok [.rule ⟨[.values [.var "v"] "Dist" [.var "k"]],
                  [.set "Copy" [.var "k"] [.var "v"]]⟩]

/-! ### Positions where egglog is more permissive

Each of the three runs in the binary and is rejected here, which is what confines reading
to `Pattern.values` and so what removes `Expr.eval`'s `lookup` constructor. -/

/- A top-level action. `(set (Copy (A)) (Dist (A)))` copies the value in egglog. -/
#guard !ok [.action (.set "Copy" [A] [.app "Dist" [A]])]

/- A `:merge` body, typechecked under `Context::Write`, which never runs the check.
`(function Dist (Math) i64 :merge (max old (Zero)))` reads `Zero` and panics with
"Lookup on Zero failed in the merge function for Dist" when the row is missing. -/
#guard !Program.noLookup
  [.decl "Zero" { arity := 0, outArity := 1, merge := some (.merge [] [.lit (.int 0)]) },
   .decl "Dist" { arity := 1, outArity := 1,
                  merge := some (.merge [] [.app "max" [.var "old", .app "Zero" []]]) }]
  emptySig

/- A read nested in a query fact. egglog flattens `(F (Dist k))` into the two atoms
`Dist(k, v), F(v, o)`; this model has no flattening pass, so it must be written flat. -/
#guard !ok [.rule ⟨[.expr (.app "F" [.app "Dist" [.var "k"]])], []⟩]
#guard ok [.rule ⟨[.values [.var "v"] "Dist" [.var "k"], .expr (.app "F" [.var "v"])], []⟩]

/-! ### What still passes

A declared constructor, a primitive and a literal are not reads. The primitive has a case
of its own — `Prim.ofName` is consulted first, exactly as `Expr.eval` does — so a merge
body computing `(min old new)` is fine, and a body writing its own table is a write. -/
#guard ok [.action (.expr (.app "F" [A])), .action (.union A (.app "G" [A, A]))]
#guard Program.noLookup decls emptySig
#guard Program.noLookup
  [.decl "A" (ctorDecl 0),
   .decl "Dist" { arity := 1, outArity := 1,
                  merge := some (.merge [.set "Dist" [A] [.lit (.int 1)]]
                    [.app "min" [.var "old", .var "new"]]) }] emptySig

end Reading

end Egglog.Examples
