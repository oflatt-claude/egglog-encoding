import Batteries.Data.List.Basic

/-!
# Syntax of the modelled egglog fragment

Ported from `semantics.rkt` in
[egglog PR #324](https://github.com/egraphs-good/egglog/pull/324), whose grammar is

```
Program = (Cmd ...)
Cmd     = Action | Rule | (run) | skip
Rule    = (rule Query Actions)
Query   = (Pattern ...)
Pattern = (= expr expr) | expr
Action  = expr | (let var expr) | (union expr expr)
expr    = number | (constructor expr ...) | var
```

Two deviations:

* `skip` is an artifact of Redex's two-level reduction relation and is dropped.
* `Cmd.decl` and `Signature` are new. The Redex has no signature at all, and treats
  every applied name as a constructor. Here a name means nothing until it is declared:
  `Expr.eval` builds an application only at a declared constructor, which is egglog's
  own declare-before-use and is what `Spec/Scope.lean`'s `Evaluable` demands
  statically.

`Expr` nests `List Expr`, which no `deriving` handler supports, so the types below
carry no derived instances. The semantics is relational and needs none; an
executable interpreter would have to write them by mutual recursion.
-/

namespace Egglog
/-- A variable, global or rule-local. -/
abbrev Var := String

/-- The name of a constructor or function. -/
abbrev FnName := String

/-- A base value. The Redex `number` covers all of Racket's numeric tower; `Int`
is enough here. Kept a separate type so `:merge` functions can add sorts. -/
inductive Lit where
  | int : Int → Lit
  deriving DecidableEq, Repr, Inhabited

/-- An expression. Evaluated against an environment to build a `Term`. -/
inductive Expr where
  | lit : Lit → Expr
  | var : Var → Expr
  | app : FnName → List Expr → Expr

/-- One conjunct of a rule's query: either a pattern to match, or an equality
constraint between two patterns. -/
inductive Pattern where
  | expr : Expr → Pattern
  | eq : Expr → Expr → Pattern
  /-- `f(a…, v…)`: read a row of `f` and bind its value columns. **The only read in the
  language.**

  This is egglog's lowered query atom, which every fact naming a non-constructor compiles
  to. Its three surface forms — `(f a…)`, `(= v (f a…))` and the tuple destructure
  `(= (values v…) (f a…))` — are one case here because they are one atom there;
  `Tests/Egg.lean` renders whichever fits the width.

  A `Pattern` case rather than a reserved `values` name inside `.eq`, for the reason that
  keeps primitives out of `Expr` (`MERGE.md`, "Multi-column outputs"): a name that is a
  term constructor in one position and a keyword in another is a trap. -/
  | values : List Expr → FnName → List Expr → Pattern

/-- A rule's query, matched conjunctively. -/
abbrev Query := List Pattern

/-- An action: build a term, bind a variable, assert an equality, or write a row.

`set` is what a `:merge` function needs (M9) and what an encoded rule head writes
(M11) — `(set (@AddView b a) (values rewrite_var ()))`. The Redex has no such action;
for a constructor-only program it is unreachable. -/
inductive Action where
  | expr : Expr → Action
  | letBind : Var → Expr → Action
  | union : Expr → Expr → Action
  /-- `(set (f args…) out…)`: assert the row `f args… ↦ out…`.

  The outputs are a **list**, one per value column, where the surface syntax writes a
  single expression for a one-column function and `(values e₀ e₁ …)` for a tuple-output
  one — the same deviation `MergeSpec.merge`'s result records. -/
  | set : FnName → List Expr → List Expr → Action

/-- A rule. Its actions run once per substitution satisfying its query. -/
structure Rule where
  query : Query
  actions : List Action

/-- How two rows of a **merge function** colliding on one key combine.

`merge body result` runs `body` once, with the two rows' outputs bound by `mergeEnv`, and
then evaluates `result` — **one expression per value column**, where the surface syntax
writes one tuple-valued `(values e₀ e₁ …)`. `noMerge` forbids a collision outright.

A constructor has no merge specification at all (`FnDecl.merge`): its collisions are an
equality, which is exactly congruence, and `MCong.fd` is the one rule that covers both.

See `MERGE.md`, "Multi-column outputs", for the per-column result and for the one place
this is coarser than egglog: a merge kind is per *function* here and per *column* there. -/
inductive MergeSpec where
  | merge : List Action → List Expr → MergeSpec
  | noMerge

/-- A function declaration.

egglog has two declaration forms and this is both of them: `(datatype …)` and
`(constructor …)` declare a **constructor**, which is `merge = none`; `(function … :merge …)`
declares a **merge function**, which is `merge = some …`. -/
structure FnDecl where
  /-- The number of key columns. Surface syntax only: nothing in `Spec/` reads it, and
  `Impl/Check.lean`'s arity check and `Tests/Egg.lean`'s emitter are its consumers. -/
  arity : Nat
  /-- The number of value columns. One for a constructor. Surface syntax only, as
  `arity`. -/
  outArity : Nat
  /-- How collisions are resolved, or `none` for a constructor. The one field the
  semantics reads: `Signature.IsCtor` and `Signature.mergeOf` are both this plus the
  question of whether there is an entry at all. -/
  merge : Option MergeSpec

/-- The declared functions. Undeclared names have no entry. -/
abbrev Signature := FnName → Option FnDecl

/-- How `f` resolves a collision. `none` covers two cases that are the same here and
different for `IsCtor`: a declared constructor, and a name nobody declared. -/
def Signature.mergeOf (sig : Signature) (f : FnName) : Option MergeSpec :=
  (sig f).bind FnDecl.merge

/-- `f` is a **declared** constructor: `(datatype …)` or `(constructor …)`.

Declaration is required. An undeclared name is not a constructor and not a merge
function; it is nothing, and `Expr.eval` has no rule for it. That is egglog's own
declare-before-use, and it is what `Spec/Scope.lean`'s `Evaluable` asks of every applied
name.

It also decides what a later declaration can undo. `Spec/Merge.lean`'s `MCong.fd` fires
only here, so if an undeclared name were a constructor, declaring it `:merge` would
*remove* derivations — `Proofs/Merge.lean`'s `CmdStep.mono_recorded` is where that is
paid for. -/
def Signature.IsCtor (sig : Signature) (f : FnName) : Prop :=
  ∃ d, sig f = some d ∧ d.merge = none

instance (sig : Signature) (f : FnName) : Decidable (sig.IsCtor f) :=
  decidable_of_iff (((sig f).map fun d => d.merge.isNone).getD false = true) (by
    unfold Signature.IsCtor
    cases h : sig f with
    | none => simp
    | some d => simp [Option.isNone_iff_eq_none])

/-- No declared function has a merge specification: the fragment this phase models.

Not `∀ f, sig.IsCtor f`, which would ask that every name in the universe be declared.
What a phase without `:merge` needs is that nothing *is* a merge function, which is
exactly what makes `MergeStep` vacuous. -/
def Signature.AllConstructors (sig : Signature) : Prop := ∀ f, sig.mergeOf f = none

/-! ### Variables and function names

The Redex has no `vars` function — its `typed-expr` walks the expression instead.
Having them separately is what lets the static checks in `Scope.lean` be related to the
runtime state: `vars` is what the environment must bind, `fns` what the signature must
declare. -/
mutual

/-- All variables occurring in `e`, deduplicated. -/
def Expr.vars : Expr → List Var
  | .lit _ => []
  | .var v => [v]
  | .app _ args => Expr.varsList args

/-- `Expr.vars` over an argument list. -/
def Expr.varsList : List Expr → List Var
  | [] => []
  | e :: es => e.vars ∪ Expr.varsList es

end

mutual

/-- Every function name applied anywhere in `e`. -/
def Expr.fns : Expr → List FnName
  | .lit _ => []
  | .var _ => []
  | .app f args => f :: Expr.fnsList args

/-- `Expr.fns` over an argument list. -/
def Expr.fnsList : List Expr → List FnName
  | [] => []
  | e :: es => e.fns ∪ Expr.fnsList es

end

/-- All variables occurring in a pattern. -/
def Pattern.vars : Pattern → List Var
  | .expr e => e.vars
  | .eq e₁ e₂ => e₁.vars ∪ e₂.vars
  | .values vs _ as => Expr.varsList vs ∪ Expr.varsList as

/-- All variables occurring in a query. -/
def Query.vars : Query → List Var
  | [] => []
  | p :: ps => p.vars ∪ Query.vars ps

/-- A top-level command. -/
inductive Cmd where
  | action : Action → Cmd
  | rule : Rule → Cmd
  | run : Cmd
  | decl : FnName → FnDecl → Cmd

/-- A program is a sequence of commands. -/
abbrev Program := List Cmd

end Egglog
