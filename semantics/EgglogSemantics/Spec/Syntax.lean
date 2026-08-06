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
* `Cmd.decl` and `Signature` are new. The Redex has no signature at all; they are
  here from the start so that adding `:merge` functions later extends `MergeSpec`
  rather than reshaping the AST. Nothing in this phase reads a declaration.

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

/-- A rule's query, matched conjunctively. -/
abbrev Query := List Pattern

/-- An action: build a term, bind a variable, or assert an equality. -/
inductive Action where
  | expr : Expr → Action
  | letBind : Var → Expr → Action
  | union : Expr → Expr → Action

/-- A rule. Its actions run once per substitution satisfying its query. -/
structure Rule where
  query : Query
  actions : List Action

/-- How two rows colliding on one key combine.

Only `union` is reachable in this phase; the other cases are the hooks for
`:merge` functions. `union` makes the collision an equality, which is exactly
congruence — see `proof_encoding.md`, "the view's `:merge` resolves congruence
directly". -/
inductive MergeSpec where
  | union
  | merge : Expr → MergeSpec
  | noMerge

/-- A function declaration. -/
structure FnDecl where
  arity : Nat
  merge : MergeSpec

/-- The declared functions. Undeclared names have no entry. -/
abbrev Signature := FnName → Option FnDecl

/-- A signature all of whose functions are constructors, i.e. the fragment this
phase models. -/
def Signature.AllConstructors (sig : Signature) : Prop :=
  ∀ f d, sig f = some d → d.merge = MergeSpec.union

/-! ### Variables

The Redex has no `vars` function — its `typed-expr` walks the expression instead.
Having it separately is what lets the static scope check in `Scope.lean` be related
to the runtime environment. -/
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

/-- All variables occurring in a pattern. -/
def Pattern.vars : Pattern → List Var
  | .expr e => e.vars
  | .eq e₁ e₂ => e₁.vars ∪ e₂.vars

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
