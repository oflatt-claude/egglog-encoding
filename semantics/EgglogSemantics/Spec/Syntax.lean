import Batteries.Data.List.Basic

/-!
# Syntax of the modelled egglog fragment

The fragment's grammar:

```
Program = (Cmd ...)
Cmd     = Action | Rule | (run) | Decl
Decl    = (datatype ...) | (constructor ...) | (function ... :merge ...)
Rule    = (rule Query Actions)
Query   = (Pattern ...)
Pattern = expr | (= expr expr) | (= (values expr ...) (f expr ...))
Action  = expr | (let var expr) | (union expr expr) | (set (f expr ...) expr ...)
expr    = number | var | (f expr ...)
```

A name means nothing until it is declared: `Expr.eval` builds an application only at a
declared constructor, which is egglog's own declare-before-use and is what
`Spec/Scope.lean`'s `Evaluable` demands statically. `Signature` is where the declarations
live, and `Cmd.decl` is the only thing that writes it.

`Expr` nests `List Expr`, which no `deriving` handler supports, so the types below carry
no derived instances.
-/

namespace Egglog
/-- A variable, global or rule-local. -/
abbrev Var := String

/-- The name of a constructor or function. -/
abbrev FnName := String

/-- A base value. `Int` is the only one modelled; kept a separate type so `:merge`
functions can add sorts. -/
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
  /-- `f(a…, v…)`: read `f`'s entry at the key `a…` and bind its value columns `v…`.
  **The only read in the language.**

  This is egglog's lowered query atom, which every fact naming a non-constructor compiles
  to. Its three surface forms — `(f a…)`, `(= v (f a…))` and the tuple destructure
  `(= (values v…) (f a…))` — are one case here because they are one atom there.

  A `Pattern` case rather than a reserved `values` name inside `.eq`: a name that is a
  term constructor in one position and a keyword in another is a trap. -/
  | values : List Expr → FnName → List Expr → Pattern

/-- A rule's query, matched conjunctively. -/
abbrev Query := List Pattern

/-- An action: build a term, bind a variable, assert an equality, or record an entry.

`set` is what a `:merge` function needs and what an encoded rule head writes —
`(set (@AddView b a) (values rewrite_var ()))`. For a constructor-only program it is
unreachable. -/
inductive Action where
  | expr : Expr → Action
  | letBind : Var → Expr → Action
  | union : Expr → Expr → Action
  /-- `(set (f args…) out…)`: record `f args… ↦ out…`. The outputs are a **list**, one per
  value column, where the surface syntax writes a single expression for a one-column
  function and `(values e₀ e₁ …)` for a tuple-output one. -/
  | set : FnName → List Expr → List Expr → Action

/-- A rule. Its actions run once per substitution satisfying its query. -/
structure Rule where
  query : Query
  actions : List Action

/-- How two entries of a **merge function** colliding on one key combine.

`merge body result` runs `body` once, with the two entries' outputs bound by `mergeEnv`,
and then evaluates `result` — **one expression per value column**, where the surface syntax
writes one tuple-valued `(values e₀ e₁ …)`. `noMerge` forbids a collision outright.

A constructor has no merge specification at all: its collisions are an equality, and that
equality is `Cong` already — `Proofs/Congruence.lean`'s `Cong.fd`. A merge kind is per
*function* here and per *column* in egglog — `MERGE.md`, "Multi-column outputs". -/
inductive MergeSpec where
  | merge : List Action → List Expr → MergeSpec
  | noMerge

/-- A function declaration.

egglog has two declaration forms and this is both of them: `(datatype …)` and
`(constructor …)` declare a **constructor**, which is `merge = none`; `(function … :merge …)`
declares a **merge function**, which is `merge = some …`. -/
structure FnDecl where
  /-- The number of key columns. Read by `MergeStep`, which needs to know where a term's
  key ends and its value columns begin. -/
  arity : Nat
  /-- The number of value columns. One for a constructor. -/
  outArity : Nat
  /-- How collisions are resolved, or `none` for a constructor. `Signature.IsCtor` and
  `Signature.mergeOf` are both this plus whether there is a declaration at all. -/
  merge : Option MergeSpec

/-- How many children a term recording an entry of this function carries.

A constructor's value *is* its application, so its entry is `f(a…)` and its key is all of
it. A merge function's entry appends the value columns: `f(a…, v…)`. -/
def FnDecl.entryWidth (d : FnDecl) : Nat :=
  if d.merge.isNone then d.arity else d.arity + d.outArity

/-- The declared functions. Undeclared names have no entry. -/
abbrev Signature := FnName → Option FnDecl

/-- How `f` resolves a collision. `none` covers two cases that are the same here and
different for `IsCtor`: a declared constructor, and a name nobody declared. -/
def Signature.mergeOf (sig : Signature) (f : FnName) : Option MergeSpec :=
  (sig f).bind FnDecl.merge

/-- `f` is a **declared** constructor: `(datatype …)` or `(constructor …)`.

An undeclared name is not a constructor and not a merge function; it is nothing, and
`Expr.eval` has no rule for it — which is egglog's declare-before-use, and the only thing
this predicate is read for. `Cong` does not read the signature at all, so a later
declaration cannot take a derivation away. -/
def Signature.IsCtor (sig : Signature) (f : FnName) : Prop :=
  ∃ d, sig f = some d ∧ d.merge = none

instance (sig : Signature) (f : FnName) : Decidable (sig.IsCtor f) :=
  decidable_of_iff (((sig f).map fun d => d.merge.isNone).getD false = true) (by
    unfold Signature.IsCtor
    cases h : sig f with
    | none => simp
    | some d => simp [Option.isNone_iff_eq_none])

/-- No declared function has a merge specification. Not `∀ f, sig.IsCtor f`, which would
ask that every name in the universe be declared; what matters is that nothing *is* a merge
function, which is exactly what makes `MergeStep` vacuous. -/
def Signature.AllConstructors (sig : Signature) : Prop := ∀ f, sig.mergeOf f = none

/-! ### Variables and function names

Collected up front so that `Scope.lean`'s static checks can be related to the runtime
state: `vars` is what the environment must bind, `fns` what the signature must
declare. -/
mutual

/-- All variables occurring in `e`, deduplicated. -/
def Expr.vars : Expr → List Var
  | .lit _ => []
  | .var v => [v]
  | .app _ args => Expr.varsList args

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

def Expr.fnsList : List Expr → List FnName
  | [] => []
  | e :: es => e.fns ∪ Expr.fnsList es

end

def Pattern.vars : Pattern → List Var
  | .expr e => e.vars
  | .eq e₁ e₂ => e₁.vars ∪ e₂.vars
  | .values vs _ as => Expr.varsList vs ∪ Expr.varsList as

def Query.vars : Query → List Var
  | [] => []
  | p :: ps => p.vars ∪ Query.vars ps

/-- A top-level command. -/
inductive Cmd where
  | action : Action → Cmd
  | rule : Rule → Cmd
  | run : Cmd
  | decl : FnName → FnDecl → Cmd

abbrev Program := List Cmd

/-! ### The constructor-only fragment

`Signature.AllConstructors` says a *state* is in the fragment this phase models; this says
a *program* keeps it there. It is a fragment restriction and not a front-end check —
egglog accepts a `:merge` declaration — which is why it is here rather than among
`Spec/Scope.lean`'s checks. -/

/-- `c` declares only constructors. Separate from `Action.SetLegal`, which says what a
head may write where this says what the signature may become: declaring a `:merge`
function makes terms *already present* a `MergeStep` collision, with no `set` involved. -/
def Cmd.CtorDecl : Cmd → Prop
  | .decl _ d => d.merge = none
  | _ => True

/-- Every declaration in the program declares a constructor. -/
def Program.CtorDecls (p : Program) : Prop := ∀ c ∈ p, c.CtorDecl

end Egglog
