import Batteries.Data.List.Basic
import Architect

/-!
# Syntax of the modelled egglog fragment

```
Program = (Cmd ...)
Cmd     = Rule | (run R) | (saturate R) | Decl | (check Query)
Decl    = (constructor ...) | (function ... :merge ...)
Rule    = (rule Query Actions :ruleset R)
Query   = (Pattern ...)
Pattern = expr | (= expr expr)
Action  = expr | (union expr expr)
expr    = number | var | (f expr ...) | (min expr expr) | (if (expr ...) = (expr ...) expr expr)
merge   = (merge (old-vars ...) (new-vars ...) Actions (expr ...))
```
-/

namespace Egglog
/-- A variable bound by a query or a merge parameter. -/
abbrev Var := String

/-- The name of a constructor or function. -/
abbrev FnName := String

/-- Mathematical integers, modelling egglog's integer literals without overflow. -/
inductive Lit where
  | int : Int → Lit
  deriving DecidableEq, Repr, Inhabited

/-- An expression. Evaluated against an environment to build a `Term`. -/
-- The paper displays the literal-free fragment; the model also supports integers.
@[blueprint "def:expressions"
  (statement := /--
  \syntaxline{Expressions}{\begin{aligned}[t]
    e &::= x\mid f(e_1,\ldots,e_n)\mid\min(e,e)\\[-1pt]
      &\phantom{::={}}\mid\kw{if}\ (e_1,\ldots,e_n)=(e'_1,\ldots,e'_n)\\[-1pt]
      &\qquad\kw{then}\ e\ \kw{else}\ e
    \end{aligned}}
  -/)
  (latexEnv := "paperfragment")]
inductive Expr where
  | lit : Lit → Expr
  | var : Var → Expr
  | app : FnName → List Expr → Expr
  /-- The smaller term in the fixed order, used by merges and leader selection. -/
  | min : Expr → Expr → Expr
  /-- Compare evaluated tuples, evaluating only the chosen branch. -/
  | ite (lhs rhs : List Expr) (yes no : Expr)

/-- One conjunct of a rule's query: a pattern to match, an equality constraint, or an
entry to read. -/
@[blueprint "def:patterns"
  (statement := /-- \syntaxline{Patterns}{p ::= e\mid e=e} -/)
  (latexEnv := "paperfragment")]
inductive Pattern where
  | expr : Expr → Pattern
  | eq : Expr → Expr → Pattern

/-- A rule's query, matched conjunctively. -/
@[blueprint "def:queries"
  (statement := /-- \syntaxline{Queries}{Q ::= p_1\land\cdots\land p_n} -/)
  (latexEnv := "paperfragment")]
abbrev Query := List Pattern

/-- An action: build a term, assert an equality, or record an entry. -/
@[blueprint "def:action-syntax"
  (statement := /--
  \syntaxline{Actions}{h ::= e\mid\kw{union}(e,e)}
  \syntaxline{Heads}{H ::= h_1;\ldots;h_n}
  -/)
  (latexEnv := "paperfragment")]
inductive Action where
  | expr : Expr → Action
  | union : Expr → Expr → Action

/-- A ruleset name. A rule joins one with `:ruleset <name>`, and a run names the one it
fires. egglog's *unnamed* ruleset is the empty name: that is what a rule with no
`:ruleset` joins and what `(run 1)` runs (`egglog/src/ast/parse.rs:713`, `:849`); a named
one is declared with `(ruleset <name>)` (`:686`). -/
abbrev RulesetName := String

/-- A rule. Its actions run once per substitution satisfying its query, in the rounds of
the ruleset it joins. -/
@[blueprint "def:rules"
  (statement := /--
  \syntaxline{Rules}{\rho ::= (R,Q\Rightarrow H)}
  -/)
  (latexEnv := "paperfragment")]
structure Rule where
  query : Query
  actions : List Action
  /-- The ruleset this rule belongs to. Only a run naming it fires it. -/
  ruleset : RulesetName

/-- Explicitly bind both output tuples before evaluating its body and result. -/
@[blueprint "def:merges"
  (statement := /--
  \syntaxline{Merges}{\begin{aligned}[t]
    \mu &::= \kw{merge}((x_1,\ldots,x_\ell),\\[-1pt]
        &\qquad(y_1,\ldots,y_\ell),H,(e_1,\ldots,e_\ell))
    \end{aligned}}
  -/)
  (latexEnv := "paperfragment")]
inductive MergeSpec where
  | merge (oldVars newVars : List Var) (body : List Action) (res : List Expr)

/-- Each input tuple has one distinct parameter per output column. -/
def MergeSpec.BindersOk : MergeSpec → Nat → Prop
  | .merge oldVars newVars _ _, n =>
      oldVars.length = n ∧ newVars.length = n ∧ (oldVars ++ newVars).Nodup

instance (m : MergeSpec) (n : Nat) : Decidable (m.BindersOk n) := by
  cases m; unfold MergeSpec.BindersOk; infer_instance

/-- A function declaration: a constructor when `merge = none`, a merge function when not. -/
@[blueprint "def:declarations"
  (statement := /--
  \syntaxline{Declarations}{d ::= \kw{ctor}(k)\mid\kw{fun}(k,\ell,\mu)}
  -/)
  (latexEnv := "paperfragment")]
structure FnDecl where
  /-- The number of key columns. Read by `MergeStep`, which needs to know where a term's
  key ends and its value columns begin. -/
  arity : Nat
  /-- The number of value columns. One for a constructor. -/
  outArity : Nat
  /-- How collisions are resolved, or `none` for a constructor. -/
  merge : Option MergeSpec

/-- How many children a term recording an entry of this function carries: a constructor's
entry is `f(a…)`, a merge function's `f(a…, v…)`. -/
def FnDecl.entryWidth (d : FnDecl) : Nat :=
  if d.merge.isNone then d.arity else d.arity + d.outArity

/-- The declared functions. Undeclared names have no entry. -/
abbrev Signature := FnName → Option FnDecl

/-- How `f` resolves a collision; `none` for a constructor and an undeclared name alike. -/
def Signature.mergeOf (sig : Signature) (f : FnName) : Option MergeSpec :=
  (sig f).bind FnDecl.merge

/-- `f` is a **declared** constructor. An undeclared name is neither this nor a merge
function, and `Expr.eval` has no rule for it. -/
def Signature.IsCtor (sig : Signature) (f : FnName) : Prop :=
  ∃ d, sig f = some d ∧ d.merge = none

instance (sig : Signature) (f : FnName) : Decidable (sig.IsCtor f) :=
  decidable_of_iff (((sig f).map fun d => d.merge.isNone).getD false = true) (by
    unfold Signature.IsCtor
    cases h : sig f with
    | none => simp
    | some d => simp [Option.isNone_iff_eq_none])

/-- No declared function has a merge specification, which makes `MergeStep` vacuous. -/
def Signature.AllConstructors (sig : Signature) : Prop := ∀ f, sig.mergeOf f = none

/-! ### Variables and function names -/
mutual

/-- All variables occurring in `e`, deduplicated. -/
def Expr.vars : Expr → List Var
  | .lit _ => []
  | .var v => [v]
  | .app _ args => Expr.varsList args
  | .min a b => a.vars ∪ b.vars
  | .ite lhs rhs yes no => (Expr.varsList lhs ∪ Expr.varsList rhs) ∪ (yes.vars ∪ no.vars)

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
  | .min a b => a.fns ∪ b.fns
  | .ite lhs rhs yes no => (Expr.fnsList lhs ∪ Expr.fnsList rhs) ∪ (yes.fns ∪ no.fns)

def Expr.fnsList : List Expr → List FnName
  | [] => []
  | e :: es => e.fns ∪ Expr.fnsList es

end

def Pattern.vars : Pattern → List Var
  | .expr e => e.vars
  | .eq e₁ e₂ => e₁.vars ∪ e₂.vars

def Query.vars : Query → List Var
  | [] => []
  | p :: ps => p.vars ∪ Query.vars ps

/-- A top-level command. Initial facts use an empty-query rule followed by `run`. -/
@[blueprint "def:commands"
  (statement := /--
  \syntaxline{Commands}{\begin{aligned}[t]
    C &::= \kw{declare}\ f:d\mid\kw{rule}\ \rho\\[-1pt]
      &\phantom{::={}}\mid\kw{run}\ R\mid\kw{saturate}\ R\mid\kw{check}\ Q
    \end{aligned}}
  -/)
  (latexEnv := "paperfragment")]
inductive Cmd where
  | rule : Rule → Cmd
  /-- One round of a ruleset: egglog's `(run <ruleset> 1)`, which is `(repeat 1 (run
  <ruleset>))` (`egglog/src/ast/parse.rs:834-864`). -/
  | run : RulesetName → Cmd
  /-- Rounds of a ruleset until nothing changes: egglog's `(run-schedule (saturate
  <ruleset>))` (`egglog/src/ast/parse.rs:1073-1079`). -/
  | saturate : RulesetName → Cmd
  | decl : FnName → FnDecl → Cmd
  /-- Observe whether a query has a match. A failed check stops the program; a successful
  check changes no state. Checks are commands, never rule-head or merge-body actions. -/
  | check : Query → Cmd

@[blueprint "def:programs"
  (statement := /-- \syntaxline{Programs}{P ::= C_1;\ldots;C_n} -/)
  (latexEnv := "paperfragment")]
abbrev Program := List Cmd

/-! ### The constructor-only fragment -/

/-- `c` declares only constructors. -/
def Cmd.CtorDecl : Cmd → Prop
  | .decl _ d => d.merge = none
  | _ => True

/-- Every declaration in the program declares a constructor, so every state it reaches is
`Signature.AllConstructors`. -/
def Program.CtorDecls (p : Program) : Prop := ∀ c ∈ p, c.CtorDecl

/-! ### The terminating fragment -/

/-- `c` is not a saturating run. A ruleset that keeps adding terms has no fixpoint, so
`Cmd.saturate` is the one command that may fail to reach a state at all. -/
def Cmd.NoSaturate : Cmd → Prop
  | .saturate _ => False
  | _ => True

/-- The program bounds its own running: every round count is written down. -/
def Program.NoSaturate (p : Program) : Prop := ∀ c ∈ p, c.NoSaturate

end Egglog
