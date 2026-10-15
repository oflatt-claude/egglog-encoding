import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

Value expressions build ground terms; complete atoms may also describe function entries.
Actions add constructor equations or insert function entries. Evaluation returns `none`
for unbound variables, undeclared heads, table applications in value positions, and
unions on literals. Atom columns use value evaluation. Rule firing and merge closure
are specified separately in `Spec/Step.lean`.
-/

namespace Egglog
mutual

/-- Build the ground term an expression denotes. The signature is read for one thing only —
whether a name **builds, reads, or means nothing**. -/
def Expr.eval (sig : Signature) : Expr → Env → Option Term
  | .lit l, _ => some (.lit l)
  | .var v, σ => (Env.lookup v σ).filter (Term.isValue sig)
  | .app f args, σ =>
      if sig.IsCtor f then (Expr.evalList sig args σ).map (Term.app f) else none
  | .min a b, σ => (a.eval sig σ).bind fun x => (b.eval sig σ).map (Term.least x)

/-- `Expr.eval` over an argument list, failing if any argument does. -/
def Expr.evalList (sig : Signature) : List Expr → Env → Option (List Term)
  | [], _ => some []
  | e :: es, σ => (e.eval sig σ).bind fun t => (Expr.evalList sig es σ).map (t :: ·)

end

/-- Interpret a root application as a table entry. The declaration determines which
columns are keys and which are outputs. Constructor applications and `min` are values. -/
def Expr.entry (sig : Signature) : Expr → Option (FnName × List Expr × List Expr)
  | .app f cols =>
      (sig f).bind fun d =>
        if d.merge.isSome then some (f, cols.take d.arity, cols.drop d.arity) else none
  | _ => none

/-- Evaluate a complete query or action expression. An entry's columns are evaluated as
values, so entry applications cannot occur as children. -/
def Expr.evalAtom (sig : Signature) : Expr → Env → Option Term
  | .app f cols, σ =>
      (sig f).bind fun d =>
        if d.merge = none ∨ cols.length = d.entryWidth then
          (Expr.evalList sig cols σ).map (Term.app f)
        else none
  | e, σ => e.eval sig σ

/-- Run one action in the database's evaluation context. Actions never bind variables.
An entry atom inserts its row; merging later resolves collisions with other rows.

A `union` on a literal is stuck. egglog rejects it in its type checker — `union` wants an
eq-sort and `i64` is not one (`TypeError::NonEqsortUnion`) — and this untyped model cannot
see it until the operands are values. Asserting it instead would cost
`Database.LitsIsolated`. -/
def evalAction (db : Database) : Action → Option Database
  | .expr e =>
      (e.evalAtom db.sig db.env).map fun t => db.addTerm t
  | .union e₁ e₂ =>
      (e₁.eval db.sig db.env).bind fun t₁ =>
        (e₂.eval db.sig db.env).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some (db.addEq t₁ t₂)

/-- Run the actions in order, threading the database through. -/
def evalActions (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction db a).bind fun db' => evalActions db' as

/-- Run a rule's actions under its query substitution, then restore the surrounding context.
For program executions the surrounding environment is empty (`ProgramStep.env`). -/
def evalLocalActions (db : Database) (as : List Action) (σ : Env) : Option Database :=
  (evalActions { db with env := σ ++ db.env } as).map fun db' =>
    { db' with env := db.env, rules := db.rules }

end Egglog
