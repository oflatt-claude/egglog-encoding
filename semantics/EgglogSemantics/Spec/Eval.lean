import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

An expression denotes a ground term; an action turns a database into a database.

Evaluation is partial, in four ways, all `none`: an unbound variable; an application of an
**undeclared** name, which is egglog's declare-before-use; an application of a declared
merge function, which is a *lookup* and so a query atom (`Pattern.values`) rather than an
expression; and a primitive given operands of the wrong sort, which this model has no
sorts to reject statically. `Scope.lean`'s `Scoped` rules out the first and its
`Evaluable` the other three.

Actions only ever add terms and equalities — `evalAction_contained`.
-/

namespace Egglog
mutual

/-- Build the ground term an expression denotes.

The signature is read for one thing only — whether a name **builds, computes, reads, or
means nothing**. egglog consults its primitive table first, so a reserved name shadows a
user function. That is why the evaluator needs a `Signature` and nothing else of the
database: reading is confined to `Pattern.values`. -/
def Expr.eval (sig : Signature) : Expr → Env → Option Term
  | .lit l, _ => some (.lit l)
  | .var v, σ => Env.lookup v σ
  | .app f args, σ =>
      match Prim.ofName f with
      | some p => (Expr.evalList sig args σ).bind p.apply
      | none =>
          if sig.IsCtor f then (Expr.evalList sig args σ).map (Term.app f) else none

/-- `Expr.eval` over an argument list, failing if any argument does. -/
def Expr.evalList (sig : Signature) : List Expr → Env → Option (List Term)
  | [], _ => some []
  | e :: es, σ => (e.eval sig σ).bind fun t => (Expr.evalList sig es σ).map (t :: ·)

end

/-- Run one action against the database.

A `let` binds in the environment the database carries, so at top level it adds a global
and inside a rule a rule-local binding; `evalLocalActions` makes the second case local by
restoring the caller's environment afterwards.

A `set` only *records* its entry: a collision with a congruent key is resolved by
`MergeStep`, which leaves both entries it merged in place. -/
def evalAction (db : Database) : Action → Option Database
  | .expr e => (e.eval db.sig db.env).map fun t => db.addTerm t
  | .letBind v e => (e.eval db.sig db.env).map fun t =>
      { db.addTerm t with env := (v, t) :: db.env }
  | .union e₁ e₂ =>
      (e₁.eval db.sig db.env).bind fun t₁ =>
        (e₂.eval db.sig db.env).map fun t₂ => db.addEq t₁ t₂
  | .set f args out =>
      (Expr.evalList db.sig args db.env).bind fun as =>
        (Expr.evalList db.sig out db.env).map fun vs => db.addTerm (.app f (as ++ vs))

/-- Run the actions in order, threading the database through. -/
def evalActions (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction db a).bind fun db' => evalActions db' as

/-- Run a rule's actions with `σ` in scope, then forget the resulting environment.

`σ` is appended *after* the globals, so a globally bound variable shadows a substitution
for the same name — which never arises, since a pattern's free variables exclude the
globals (`Expr.freeVars`). -/
def evalLocalActions (db : Database) (as : List Action) (σ : Env) : Option Database :=
  (evalActions { db with env := db.env ++ σ } as).map fun db' =>
    { db' with env := db.env, rules := db.rules }

end Egglog
