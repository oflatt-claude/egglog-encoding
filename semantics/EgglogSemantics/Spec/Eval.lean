import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

Ports the Redex `Eval-Expr`, `Eval-Action`, `Eval-Global-Actions` and
`Eval-Local-Actions`.

Evaluation is partial, in three ways. `Eval-Expr` has no rule for an unbound variable;
an application of a non-constructor is a *lookup*, which is a query atom
(`Pattern.values`) and never an expression; and a primitive may be given operands of the
wrong sort, which is egglog's own `i64` type error and which this model has no sort
discipline to reject statically. All three are `none`. `Scope.lean`'s `Scoped` rules out
the first and its `Evaluable` the other two.

Actions only ever add terms, rows and equalities, which is `evalAction_contained` — the
fact the Redex documentation appeals to when it says the order of actions does not
matter.
-/

namespace Egglog
mutual

/-- The Redex `Eval-Expr`: build the ground term an expression denotes.

The signature is read for one thing only — whether a name **builds or computes or
reads**. egglog consults its primitive table first, so a reserved name shadows a user
function; a constructor builds the application; and anything else is a lookup, which has
no rule here at all. That is why the evaluator needs a `Signature` and nothing else of
the database: reading is confined to `Pattern.values`.

Because only constructor applications ever end up inside a `Term`, `Term.ctorRows` needs
no signature. -/
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

/-- The Redex `Eval-Action`, plus `set`.

A `let` binds in the environment the database carries, so at top level it adds a
global and inside a rule it adds a rule-local binding; `evalLocalActions` is what
makes the second case local by restoring the caller's environment afterwards.

`set` is the one case the Redex has no rule for. It only ever adds: a collision with a
congruent key is resolved by `MCong.fd` or by `MergeStep`, neither of which removes the
row it wrote. -/
def evalAction (db : Database) : Action → Option Database
  | .expr e => (e.eval db.sig db.env).map fun t => db.addTerm t
  | .letBind v e => (e.eval db.sig db.env).map fun t =>
      { db.addTerm t with env := (v, t) :: db.env }
  | .union e₁ e₂ =>
      (e₁.eval db.sig db.env).bind fun t₁ =>
        (e₂.eval db.sig db.env).map fun t₂ => db.addEq t₁ t₂
  | .set f args out =>
      (Expr.evalList db.sig args db.env).bind fun as =>
        (Expr.evalList db.sig out db.env).map fun vs => db.addRow f as vs

/-- The Redex `Eval-Global-Actions`: run the actions in order. -/
def evalActions (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction db a).bind fun db' => evalActions db' as

/-- The Redex `Eval-Local-Actions`: run a rule's actions with `σ` in scope, then
forget the resulting environment.

`σ` is appended *after* the globals, matching `Env-Union Env_1 Env_local`, so a
globally bound variable shadows a substitution for the same name. That never
happens in practice because a pattern's free variables exclude the globals
(`Expr.freeVars`), but the order is the Redex's. -/
def evalLocalActions (db : Database) (as : List Action) (σ : Env) : Option Database :=
  (evalActions { db with env := db.env ++ σ } as).map fun db' =>
    { db' with env := db.env, rules := db.rules }

end Egglog
