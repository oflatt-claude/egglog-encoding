import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

An expression denotes a ground term; an action turns a database into a database. This file
is `Option`-valued: what a command computes, deterministically. The nondeterminism —
merge closure, rule firing — is `Spec/Step.lean`. Evaluation is partial in five ways, all
`none`: an unbound variable, an **undeclared** name, a declared merge function — which is a
*lookup*, and so the query atom `Pattern.values` rather than an expression — a
primitive given operands of the wrong sort, and a `union` on a literal. Actions only ever
add equations.
-/

namespace Egglog
mutual

/-- Build the ground term an expression denotes. The signature is read for one thing only —
whether a name **builds, computes, reads, or means nothing** — and the primitive table is
consulted first, so a reserved name shadows a user function. -/
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

/-- Run one action against the database. A `let` binds in the environment the database
carries, a global at top level and a rule-local binding inside a rule. A `set` only
*records* its entry; a collision on a congruent key is resolved by `MergeStep`.

A `union` on a literal is stuck. egglog rejects it in its type checker — `union` wants an
eq-sort and `i64` is not one (`TypeError::NonEqsortUnion`) — and this untyped model cannot
see it until the operands are values. Asserting it instead would cost
`Database.LitsIsolated`. -/
def evalAction (db : Database) : Action → Option Database
  | .expr e => (e.eval db.sig db.env).map fun t => db.addTerm t
  | .letBind v e => (e.eval db.sig db.env).map fun t =>
      { db.addTerm t with env := (v, t) :: db.env }
  | .union e₁ e₂ =>
      (e₁.eval db.sig db.env).bind fun t₁ =>
        (e₂.eval db.sig db.env).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some (db.addEq t₁ t₂)
  | .set f args out =>
      (Expr.evalList db.sig args db.env).bind fun as =>
        (Expr.evalList db.sig out db.env).map fun vs => db.addTerm (.app f (as ++ vs))

/-- **Run one top-level action.** A top-level `let` declares a *global*, and a global's name
must be new: it is stuck where the environment already binds the name. Only at the top level —
a rule-local `let` binds in the environment `evalLocalActions` builds and is gone when the
firing ends, so `evalAction` is where a `let` binds and this is where a global is declared.

egglog runs the same check. `remove_globals` turns a top-level `let` into a function
declaration, and `Names::check_shadowing` puts that declaration through `Names::check`
(`egglog/src/ast/check_shadowing.rs:49-50`), which raises `Error::Shadowing` — "Shadowing is
not allowed" — on a name it has already seen (`:11-12`). -/
def evalTopAction (db : Database) : Action → Option Database
  | .letBind v e =>
      if (Env.lookup v db.env).isSome then none else evalAction db (.letBind v e)
  | a => evalAction db a

/-- A top-level action that ran is an action that ran. -/
theorem evalAction_of_top {db db' : Database} {a : Action}
    (h : evalTopAction db a = some db') : evalAction db a = some db' := by
  cases a with
  | letBind v e =>
      rw [evalTopAction] at h
      split at h
      · exact absurd h (by simp)
      · exact h
  | _ => exact h

/-- Away from a `let`, a top-level action is an action. -/
@[simp] theorem evalTopAction_expr (db : Database) (e : Expr) :
    evalTopAction db (.expr e) = evalAction db (.expr e) := rfl

@[simp] theorem evalTopAction_union (db : Database) (e₁ e₂ : Expr) :
    evalTopAction db (.union e₁ e₂) = evalAction db (.union e₁ e₂) := rfl

@[simp] theorem evalTopAction_set (db : Database) (f : FnName) (args out : List Expr) :
    evalTopAction db (.set f args out) = evalAction db (.set f args out) := rfl

/-- A `let` on a name the environment does not hold is an ordinary `let`. -/
theorem evalTopAction_letBind_of_fresh {db : Database} {v : Var} {e : Expr}
    (h : Env.lookup v db.env = none) :
    evalTopAction db (.letBind v e) = evalAction db (.letBind v e) := by
  rw [evalTopAction, if_neg (by simp [h])]

/-- The freshness guard reads the environment alone, so a top-level action that ran at one
state runs at any state with the same environment where the action itself does. -/
theorem evalTopAction_of_env {A C e E : Database} {a : Action} (henv : A.env = C.env)
    (hA : evalTopAction A a = some e) (hC : evalAction C a = some E) :
    evalTopAction C a = some E := by
  cases a with
  | letBind v e' =>
      rw [evalTopAction] at hA ⊢
      split at hA
      · exact absurd hA (by simp)
      · rename_i hne
        rw [if_neg (by rw [← henv]; exact hne)]
        exact hC
  | expr e' => exact hC
  | union e₁ e₂ => exact hC
  | set f args out => exact hC

/-- Run the actions in order, threading the database through. -/
def evalActions (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction db a).bind fun db' => evalActions db' as

/-- Run a rule's actions with `σ` in scope, then forget the resulting environment. `σ` is
appended *after* the globals, so a global shadows a substitution for the same name. -/
def evalLocalActions (db : Database) (as : List Action) (σ : Env) : Option Database :=
  (evalActions { db with env := db.env ++ σ } as).map fun db' =>
    { db' with env := db.env, rules := db.rules }

end Egglog
