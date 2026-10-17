import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

Expressions build constructor terms; complete atoms may also describe function entries.
Evaluation is partial for unbound variables, undeclared heads, nested function syntax,
and unions on literals. Rule firing and merging are specified in `Spec/Step.lean`.
-/

namespace Egglog
mutual

/-- Build the ground term an expression denotes. The signature is read for one thing only —
whether a name **builds, reads, or means nothing**. -/
@[blueprint "def:evaluation"
  (statement := /--
  \[
  \begin{gathered}
  \sigma:\mathit{Var}\rightharpoonup\mathit{Term}\qquad\eval x=\sigma(x)\\
  \eval{c(\bar e)}=c(\eval{\bar e})\quad(c\in\mathit{Ctor}_{\Sigma})\qquad
  \eval{\min(e_1,e_2)}=\min_{\prec}(\eval{e_1},\eval{e_2})\\
  \aval{f(\bar e;\bar e')}=f(\eval{\bar e};\eval{\bar e'})\quad(f\in\mathit{Fun}_{\Sigma})
  \qquad \aval e=\eval e\quad(e\text{ not a function atom or conditional})\\
  \eval{\kw{if}\ \bar e=\bar e'\ \kw{then}\ a\ \kw{else}\ b}=
    \begin{cases}\eval a&\eval{\bar e}=\eval{\bar e'}\\
    \eval b&\eval{\bar e}\ne\eval{\bar e'}\end{cases}\quad
  \text{and likewise for }\aval{\kw{if}\ \cdots}.
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Expr.eval (sig : Signature) : Expr → Env → Option Term
  | .lit l, _ => some (.lit l)
  | .var v, σ => Env.lookup v σ
  | .app f args, σ =>
      if sig.IsCtor f then (Expr.evalList sig args σ).map (Term.app f) else none
  | .min a b, σ => (a.eval sig σ).bind fun x => (b.eval sig σ).map (Term.least x)
  | .ite lhs rhs yes no, σ => do
      let xs ← Expr.evalList sig lhs σ
      let ys ← Expr.evalList sig rhs σ
      if xs = ys then yes.eval sig σ else no.eval sig σ

/-- `Expr.eval` over an argument list, failing if any argument does. -/
def Expr.evalList (sig : Signature) : List Expr → Env → Option (List Term)
  | [], _ => some []
  | e :: es, σ => (e.eval sig σ).bind fun t => (Expr.evalList sig es σ).map (t :: ·)

end

/-- Interpret a root application as a table entry. The declaration determines which
columns are keys and which are outputs. Constructor applications and `min` are not entries. -/
def Expr.entry (sig : Signature) : Expr → Option (FnName × List Expr × List Expr)
  | .app f cols =>
      (sig f).bind fun d =>
        if d.merge.isSome then some (f, cols.take d.arity, cols.drop d.arity) else none
  | _ => none

/-- Evaluate a complete atom; a selected branch may itself be a function atom. -/
def Expr.evalAtom (sig : Signature) : Expr → Env → Option Term
  | .app f cols, σ =>
      (sig f).bind fun d =>
        if d.merge = none ∨ cols.length = d.entryWidth then
          (Expr.evalList sig cols σ).map (Term.app f)
        else none
  | .ite lhs rhs yes no, σ => do
      let xs ← Expr.evalList sig lhs σ
      let ys ← Expr.evalList sig rhs σ
      if xs = ys then yes.evalAtom sig σ else no.evalAtom sig σ
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

/-- Execute the merge body, then evaluate its output tuple. -/
def evalMerge (db : Database) (body : List Action) (res : List Expr) :
    Option (Database × List Term) :=
  (evalActions db body).bind fun d => (Expr.evalList d.sig res d.env).map (d, ·)

end Egglog
