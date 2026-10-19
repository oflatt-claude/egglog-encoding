import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

The paper evaluator builds terms without consulting a signature. The checked entry
points agree with it on well-formed expressions (see Proofs/Presentation.lean).
-/

namespace Egglog
mutual

/-- Structural evaluation; declarations and row nesting are checked separately. -/
@[blueprint "def:evaluation"
  (statement := /--
  \[
  \begin{array}{@{}c@{\qquad}c@{\qquad}c@{\qquad}c@{}}
    \sigma:\mathit{Var}\rightharpoonup\mathit{Term}
      &\eval{f(e_1,\ldots,e_n)}
      &\eval{\min(e_1,e_2)}
      &\eval{\kw{if}\ \bar e=\bar e'\ \kw{then}\ a\ \kw{else}\ b}\\[.6em]
    \eval x=\sigma(x)
      &{}=f(\eval{e_1},\ldots,\eval{e_n})
      &{}=\min_{\prec}(\eval{e_1},\eval{e_2})
      &{}=\begin{cases}\eval a&\eval{\bar e}=\eval{\bar e'}\\
        \eval b&\eval{\bar e}\ne\eval{\bar e'}\end{cases}
  \end{array}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Expr.evaluate : Expr → Env → Option Term
  | .lit l, _ => some (.lit l)
  | .var v, σ => Env.lookup v σ
  | .app f args, σ => (Expr.evaluateList args σ).map (Term.app f)
  | .min a b, σ => (a.evaluate σ).bind fun x => (b.evaluate σ).map (Term.least x)
  | .ite lhs rhs yes no, σ => do
      let xs ← Expr.evaluateList lhs σ
      let ys ← Expr.evaluateList rhs σ
      if xs = ys then yes.evaluate σ else no.evaluate σ

def Expr.evaluateList : List Expr → Env → Option (List Term)
  | [], _ => some []
  | e :: es, σ => (e.evaluate σ).bind fun t => (Expr.evaluateList es σ).map (t :: ·)

end

mutual

/-- Evaluate a constructor expression, checking its applied names. -/
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

/-- The one equation an action asserts. Actions read only the signature and bindings,
never the store, so an action sequence denotes a set of equations.

A `union` on a literal is stuck. egglog rejects it in its type checker — `union` wants an
eq-sort and `i64` is not one (`TypeError::NonEqsortUnion`) — and this untyped model cannot
see it until the operands are values. Asserting it instead would cost
`Database.LitsIsolated`. -/
def Action.write (sig : Signature) (σ : Env) : Action → Option (Term × Term)
  | .expr e => (e.evalAtom sig σ).map fun t => (t, t)
  | .union e₁ e₂ =>
      (e₁.eval sig σ).bind fun t₁ =>
        (e₂.eval sig σ).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some (t₁, t₂)

/-- The equations asserted by an action sequence, defined when every action's is. -/
@[blueprint "def:actions"
  (statement := /--
\[
  \begin{gathered}
  \writes e=\{(\eval e,\eval e)\}\qquad
  \writes{\kw{union}(e_1,e_2)}=\{(\eval{e_1},\eval{e_2})\}\\
  \writes{h_1;\ldots;h_n}=\bigcup_{i=1}^n\writes{h_i}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Action.writes (sig : Signature) (σ : Env) : List Action → Option (Set (Term × Term))
  | [] => some ∅
  | a :: as => (a.write sig σ).bind fun p => (Action.writes sig σ as).map (insert p)

end Egglog
