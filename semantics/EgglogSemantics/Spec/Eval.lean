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

/-- The one equation an action asserts. Actions read only the signature and bindings,
never the store, so a head denotes a set of equations.

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

/-- The equations a head asserts, defined only when every action's is. -/
@[blueprint "def:actions"
  (statement := /--
\[
  \writes e=(\aval e,\aval e)\qquad
  \writes{\kw{union}(e_1,e_2)}=(\eval{e_1},\eval{e_2})\qquad
  \writes{h_1;\ldots;h_n}=\{\writes{h_1},\ldots,\writes{h_n}\}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Action.writes (sig : Signature) (σ : Env) : List Action → Option (Set (Term × Term))
  | [] => some ∅
  | a :: as => (a.write sig σ).bind fun p => (Action.writes sig σ as).map (insert p)

end Egglog
