import EgglogSemantics.Spec.Step

/-!
# The proof checker

`CHECKER.md`'s constructor-only fragment: five justifications, `Bool`-valued, reading the
**source** program and nothing else — no database, no e-graph, no rows.

A proof is an ordinary `Term`:

```
@Fiat                 arity 0   a top-level action asserted the claim
@Sym    (p)           arity 1
@Trans  (p, q)        arity 2
@Congr  (p₁ … p_k)    arity k   congruence at a k-ary constructor, one proof per child
@Rule_i (p₁ … p_n)    arity n   rule i fired, one proof per premise
```

It carries no proposition; the row it sits in does, so `Checks P pf a b` is asked with both
endpoints. `Trans`'s middle term and `Rule_i`'s substitution are the two things neither the
node nor the claim supplies, and `Proof.props` is what recovers them: it computes the
finite set of propositions a proof admits under an optional constraint on each endpoint,
which is `checkFactMatchesProposition` and `computeRuleSubstitution` run as one pass.

**Incompleteness, exactly.** `props` needs an endpoint to synthesise a `@Congr` — the node
names no head — so a `@Congr` standing as a rule premise whose body fact has neither side
ground under the substitution built so far is rejected. A body fact reading a merge
function's row is rejected for the same reason, `Expr.eval` having no case for one. Both are
refusals, so the checker stays sound; `Proof.Sound` is the statement that says so.
-/

namespace Egglog
namespace Proof

/-! ### The vocabulary -/

def fiatName : FnName := "@Fiat"
def symName : FnName := "@Sym"
def transName : FnName := "@Trans"
def congrName : FnName := "@Congr"

/-- `@Rule_i` names the program's `i`th rule. -/
def rulePrefix : String := "@Rule_"

/-- The rule a head names, if it names one. -/
def ruleIndex (f : FnName) : Option Nat :=
  if rulePrefix.isPrefixOf f then (f.drop rulePrefix.length).toNat? else none

/-! ### What the checker reads out of the program -/

/-- The source program as the checker sees it: declarations, the globals and equalities the
top-level actions assert, and the rules in program order. -/
structure Ctx where
  sig : Signature
  /-- Globals bound by a top-level `let`, innermost first. -/
  env : Env
  /-- The equalities the top-level actions assert. -/
  eqs : List (Term × Term)
  /-- The rules in program order; `@Rule_i` indexes this. -/
  rules : List Rule

/-- One reflexive equality per subterm, which is what building a term asserts. -/
def reflEqs (t : Term) : List (Term × Term) := t.subtermList.map fun s => (s, s)

/-- `Spec/Eval.lean`'s `evalAction` with the asserted equalities as the accumulator:
`union` contributes its pair both ways, everything built contributes `reflEqs`. -/
def procAction (sig : Signature) (σ : Env) : Action → Option (Env × List (Term × Term))
  | .expr e => (e.eval sig σ).map fun t => (σ, reflEqs t)
  | .letBind v e => (e.eval sig σ).map fun t => ((v, t) :: σ, reflEqs t)
  | .union e₁ e₂ =>
      (e₁.eval sig σ).bind fun t₁ => (e₂.eval sig σ).bind fun t₂ =>
        if t₁.isLit || t₂.isLit then none
        else some (σ, (t₁, t₂) :: (t₂, t₁) :: (reflEqs t₁ ++ reflEqs t₂))
  | .set f args out =>
      (Expr.evalList sig args σ).bind fun as =>
        (Expr.evalList sig out σ).map fun vs => (σ, reflEqs (.app f (as ++ vs)))

/-- `procAction` in order, threading the environment. -/
def procActions (sig : Signature) (σ : Env) : List Action → Option (Env × List (Term × Term))
  | [] => some (σ, [])
  | a :: as => (procAction sig σ a).bind fun r =>
      (procActions sig r.1 as).map fun r' => (r'.1, r.2 ++ r'.2)

/-- The equalities a rule head derives under `σ`. -/
def headEqs (sig : Signature) (as : List Action) (σ : Env) : List (Term × Term) :=
  ((procActions sig σ as).map Prod.snd).getD []

def Ctx.empty : Ctx := { sig := fun _ => none, env := [], eqs := [], rules := [] }

/-- One command. An action that does not evaluate contributes nothing: the program is stuck
there, so no state is reachable. -/
def Ctx.step (C : Ctx) : Cmd → Ctx
  | .decl f d => { C with sig := Function.update C.sig f (some d) }
  | .rule r => { C with rules := C.rules ++ [r] }
  | .action a =>
      match procAction C.sig C.env a with
      | some (σ, es) => { C with env := σ, eqs := C.eqs ++ es }
      | none => C
  | .run _ => C
  | .saturate _ => C

def ctxOf (P : Program) : Ctx := P.foldl Ctx.step Ctx.empty

/-! ### Matching a body fact against a premise's proposition -/

mutual

/-- Match `e` against the ground term `t`, extending `σ`. A new binding is appended, so the
globals `σ` starts from stay in front and shadow rule variables, as in `evalLocalActions`. -/
def unifyExpr (sig : Signature) : Expr → Term → Env → Option Env
  | .lit l, .lit l', σ => if l = l' then some σ else none
  | .lit _, .app _ _, _ => none
  | .var v, t, σ =>
      match Env.lookup v σ with
      | some t' => if t = t' then some σ else none
      | none => some (σ ++ [(v, t)])
  | .app f args, t, σ =>
      if (Prim.ofName f).isSome then
        if Expr.eval sig (.app f args) σ = some t then some σ else none
      else
        match t with
        | .app g ts => if f = g ∧ sig.IsCtor f then unifyExprList sig args ts σ else none
        | .lit _ => none

def unifyExprList (sig : Signature) : List Expr → List Term → Env → Option Env
  | [], [], σ => some σ
  | e :: es, t :: ts, σ => (unifyExpr sig e t σ).bind (unifyExprList sig es ts)
  | _, _, _ => none

end

/-- The proposition a body fact states, as a pair of expressions. A pattern and a row atom
state a reflexive one. -/
def factProp : Pattern → Expr × Expr
  | .expr e => (e, e)
  | .eq e₁ e₂ => (e₁, e₂)
  | .values vs f as => (.app f (as ++ vs), .app f (as ++ vs))

/-- Extend `σ` so that `pr` is what the body fact `q` states. -/
def unifyFact (sig : Signature) (q : Pattern) (σ : Env) (pr : Term × Term) : Option Env :=
  (unifyExpr sig (factProp q).1 pr.1 σ).bind (unifyExpr sig (factProp q).2 pr.2)

/-! ### The checker -/

mutual

/-- The measure `props` recurses on. -/
def size : Term → Nat
  | .lit _ => 1
  | .app _ as => 1 + sizeL as

/-- `size` over an argument list, one extra per element so a child is strictly smaller. -/
def sizeL : List Term → Nat
  | [] => 0
  | a :: as => 1 + size a + sizeL as

end

/-- A proposition passes the endpoints the caller fixed. -/
def endsOk (ma mb : Option Term) (p : Term × Term) : Bool :=
  (match ma with | some a => decide (p.1 = a) | none => true) &&
  (match mb with | some b => decide (p.2 = b) | none => true)

mutual

/-- The propositions `pf` proves whose left endpoint is `ma` and right endpoint is `mb`,
where those are given. -/
def props (C : Ctx) : Term → Option Term → Option Term → List (Term × Term)
  | .lit _, _, _ => []
  | .app f ps, ma, mb =>
      if f = fiatName then
        if ps.isEmpty then C.eqs.filter (endsOk ma mb) else []
      else if f = symName then
        match ps with
        | [p] => (props C p mb ma).map Prod.swap
        | _ => []
      else if f = transName then
        match ps with
        | [p, q] =>
            if ma.isSome then
              (props C p ma none).flatMap fun r =>
                (props C q (some r.2) mb).map fun r' => (r.1, r'.2)
            else
              (props C q none mb).flatMap fun r' =>
                (props C p ma (some r'.1)).map fun r => (r.1, r'.2)
        | _ => []
      else if f = congrName then
        match ma, mb with
        | some (.app g as), some (.app h bs) =>
            if g = h ∧ C.sig.IsCtor g ∧ congrOk C ps as bs then [(.app g as, .app g bs)]
            else []
        | some (.app g as), none =>
            if C.sig.IsCtor g then (congrRhs C ps as).map fun bs => (.app g as, .app g bs)
            else []
        | none, some (.app h bs) =>
            if C.sig.IsCtor h then (congrLhs C ps bs).map fun as => (.app h as, .app h bs)
            else []
        | _, _ => []
      else
        match ruleIndex f with
        | none => []
        | some i =>
            match C.rules[i]? with
            | none => []
            | some r =>
                if ps.length = r.query.length then
                  (ruleSubsts C ps r.query [C.env]).flatMap fun σ =>
                    (headEqs C.sig r.actions σ).filter (endsOk ma mb)
                else []
  termination_by pf => size pf
  decreasing_by all_goals (simp [size, sizeL]; try omega)

/-- Both endpoints known: every child proves its own argument pair. -/
def congrOk (C : Ctx) : List Term → List Term → List Term → Bool
  | [], [], [] => true
  | p :: ps, a :: as, b :: bs =>
      !(props C p (some a) (some b)).isEmpty && congrOk C ps as bs
  | _, _, _ => false
  termination_by ps => sizeL ps
  decreasing_by all_goals (simp [sizeL]; try omega)

/-- Left endpoint known: the right-hand argument lists the children admit. -/
def congrRhs (C : Ctx) : List Term → List Term → List (List Term)
  | [], [] => [[]]
  | p :: ps, a :: as =>
      (props C p (some a) none).flatMap fun r => (congrRhs C ps as).map (r.2 :: ·)
  | _, _ => []
  termination_by ps => sizeL ps
  decreasing_by all_goals (simp [sizeL]; try omega)

/-- Right endpoint known: the left-hand argument lists the children admit. -/
def congrLhs (C : Ctx) : List Term → List Term → List (List Term)
  | [], [] => [[]]
  | p :: ps, b :: bs =>
      (props C p none (some b)).flatMap fun r => (congrLhs C ps bs).map (r.1 :: ·)
  | _, _ => []
  termination_by ps => sizeL ps
  decreasing_by all_goals (simp [sizeL]; try omega)

/-- The substitutions the premises admit, one body fact at a time. -/
def ruleSubsts (C : Ctx) : List Term → Query → List Env → List Env
  | [], [], σs => σs
  | p :: ps, q :: qs, σs =>
      ruleSubsts C ps qs (σs.flatMap fun σ =>
        -- Each side anchors the premise when `σ` already grounds it.
        (props C p ((factProp q).1.eval C.sig σ)
            ((factProp q).2.eval C.sig σ)).filterMap (unifyFact C.sig q σ))
  | _, _, _ => []
  termination_by ps => sizeL ps
  decreasing_by all_goals (simp [sizeL]; try omega)

end

/-- **`pf` justifies `a = b` in the source program `P`.** -/
def Checks (P : Program) (pf : Term) (a b : Term) : Bool :=
  (props (ctxOf P) pf (some a) (some b)).any fun p => decide (p = (a, b))

/-! ### Soundness

Stated, not proved. `Cong.le` is the induction it would go by; each case names what the
checker does not itself witness.

* `Fiat` reads the top-level actions of `P`, so their equalities have to be in `db.eqs` —
  `ProgramStep Database.empty P db`.
* `Rule_i` checks that the head derives the claim under a substitution its premises admit.
  Deriving it is not asserting it: the rule has to have fired, which is `RunSaturated`. The
  premises give `Cong db` on each body fact, and `Cong.mem_of` turns each into the witness
  `Matches` wants; `ValidEnv`'s `Perm` clause is the remaining gap.
* `Congr` at `f(as) = f(bs)` needs both applications present, which `Cong.congr` demands and
  a k-ary node does not witness — hence the endpoint hypotheses, from which `WF.subtermClosed`
  reaches the children. `Trans`'s middle term has no such source.

Without `RunSaturated` the statement is false: a program whose rule is never `run` reaches
states in which the head's equalities are absent and `Checks` still accepts the `@Rule_i`. -/
/-- **Checker soundness at `db`**: every claim the checker accepts is derivable there. -/
def Sound (P : Program) (db : Database) : Prop :=
  ∀ pf a b, a ∈ db.terms → b ∈ db.terms → Checks P pf a b = true → Cong db a b

/-- `Sound` at every state `P` reaches in which its rules have saturated. -/
def SoundAt (P : Program) : Prop :=
  ∀ db, ProgramStep Database.empty P db → db.WF → (∀ R, RunSaturated R db) → Sound P db

end Proof

/-! ## Witnesses

What the checker accepts and, next to each, what it refuses. The program is
constructor-only: four constants, a unary `F`, two `union`s, one built term, one rule. -/

section Witnesses
open Proof
set_option linter.hashCommand false

private def cnst (n : Nat) : FnDecl := { arity := n, outArity := 1, merge := none }

private def eA : Expr := .app "A" []
private def eB : Expr := .app "B" []
private def eC : Expr := .app "C" []
private def eD : Expr := .app "D" []
private def tA : Term := .app "A" []
private def tB : Term := .app "B" []
private def tC : Term := .app "C" []
private def tD : Term := .app "D" []
private def tF (t : Term) : Term := .app "F" [t]

/-- `(A) = (B)`, `(C) = (D)`, the term `(F (A))`, and a rule rewriting any `(F y)` to
`(F (C))`. -/
private def prog : Program :=
  [.decl "A" (cnst 0), .decl "B" (cnst 0), .decl "C" (cnst 0), .decl "D" (cnst 0),
   .decl "F" (cnst 1),
   .action (.union eA eB),
   .action (.union eC eD),
   .action (.expr (.app "F" [eA])),
   .rule ⟨[.eq (.var "x") (.app "F" [.var "y"])],
          [.union (.var "x") (.app "F" [eC])], ""⟩,
   .run ""]

private def pFiat : Term := .app "@Fiat" []
private def pSym (p : Term) : Term := .app "@Sym" [p]
private def pTrans (p q : Term) : Term := .app "@Trans" [p, q]
private def pCongr (ps : List Term) : Term := .app "@Congr" ps
private def pRule (i : Nat) (ps : List Term) : Term := .app ("@Rule_" ++ toString i) ps

/-! ### It says no

Each rejection is paired with the acceptance it differs from, so the refusal is the claim's
and not the proof term's. -/

/-! A `@Trans` whose endpoints do not meet: nothing the left proves ends where anything the
right proves begins. The same node proves `(A) = (B)`. -/
#guard !Checks prog (pTrans pFiat pFiat) tA tD
#guard Checks prog (pTrans pFiat pFiat) tA tB

/-! A `@Fiat` for an equation no action asserts. The same node proves `(A) = (B)`. -/
#guard !Checks prog pFiat tA tC
#guard Checks prog pFiat tA tB

/-! A `@Rule_0` whose claim the head does not derive: the head unions `x` with `(F (C))`,
never with `(F (D))` though `(C) = (D)` is asserted, and the only substitution the premise
admits binds `x` to `(F (A))`. -/
#guard !Checks prog (pRule 0 [pFiat]) (tF tA) (tF tD)
#guard !Checks prog (pRule 0 [pFiat]) (tF tB) (tF tC)
#guard Checks prog (pRule 0 [pFiat]) (tF tA) (tF tC)

/-! A `@Congr` whose child does not prove the argument pair, one at mismatched heads, and
one at a head the program never declared. -/
#guard !Checks prog (pCongr [pFiat]) (tF tA) (tF tC)
#guard Checks prog (pCongr [pFiat]) (tF tA) (tF tB)
#guard !Checks prog (pCongr [pFiat]) (tF tA) (.app "G" [tB])
#guard !Checks prog (pCongr []) (.app "Z" []) (.app "Z" [])

/-! Arity is part of the shape: `@Fiat` takes none, `@Congr` one per child, `@Rule_i` one
per premise, and `@Rule_1` names no rule. -/
#guard !Checks prog (.app "@Fiat" [tA, tB]) tA tB
#guard !Checks prog (pCongr [pFiat, pFiat]) (tF tA) (tF tB)
#guard !Checks prog (pRule 0 []) (tF tA) (tF tC)
#guard !Checks prog (pRule 1 [pFiat]) (tF tA) (tF tC)

/-! A term that is not a proof proves nothing. -/
#guard !Checks prog (.lit (.int 0)) tA tA
#guard !Checks prog (.app "@Bogus" [pFiat]) tA tB

/-! ### It says yes -/

/-! `union` contributes its pair both ways, and every built term its subterms reflexively. -/
#guard Checks prog pFiat tB tA
#guard Checks prog pFiat tA tA
#guard Checks prog pFiat (tF tA) (tF tA)

#guard Checks prog (pSym pFiat) tB tA
#guard Checks prog (pTrans pFiat (pSym pFiat)) tA tA
#guard Checks prog (pTrans (pSym pFiat) pFiat) tB tB

/-! Congruence under `F`, and a `@Rule_0` firing on the premise `(F (A)) = (F (A))`. -/
#guard Checks prog (pCongr [pSym pFiat]) (tF tB) (tF tA)
#guard Checks prog (pRule 0 [pFiat]) (tF tA) (tF tC)

/-! A nullary `@Congr` proves a declared constant self-equal with nothing to show for it: a
k-ary node carries no base proof, so presence is `Sound`'s endpoint hypothesis, not a check
this can run. -/
#guard Checks prog (pCongr []) tA tA

/-! The proposition is pinned, not merely non-empty. -/
#guard props (ctxOf prog) (pRule 0 [pFiat]) (some (tF tA)) (some (tF tC)) = [(tF tA, tF tC)]

end Witnesses
end Egglog
