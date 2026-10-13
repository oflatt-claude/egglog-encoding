import EgglogSemantics.Encoding.Encode

/-!
# Legacy proof checker (known unsound)

This executable checker is retained as a regression reference during the pass split.
It must not be used as a proof-validity oracle. `reflProps` accepts an arbitrary supplied
constructor term as existing, which lets a fabricated `@Fiat` premise trigger a source
rule whose query was never satisfied. Endpoint membership in `Sound` does not justify
these intermediate premises. See `CHECKER.md` for the concrete counterexample.

The old encoder also emits `@Fiat` for rule-created terms, omitting their actual rule
justifications. This causes both rejected generated proofs and false acceptances. The
replacement pipeline will instrument provenance, resugar explicit claims against the
original query, and validate the same certificate with the Lean and Rust checkers.

The code below still interprets the old endpoint-free `@Fiat`, `@Sym`, `@Trans`,
`@Congr_k`, and `@Rule_i` terms. It is independent of the new congruence pass.
-/

namespace Egglog
namespace Proof

/-! ### The vocabulary -/

def fiatName : FnName := "@Fiat"
def symName : FnName := "@Sym"
def transName : FnName := "@Trans"

/-- Congruence and rule firing are **families indexed at the name**, `@Congr_k` and
`@Rule_i`. The modelled language fixes one arity per name — a name used at two is
`Program.arityConflicts`, egglog's "Function already bound" — and congruence is needed at
every source arity, so a single `@Congr` cannot be declared. `Encode.lean`'s `congrName`
and `ruleName` are what write these. -/
def congrPrefix : String := "@Congr_"

/-- `@Rule_i` names the program's `i`th rule. -/
def rulePrefix : String := "@Rule_"

/-- The index a head in the family `pre` carries, if it is one of that family. -/
def familyIndex (pre : String) (f : FnName) : Option Nat :=
  if pre.isPrefixOf f then (f.drop pre.length).toNat? else none

/-- The arity a congruence head names; the node is refused unless its argument list has
exactly that length. -/
def congrIndex (f : FnName) : Option Nat := familyIndex congrPrefix f

/-- The rule a head names, if it names one. -/
def ruleIndex (f : FnName) : Option Nat := familyIndex rulePrefix f

/-! ### What the checker reads out of the program -/

/-- The source declarations, asserted equalities, and rules in program order. -/
structure Ctx where
  sig : Signature
  eqs : List (Term × Term)
  rules : List Rule

/-- One reflexive equality per subterm, which is what building a term asserts. -/
def reflEqs (t : Term) : List (Term × Term) := t.subtermList.map fun s => (s, s)

/-- `Spec/Eval.lean`'s `evalAction` with the asserted equalities as the accumulator:
`union` contributes its pair both ways, everything built contributes `reflEqs`. -/
def procAction (sig : Signature) (σ : Env) : Action → Option (List (Term × Term))
  | .expr e => (e.evalAtom sig σ).map fun t => reflEqs t
  | .union e₁ e₂ =>
      (e₁.eval sig σ).bind fun t₁ => (e₂.eval sig σ).bind fun t₂ =>
        if t₁.isLit || t₂.isLit then none
        else some ((t₁, t₂) :: (t₂, t₁) :: (reflEqs t₁ ++ reflEqs t₂))

/-- Evaluate every action in the same query substitution. -/
def procActions (sig : Signature) (σ : Env) : List Action → Option (List (Term × Term))
  | [] => some []
  | a :: as => (procAction sig σ a).bind fun r =>
      (procActions sig σ as).map fun r' => r ++ r'

/-- The equalities a rule head derives under `σ`. -/
def headEqs (sig : Signature) (as : List Action) (σ : Env) : List (Term × Term) :=
  (procActions sig σ as).getD []

def Ctx.empty : Ctx :=
  { sig := fun _ => none, eqs := [], rules := [] }

/-- Top-level expressions are closed. Rule variables are bound only when a proof is checked. -/
def Ctx.step (C : Ctx) : Cmd → Ctx
  | .decl f d => { C with sig := Function.update C.sig f (some d) }
  | .rule r => { C with rules := C.rules ++ [r] }
  | .action a =>
      match procAction C.sig [] a with
      | some es => { C with eqs := C.eqs ++ es }
      | none => C
  | .run _ => C
  | .saturate _ => C

def ctxOf (P : Program) : Ctx := P.foldl Ctx.step Ctx.empty

/-! ### Matching a body fact against a premise's proposition -/

mutual

/-- Match `e` against the ground term `t`, extending the rule's query substitution.
A name already bound is compared with its existing value; new bindings are appended. -/
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

/-- Extend `σ` so that `pr` is what the body fact `q` states. -/
def unifyFact (sig : Signature) (q : Pattern) (σ : Env) (pr : Term × Term) : Option Env :=
  (unifyExpr sig (factProp q).1 pr.1 σ).bind (unifyExpr sig (factProp q).2 pr.2)

/-! ### The query in proof normal form

egglog's checker reads the program **already flattened** — one body fact per application,
which is what `assert_body_proof_normal_form` demands — and `@Rule_i`'s premise count is
that flattened length, not the source query's. So is the encoding's: `encodeQuery` emits one
view read per application and `@Rule_i` takes one proof per read, which makes
`(Add (Add a b) c)` **two** premises and not one.

The flattening below is `Encoding/Encode.lean`'s `encodeQueryExpr` read on the source side —
same traversal, same order, same two-variables-per-read supply — with the target's view read
`(= (values x pf) (@fView c…))` written as the source equality `f(c…) = x` it stands for. A
source `(= e₁ e₂)` adds the id equality joining the two, which the encoding also emits and
no premise proof stands for.

The generated names are the encoding's own `@v0`, `@v1`, …, so they collide with nothing a
source program in `Program.EncodeDomain` can write (`EncodeDomain.noAt`).
`DiffTest.lean`'s `premiseCount_eq_ruleProofArity` is what keeps the two in step: it proves
the arity this demands is the arity `proofDecls` declares. -/

/-- The `n`th generated variable, `Encode.lean`'s `freshVar`. -/
def flatVar (n : Nat) : Var := "@v" ++ toString n

/-- A query in **proof normal form**: one fact per application, each flagged with whether a
premise proof stands for it. A view read carries one; the id equality joining two reads
carries none. -/
abbrev NormalQuery := List (Pattern × Bool)

mutual

/-- Flatten `e`: the expression naming its e-class, the facts, and the next variable number.
An application becomes the fact `f(children) = x` at a fresh `x`, its children flattened
first, and consumes two variables — the e-class and the premise proof, as the read it
mirrors binds both. -/
def flatExpr : Expr → Nat → Expr × NormalQuery × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .app f args, n =>
      match flatArgs args n with
      | (es, qs, n₁) =>
          (.var (flatVar n₁), qs ++ [(.eq (.app f es) (.var (flatVar n₁)), true)], n₁ + 2)

/-- `flatExpr` over an argument list. -/
def flatArgs : List Expr → Nat → List Expr × NormalQuery × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match flatExpr e n with
      | (e', qs, n₁) =>
          match flatArgs es n₁ with
          | (es', qs', n₂) => (e' :: es', qs ++ qs', n₂)

end

/-- Flatten one source pattern. `.expr e` is "`e` is present", which the reads already say;
`.eq` adds the id equality. An entry atom is passed through as `encodePattern` passes it
through, and stands for a premise proof exactly when `queryProofs` reads one off it — a
two-column read. Under `Program.EncodeDomain` the source has none. -/
def flatPattern : Pattern → Nat → NormalQuery × Nat
  | .expr e, n => match flatExpr e n with | (_, qs, n₁) => (qs, n₁)
  | .eq e₁ e₂, n =>
      match flatExpr e₁ n with
      | (x₁, qs₁, n₁) =>
          match flatExpr e₂ n₁ with
          | (x₂, qs₂, n₂) => (qs₁ ++ qs₂ ++ [(.eq x₁ x₂, false)], n₂)

/-- `flatPattern` over a query. -/
def flatQuery : Query → Nat → NormalQuery × Nat
  | [], n => ([], n)
  | p :: ps, n =>
      match flatPattern p n with
      | (qs, n₁) => match flatQuery ps n₁ with | (qs', n₂) => (qs ++ qs', n₂)

/-- **`@Rule_i`'s arity**: how many facts of `r`'s normal form a premise proof stands for.
`Encode.lean`'s `ruleProofArity` is the same number counted on the encoded query. -/
def premiseCount (r : Rule) : Nat := ((flatQuery r.query 0).1.filter Prod.snd).length

/-- Constrain `σ` by a fact no premise proof stands for: whichever side `σ` already grounds
fixes the other. Both sides name ids the reads have bound, so this filters `σ` and is not a
source of propositions. -/
def unifyJoin (sig : Signature) (q : Pattern) (σ : Env) : Option Env :=
  match (factProp q).1.eval sig σ with
  | some t => unifyExpr sig (factProp q).2 t σ
  | none => ((factProp q).2.eval sig σ).bind fun t => unifyExpr sig (factProp q).1 t σ

/-- Apply the leading run of proof-free facts, leaving the next fact a proof stands for. -/
def dropJoins (sig : Signature) : NormalQuery → List Env → NormalQuery × List Env
  | (q, false) :: qs, σs => dropJoins sig qs (σs.filterMap (unifyJoin sig q))
  | qs, σs => (qs, σs)

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

/-- Legacy permissive reflexivity. This is unsound for intermediate constructor premises:
it supplies no evidence that the term was built. Rust's `reflexive_value_term` only permits
primitive values and recursively justified value constructors, not eq-sort constructors. -/
def reflProps : Option Term → Option Term → List (Term × Term)
  | some a, some b => if a = b then [(a, a)] else []
  | some a, none => [(a, a)]
  | none, some b => [(b, b)]
  | none, none => []

mutual

/-- The propositions `pf` proves whose left endpoint is `ma` and right endpoint is `mb`,
where those are given. -/
def props (C : Ctx) : Term → Option Term → Option Term → List (Term × Term)
  | .lit _, _, _ => []
  | .app f ps, ma, mb =>
      if f = fiatName then
        if ps.isEmpty then
          let es := C.eqs.filter (endsOk ma mb)
          es ++ (reflProps ma mb).filter (fun p => p ∉ es)
        else []
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
      else
        match congrIndex f with
        | some k =>
            if ps.length ≠ k then [] else
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
        | none =>
          match ruleIndex f with
          | none => []
          | some i =>
              match C.rules[i]? with
              | none => []
              | some r =>
                  if ps.length = premiseCount r then
                    (ruleSubsts C ps (flatQuery r.query 0).1 [[]]).flatMap fun σ =>
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

/-- The substitutions the premises admit, one fact of the **normal form** at a time: a
proof-free fact only constrains `σ`, and each premise proof is paired with the next fact one
stands for. A leftover fact or a leftover proof is a refusal, which the arity test in `props`
has already made. -/
def ruleSubsts (C : Ctx) : List Term → NormalQuery → List Env → List Env
  | [], qs, σs =>
      match dropJoins C.sig qs σs with
      | ([], σs') => σs'
      | (_ :: _, _) => []
  | p :: ps, qs, σs =>
      match dropJoins C.sig qs σs with
      | ([], _) => []
      | ((q, _) :: qs', σs') =>
          ruleSubsts C ps qs' (σs'.flatMap fun σ =>
            -- Each side anchors the premise when `σ` already grounds it.
            (props C p ((factProp q).1.eval C.sig σ)
                ((factProp q).2.eval C.sig σ)).filterMap (unifyFact C.sig q σ))
  termination_by ps => sizeL ps
  decreasing_by all_goals (simp [sizeL]; try omega)

end

/-- `Checks` against a context already read off the program, so a caller with many claims
about one program reads it once. -/
def ChecksAt (C : Ctx) (pf : Term) (a b : Term) : Bool :=
  (props C pf (some a) (some b)).any fun p => decide (p = (a, b))

/-- **`pf` justifies `a = b` in the source program `P`.** -/
def Checks (P : Program) (pf : Term) (a b : Term) : Bool := ChecksAt (ctxOf P) pf a b

/-! ### Intended soundness contract

The current implementation does not satisfy this contract. Even at a saturated source
state, a `@Rule_i` can use `reflProps` to invent the existence of a missing constructor
premise. Requiring the final endpoints to belong to the source does not repair that gap.
-/
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
private def pCongr (ps : List Term) : Term := .app ("@Congr_" ++ toString ps.length) ps
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

/-! Reflexivity is `@Fiat`'s other disjunct, so it holds of a term no action built — which
is every term a rule head constructs. Only of a *reflexive* claim, and only with an endpoint
to read it off. -/
#guard Checks prog pFiat (tF tB) (tF tB)
#guard !Checks prog pFiat (tF tB) (tF tA)
#guard props (ctxOf prog) pFiat (some (tF tB)) none = [(tF tB, tF tB)]
#guard props (ctxOf prog) pFiat none none = (ctxOf prog).eqs

/-! A `@Rule_0` whose claim the head does not derive: the head unions `x` with `(F (C))`,
never with `(F (D))` though `(C) = (D)` is asserted, and the only substitution the premise
admits binds `x` to `(F (A))`. -/
#guard !Checks prog (pRule 0 [pFiat]) (tF tA) (tF tD)
#guard !Checks prog (pRule 0 [pFiat]) (tF tB) (tF tC)
#guard Checks prog (pRule 0 [pFiat]) (tF tA) (tF tC)

/-! A `@Congr_k` whose child does not prove the argument pair, one at mismatched heads, and
one at a head the program never declared. -/
#guard !Checks prog (pCongr [pFiat]) (tF tA) (tF tC)
#guard Checks prog (pCongr [pFiat]) (tF tA) (tF tB)
#guard !Checks prog (pCongr [pFiat]) (tF tA) (.app "G" [tB])
#guard !Checks prog (pCongr []) (.app "Z" []) (.app "Z" [])

/-! Congruence is the family `@Congr_k`, so the arity in the name is checked against the
argument list, and the bare `@Congr` the family replaced is no longer a proof at all. -/
#guard !Checks prog (.app "@Congr_2" [pFiat]) (tF tA) (tF tB)
#guard !Checks prog (.app "@Congr_0" [pFiat]) (tF tA) (tF tB)
#guard !Checks prog (.app "@Congr" [pFiat]) (tF tA) (tF tB)

/-! Arity is part of the shape: `@Fiat` takes none, `@Congr_k` one per child of a `k`-ary
head, `@Rule_i` one per premise, and `@Rule_1` names no rule. -/
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

/-! ### One premise per application

A nested source pattern reads one view per application, so `@Rule_i`'s arity is the query's
**flattened** length. `(F (F z))` is one pattern and two premises, and `@Rule_0` at one
premise is refused however good that premise is. -/
private def nested : Rule :=
  ⟨[.expr (.app "F" [.app "F" [.var "z"]])],
   [.union (.app "F" [.app "F" [.var "z"]]) eB], ""⟩

private def prog2 : Program :=
  [.decl "A" (cnst 0), .decl "B" (cnst 0), .decl "F" (cnst 1),
   .action (.union eA eB),
   .action (.expr (.app "F" [.app "F" [eA]])),
   .rule nested, .run ""]

#guard nested.query.length = 1
#guard premiseCount nested = 2
#guard Checks prog2 (pRule 0 [pFiat, pFiat]) (tF (tF tA)) tB
#guard !Checks prog2 (pRule 0 [pFiat]) (tF (tF tA)) tB
#guard !Checks prog2 (pRule 0 [pFiat, pFiat, pFiat]) (tF (tF tA)) tB

/-! ### A premise proof has to reach outside `C.eqs`

`props C p` is the **only** generator of premise propositions, and at `@Fiat` it generates
`C.eqs` and nothing else. So a rule whose body joins two reads through a middle term the
program never asserted fires only under a *composed* premise proof, and acceptance flips on
the shape of that proof rather than on the claim. `@Rule_i`'s premise arguments are
load-bearing, not decoration.

`chain` asserts `(F (A)) = H1`, `H1 = H2` and `H2 = (G (B))`, so `(F (A)) = (G (B))` is
derivable and not asserted, and the rule's two reads join on it. -/
private def eH1 : Expr := .app "H1" []
private def eH2 : Expr := .app "H2" []
private def tH2 : Term := .app "H2" []
private def tG (t : Term) : Term := .app "G" [t]

private def chainRule : Rule :=
  ⟨[.eq (.app "F" [.var "x"]) (.app "G" [.var "y"])],
   [.union (.var "x") (.var "y")], ""⟩

private def chain : Program :=
  [.decl "A" (cnst 0), .decl "B" (cnst 0), .decl "H1" (cnst 0), .decl "H2" (cnst 0),
   .decl "F" (cnst 1), .decl "G" (cnst 1),
   .action (.union (.app "F" [eA]) eH1),
   .action (.union eH1 eH2),
   .action (.union eH2 (.app "G" [eB])),
   .rule chainRule, .run ""]

/-! The join itself: a two-step `@Trans` reaches the middle term `H2`, and no number of steps
makes `(F (A)) = (G (B))` a `@Fiat`. -/
#guard premiseCount chainRule = 2
#guard Checks chain (pTrans pFiat pFiat) (tF tA) tH2
#guard !Checks chain pFiat (tF tA) tH2
#guard !Checks chain (pTrans pFiat pFiat) (tF tA) (tG tB)
#guard Checks chain (pTrans pFiat (pTrans pFiat pFiat)) (tF tA) (tG tB)

/-! And the flip, at the rule. Two `@Fiat` premises cannot meet, because each is confined to
`C.eqs` and the meet is `H2`; either premise composed to reach `H2` fires it. Direction is
free — `@Sym` inside a premise walks the chain the other way — and the arity test still runs
ahead of everything. -/
#guard !Checks chain (pRule 0 [pFiat, pFiat]) tA tB
#guard Checks chain (pRule 0 [pTrans pFiat pFiat, pFiat]) tA tB
#guard Checks chain (pRule 0 [pFiat, pTrans (pSym pFiat) (pSym pFiat)]) tA tB
#guard !Checks chain (pRule 0 [pSym pFiat, pFiat]) tA tB
#guard !Checks chain (pRule 0 []) tA tB

/-! ### Query variables remain local to the rule -/
private def localRule : Rule :=
  ⟨[.expr (.app "F" [.var "x"])], [.union (.app "F" [.var "x"]) eB], ""⟩

private def localProgram : Program :=
  [.decl "A" (cnst 0), .decl "B" (cnst 0), .decl "C" (cnst 0), .decl "F" (cnst 1),
   .rule localRule, .action (.expr (.app "F" [eA])), .action (.expr eC), .run ""]

#guard (ctxOf localProgram).rules.map premiseCount = [1]
#guard Checks localProgram (pRule 0 [pFiat]) (tF tA) tB
#guard !Checks localProgram (pRule 0 [pFiat]) (tF tC) tB

/-! ### Missing construction provenance

The legacy encoder uses `@Fiat` for rule-created terms, omitting the creating firing.
With both endpoints free, the checker cannot recover those terms from globals. Supplying
the creating rule proof repairs these examples (`both-2` and `rand-43`). Allowing arbitrary
constructor reflexivity instead is unsound; see `CHECKER.md`.

Here rule 0 builds `(G (B) (A))` as a subterm, and rule 1 needs evidence of its existence. -/
private def eG (x y : Expr) : Expr := .app "G" [x, y]
private def tG2 (x y : Term) : Term := .app "G" [x, y]

private def created : Program :=
  [.decl "A" (cnst 0), .decl "B" (cnst 0), .decl "F" (cnst 1), .decl "G" (cnst 2),
   .action (.expr (eG eA eB)),
   .rule ⟨[.expr (eG (.var "x") (.var "y"))],
          [.union (eG (.var "x") (.var "y")) (.app "F" [eG (.var "y") (.var "x")])], ""⟩,
   .rule ⟨[.expr (eG (.var "x") (.var "y"))],
          [.union (eG (.var "x") (.var "y")) eB], ""⟩,
   .run "", .run ""]

/-! At the top-level term rule 1 checks; at the term rule 0 created it does not, and the
same claim with the creating firing named as the premise does. -/
#guard Checks created (pRule 1 [pFiat]) (tG2 tA tB) tB
#guard !Checks created (pRule 1 [pFiat]) (tG2 tB tA) tB
#guard Checks created (pRule 1 [pRule 0 [pFiat]]) (tG2 tB tA) tB

end Witnesses
end Egglog
