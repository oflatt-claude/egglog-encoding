import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Source.Domain

/-! Certificates for a program: the original program, or its compilation, whose equations
are all reflexive. A proof cites the program's rules; arbitrary reflexivity cannot justify
a missing rule premise. The checker reads only the program, never a state of the e-graph.
-/

namespace Egglog.SourceProof

/-- Only the monotone constructor source fragment. -/
def sourceOk (P : Program) : Bool := decide P.Fragment

/-- An equality premise is proved by the equation of its two instances; a bare pattern `e`
is the paper's `e = e`, so it is proved by its instance's reflexivity. A disequality, which
only compiled programs use, is proved by its left instance's reflexivity when the two
instances differ; `ruleFacts` also asks that the right instance be a subterm of some
premise claim, so that it exists. -/
def premiseMatches (σ : Env) (p : Pattern) (c : Claim) : Bool :=
  match p with
  | .expr e => e.eval σ == some c.lhs && c.lhs == c.rhs
  | .eq a b => a.eval σ == some c.lhs && b.eval σ == some c.rhs
  | .ne a b =>
    a.eval σ == some c.lhs && c.lhs == c.rhs && (b.eval σ).isSome && a.eval σ != b.eval σ

def premisesMatch (σ : Env) : Query → List Claim → Bool
  | [], [] => true
  | p :: ps, c :: cs => premiseMatches σ p c && premisesMatch σ ps cs
  | _, _ => false

/-- `t` is a subterm of a side of one of the claims. -/
def supported (cs : List Claim) (t : Term) : Bool :=
  cs.any fun c => decide (t ∈ c.lhs.subtermList ∨ t ∈ c.rhs.subtermList)

/-- The right side of every disequality premise exists: it is a subterm of a premise claim. -/
def disequalitiesSupported (σ : Env) (q : Query) (cs : List Claim) : Bool :=
  q.all fun p => match p with
    | .ne _ b => (b.eval σ).any (supported cs)
    | _ => true

/-- The facts a firing of `r` under `σ` with the premise claims `premises` may state: `σ`
binds exactly the query's variables, the premise claims match the patterns in order, and
the facts are those of the head. Every bound value is a subterm of a premise instance, so
no further support is needed. -/
@[blueprint "def:proof-facts"
  (statement := /--
  \[
  \begin{aligned}
  \operatorname{premises}_\sigma(e_1=e_2)&=\{\eval{e_1}=\eval{e_2}\}\\
  \operatorname{premises}_\sigma(e_1\ne e_2)&=\{\eval{e_1}=\eval{e_1}\}\\
    &\qquad\text{if }\eval{e_1}\ne\eval{e_2}\text{ and }\eval{e_2}
    \text{ is a subterm of a premise claim}\\
  \operatorname{refl}(t)&=\{\,s=s\mid s\text{ a subterm of }t\,\}\\
  \operatorname{facts}_\sigma(\kw{union}(e_1,e_2))
    &=\{\eval{e_1}=\eval{e_2},\ \eval{e_2}=\eval{e_1}\}
    \cup\operatorname{refl}(\eval{e_1})\cup\operatorname{refl}(\eval{e_2})\\
  \operatorname{facts}_\sigma(\kw{subsume}(f(e_1,\ldots,e_n)))&=\emptyset\\
  \operatorname{facts}_\sigma(\{h_1,\ldots,h_n\})
    &=\operatorname{facts}_\sigma(h_1)\cup\cdots\cup\operatorname{facts}_\sigma(h_n)
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def ruleFacts (r : Rule) (σ : Env) (premises : List Claim) : Option (List Claim) := do
  if decide ((Env.dom σ).Perm r.query.vars) && premisesMatch σ r.query premises &&
      disequalitiesSupported σ r.query premises then
    actionsFacts σ r.actions
  else none

/-- The root node, against the claims its subproofs state: `P ⊢ π : c`. -/
@[blueprint "def:proof-check"
  (statement := /--
  \begin{mathpar}
  \ir{Sym}{P\vdash\pi:s=t}{P\vdash\kw{sym}(\pi):t=s}
  \and
  \ir{Trans}{P\vdash\pi_1:s=t\\P\vdash\pi_2:t=u}{P\vdash\kw{trans}(\pi_1,\pi_2):s=u}
  \and
  \ir{Cong}{P\vdash\pi:s=f(t_1,\ldots,t_n)\\P\vdash\pi':t_k=t}
    {P\vdash\kw{cong}_k(\pi,\pi'):s=f(t_1,\ldots,t,\ldots,t_n)}
  \and
  \ir{Rule}{r_i=(p_1\land\cdots\land p_n\Rightarrow H)\\
    \sigma:\operatorname{FV}(p_1\land\cdots\land p_n)\to\mathit{Term}\\
    P\vdash\pi_j:c_j\\c_j\in\operatorname{premises}_\sigma(p_j)\ (\forall j)\\
    c\in\operatorname{facts}_\sigma(H)}
    {P\vdash\kw{rule}_i(c,\sigma;\pi_1,\ldots,\pi_n):c}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def checkNode (P : Program) : Proof → Bool
  | .rule c i σ ps => (do
      let r ← P.rules[i]?
      let fs ← ruleFacts r σ (ps.map Proof.claim)
      some (decide (c ∈ fs))).getD false
  | .symm _ => true
  | .trans p q => p.claim.rhs == q.claim.lhs
  | .congr p k q =>
      match p.claim.rhs with
      | .app _ args => args[k]? == some q.claim.lhs
      | .lit _ => false

mutual

/-- Every node is valid. -/
def valid (P : Program) : Proof → Bool
  | .rule c i σ ps => allValid P ps && checkNode P (.rule c i σ ps)
  | .symm p => valid P p && checkNode P (.symm p)
  | .trans p q => valid P p && valid P q && checkNode P (.trans p q)
  | .congr p k q => valid P p && valid P q && checkNode P (.congr p k q)

def allValid (P : Program) : List Proof → Bool
  | [] => true
  | p :: ps => valid P p && allValid P ps

end

/-- The claim of a proof whose every node is valid, against any program. -/
def checkIn (P : Program) (pf : Proof) : Option Claim :=
  if valid P pf then some pf.claim else none

/-- The claim of a proof whose every node is valid, against a source program in the
fragment. -/
def check (P : Program) (pf : Proof) : Option Claim := do
  if !sourceOk P then none else checkIn P pf

end Egglog.SourceProof
