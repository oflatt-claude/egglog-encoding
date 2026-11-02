import EgglogSemantics.SourceProof.Checker

/-! Source proof construction. Every constructor validates the new root node against its
subproofs, so a lifting step fails where its justification is wrong. -/

namespace Egglog.Resugar

open SourceProof (Claim Proof)

def node (P : Program) (pf : Proof) : Option Proof :=
  if SourceProof.checkNode P pf then some pf else none

def symm (P : Program) : Proof → Option Proof
  | .symm p => some p
  | p => node P (.symm p)

def trans (P : Program) (p q : Proof) : Option Proof :=
  if p.claim.rhs != q.claim.lhs then none else node P (.trans p q)

def congr (P : Program) (p : Proof) (k : Nat) (q : Proof) : Option Proof := do
  let .app _ args := p.claim.rhs | none
  if args[k]? != some q.claim.lhs then none else node P (.congr p k q)

def orient (P : Program) (p : Proof) (c : Claim) : Option Proof :=
  if p.claim == c then some p else
    if p.claim.lhs == c.rhs && p.claim.rhs == c.lhs then symm P p else none

def contains (c : Claim) (t : Term) : Bool :=
  decide (t ∈ c.lhs.subtermList ∨ t ∈ c.rhs.subtermList)

/-- `t = t` from a proof whose claim is an endpoint equation of `t`, else `descend`. -/
def endpoints (P : Program) (t : Term) (p : Proof)
    (descend : Unit → Option Proof) : Option Proof :=
  if !contains p.claim t then none
  else if p.claim.lhs == t then do
    let s ← symm P p
    trans P p s
  else if p.claim.rhs == t then do
    let s ← symm P p
    trans P s p
  else descend ()

/-- Recover subterm existence from a source derivation, without a new proof axiom: an
endpoint by transitivity with its own symmetry, a subterm a firing built from that firing,
and otherwise from a subproof. -/
@[blueprint "def:lift-exist"
  (statement := /--
  \[
  \begin{aligned}
  \operatorname{exist}_s(\pi)&=\kw{trans}(\pi,\kw{sym}(\pi))&&\text{if }P\vdash\pi:s=t\\
  \operatorname{exist}_s(\pi)&=\kw{trans}(\kw{sym}(\pi),\pi)&&\text{if }P\vdash\pi:t=s\\
  \operatorname{exist}_s(\kw{rule}_i(c,\sigma;\pi_1,\ldots,\pi_n))&=\kw{rule}_i((s=s),\sigma;\pi_1,\ldots,\pi_n)
    &&\text{if }r_i=(Q_i\Rightarrow H_i)\text{ and }(s=s)\in\operatorname{facts}_\sigma(H_i)\\
  \operatorname{exist}_s(\pi)&=\operatorname{exist}_s(\pi')&&\text{for a subproof }\pi'\text{ of }\pi\text{, otherwise}
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def support (P : Program) (t : Term) : Proof → Option Proof
  | p@(.rule _ command σ ps) => endpoints P t p fun _ =>
      node P (.rule ⟨t, t⟩ command σ ps)
  | p@(.symm q) => endpoints P t p fun _ => support P t q
  | p@(.trans q r) | p@(.congr q _ r) => endpoints P t p fun _ =>
      support P t q <|> support P t r

def witness (P : Program) (t : Term) : List Proof → Option Proof
  | [] => none
  | p :: ps => support P t p <|> witness P t ps

def finish (P : Program) (p : Proof) (c : Claim) : Option Proof :=
  orient P p c <|> if c.lhs == c.rhs then support P c.lhs p else none

end Egglog.Resugar
