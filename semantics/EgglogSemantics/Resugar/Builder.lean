import EgglogSemantics.SourceProof.Checker

/-! Source proof construction. Every constructor validates the new root node against its
subproofs, so a lifting step fails where its justification is wrong. -/

namespace Egglog.Resugar

open SourceProof (Claim Proof Context)

def node (P : Program) (C : Context) (pf : Proof) : Option Proof :=
  if SourceProof.checkNode P C pf then some pf else none

def symm (P : Program) (C : Context) : Proof → Option Proof
  | .symm _ p => some p
  | p => node P C (.symm ⟨p.claim.rhs, p.claim.lhs⟩ p)

def trans (P : Program) (C : Context) (p q : Proof) : Option Proof :=
  if p.claim.rhs != q.claim.lhs then none else
    node P C (.trans ⟨p.claim.lhs, q.claim.rhs⟩ p q)

def congr (P : Program) (C : Context) (p : Proof) (k : Nat) (q : Proof) : Option Proof := do
  let .app f args := p.claim.rhs | none
  if args[k]? != some q.claim.lhs then none else
    node P C (.congr ⟨p.claim.lhs, .app f (args.set k q.claim.rhs)⟩ p k q)

def orient (P : Program) (C : Context) (p : Proof) (c : Claim) : Option Proof :=
  if p.claim == c then some p else
    if p.claim.lhs == c.rhs && p.claim.rhs == c.lhs then symm P C p else none

def contains (c : Claim) (t : Term) : Bool :=
  decide (t ∈ c.lhs.subtermList ∨ t ∈ c.rhs.subtermList)

/-- `t = t` from a proof whose claim is an endpoint equation of `t`, else `descend`. -/
def endpoints (P : Program) (C : Context) (t : Term) (p : Proof)
    (descend : Unit → Option Proof) : Option Proof :=
  if !contains p.claim t then none
  else if p.claim.lhs == t then do
    let s ← symm P C p
    trans P C p s
  else if p.claim.rhs == t then do
    let s ← symm P C p
    trans P C s p
  else descend ()

/-- Recover subterm existence from a source derivation, without a new proof axiom. -/
def support (P : Program) (C : Context) (t : Term) : Proof → Option Proof
  | p@(.fiat _) => endpoints P C t p fun _ => node P C (.fiat ⟨t, t⟩)
  | p@(.rule _ command σ ps) => endpoints P C t p fun _ =>
      node P C (.rule ⟨t, t⟩ command σ ps)
  | p@(.symm _ q) => endpoints P C t p fun _ => support P C t q
  | p@(.trans _ q r) | p@(.congr _ q _ r) => endpoints P C t p fun _ =>
      support P C t q <|> support P C t r

def witness (P : Program) (C : Context) (t : Term) : List Proof → Option Proof
  | [] => none
  | p :: ps => support P C t p <|> witness P C t ps

def finish (P : Program) (C : Context) (p : Proof) (c : Claim) : Option Proof :=
  orient P C p c <|> if c.lhs == c.rhs then support P C c.lhs p else none

end Egglog.Resugar
