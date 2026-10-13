import EgglogSemantics.Spec.Step

namespace Egglog.SourceProof

structure Claim where
  lhs : Term
  rhs : Term
  deriving DecidableEq

/-- A proof tree. Every node states its claim. `fiat` cites an original global action, and
`rule` an original command with its substitution and one premise proof per query conjunct. -/
inductive Proof where
  | fiat (claim : Claim)
  | symm (claim : Claim) (proof : Proof)
  | trans (claim : Claim) (left right : Proof)
  | congr (claim : Claim) (base : Proof) (childIndex : Nat) (child : Proof)
  | rule (claim : Claim) (command : Nat) (subst : Env) (premises : List Proof)
  deriving BEq

def Proof.claim : Proof → Claim
  | .fiat c | .symm c _ | .trans c _ _ | .congr c _ _ _ | .rule c _ _ _ => c

@[simp] theorem Proof.claim_fiat (c : Claim) : (Proof.fiat c).claim = c := rfl
@[simp] theorem Proof.claim_symm (c : Claim) (p : Proof) : (Proof.symm c p).claim = c := rfl
@[simp] theorem Proof.claim_trans (c : Claim) (p q : Proof) :
    (Proof.trans c p q).claim = c := rfl
@[simp] theorem Proof.claim_congr (c : Claim) (p : Proof) (k : Nat) (q : Proof) :
    (Proof.congr c p k q).claim = c := rfl
@[simp] theorem Proof.claim_rule (c : Claim) (i : Nat) (σ : Env) (ps : List Proof) :
    (Proof.rule c i σ ps).claim = c := rfl

def Proof.subproofs : Proof → List Proof
  | .fiat _ => []
  | .symm _ p => [p]
  | .trans _ p q | .congr _ p _ q => [p, q]
  | .rule _ _ _ ps => ps

mutual

/-- Every node of the tree, in preorder. -/
def Proof.nodes : Proof → List Proof
  | p@(.fiat _) => [p]
  | p@(.symm _ q) => p :: q.nodes
  | p@(.trans _ q r) | p@(.congr _ q _ r) => p :: (q.nodes ++ r.nodes)
  | p@(.rule _ _ _ qs) => p :: Proof.nodesAll qs

def Proof.nodesAll : List Proof → List Proof
  | [] => []
  | q :: qs => q.nodes ++ Proof.nodesAll qs

end

end Egglog.SourceProof
