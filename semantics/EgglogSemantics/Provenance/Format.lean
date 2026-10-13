import EgglogSemantics.SourceProof.Evaluate

namespace Egglog.Provenance

/-- Relational facts have existence evidence, without equality axioms. Every node states
its fact: `global` cites an original action, `rule` a firing with its substitution and one
proof per premise, `merge` a derivation from two established entries, and `subterm` an
established fact containing it. -/
inductive Proof where
  | global (fact : Term) (command : Nat)
  | rule (fact : Term) (command : Nat) (subst : Env) (premises : List Proof)
  | merge (fact : Term) (function : FnName) (old new : Proof)
  | subterm (fact : Term) (parent : Proof)

def Proof.fact : Proof → Term
  | .global t _ | .rule t _ _ _ | .merge t _ _ _ | .subterm t _ => t

@[simp] theorem Proof.fact_global (t : Term) (i : Nat) : (Proof.global t i).fact = t := rfl
@[simp] theorem Proof.fact_rule (t : Term) (i : Nat) (σ : Env) (ps : List Proof) :
    (Proof.rule t i σ ps).fact = t := rfl
@[simp] theorem Proof.fact_merge (t : Term) (f : FnName) (p q : Proof) :
    (Proof.merge t f p q).fact = t := rfl
@[simp] theorem Proof.fact_subterm (t : Term) (p : Proof) : (Proof.subterm t p).fact = t := rfl

def Proof.subproofs : Proof → List Proof
  | .global _ _ => []
  | .rule _ _ _ ps => ps
  | .merge _ _ p q => [p, q]
  | .subterm _ p => [p]

end Egglog.Provenance
