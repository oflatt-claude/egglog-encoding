import EgglogSemantics.SourceProof.Evaluate

namespace Egglog.Provenance

/-- Relational facts have existence evidence, without equality axioms. Every node states
its fact: `rule` cites a firing with one proof per premise, `merge` two established
entries, and `subterm` an established fact containing it. -/
inductive Proof where
  | rule (fact : Term) (command : Nat) (subst : Env) (premises : List Proof)
  | merge (fact : Term) (function : FnName) (old new : Proof)
  | subterm (fact : Term) (parent : Proof)

def Proof.fact : Proof → Term
  | .rule t _ _ _ | .merge t _ _ _ | .subterm t _ => t

@[simp] theorem Proof.fact_rule (t : Term) (i : Nat) (σ : Env) (ps : List Proof) :
    (Proof.rule t i σ ps).fact = t := rfl
@[simp] theorem Proof.fact_merge (t : Term) (f : FnName) (p q : Proof) :
    (Proof.merge t f p q).fact = t := rfl
@[simp] theorem Proof.fact_subterm (t : Term) (p : Proof) : (Proof.subterm t p).fact = t := rfl

def Proof.subproofs : Proof → List Proof
  | .rule _ _ _ ps => ps
  | .merge _ _ p q => [p, q]
  | .subterm _ p => [p]

end Egglog.Provenance
