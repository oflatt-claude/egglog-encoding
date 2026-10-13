import EgglogSemantics.SourceProof.Evaluate

namespace Egglog.Provenance

/-- Relational facts have existence evidence, without equality axioms. -/
inductive Reason where
  | global (command : Nat)
  | rule (command : Nat) (subst : Env) (premises : List Nat)
  | merge (function : FnName) (old new : Nat)
  | subterm (parent : Nat)

structure Node where
  fact : Term
  reason : Reason

structure Certificate where
  nodes : List Node
  root : Nat

end Egglog.Provenance
