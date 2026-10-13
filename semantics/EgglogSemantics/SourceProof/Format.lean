import EgglogSemantics.Spec.Step

namespace Egglog.SourceProof

structure Claim where
  lhs : Term
  rhs : Term
  deriving DecidableEq

/-- References index earlier nodes in the certificate. -/
inductive Reason where
  | fiat
  | symm (proof : Nat)
  | trans (left right : Nat)
  | congr (base childIndex child : Nat)
  | rule (command : Nat) (subst : Env) (premises : List Nat)
  | merge (function : FnName) (old new : Nat)

structure Node where
  claim : Claim
  reason : Reason

structure Certificate where
  nodes : List Node
  root : Nat

end Egglog.SourceProof
