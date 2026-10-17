import EgglogSemantics.Provenance.Checker

namespace Egglog.Provenance.Counterexamples

/-- A single row cannot supply the two distinct inputs of a collision. -/
theorem self_merge_rejected (sig : Signature) (f : FnName) (input : Term) :
    mergeFacts sig f input input = none := by
  cases hs : sig f with
  | none => simp [mergeFacts, hs]
  | some dc =>
      cases hm : dc.merge with
      | none => simp [mergeFacts, hs, hm]
      | some ms =>
          cases ms
          cases input <;> simp [mergeFacts, hs, hm]

end Egglog.Provenance.Counterexamples
