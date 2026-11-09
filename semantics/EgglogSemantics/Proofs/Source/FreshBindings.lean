import EgglogSemantics.Proofs.Source.RebuildVars

/-! Fresh binding ranges compose independently of the allowed value universe. -/

namespace Egglog

/-- **The supply is injective**, so two blocks numbered apart bind different variables.
`toString_nat_inj` is the digits, and `String.append` cancels the `"@v"`. -/
theorem freshVar_inj {i j : Nat} (h : freshVar i = freshVar j) : i = j := by
  have h2 : (freshVar i).toList = (freshVar j).toList := by rw [h]
  rw [freshVar, freshVar, String.toList_append, String.toList_append] at h2
  exact toString_nat_inj (String.toList_inj.mp (List.append_cancel_left h2))

end Egglog
