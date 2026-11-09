import EgglogSemantics.Source.Names
import EgglogSemantics.Proofs.Bindings

/-! Distinct key variables shared by the rebuilding passes. -/

namespace Egglog

theorem toString_nat_inj {i j : Nat} (h : toString i = toString j) : i = j := by
  have hd : Nat.toDigits 10 i = Nat.toDigits 10 j := by
    rw [← Nat.toList_repr, ← Nat.toList_repr, ← Nat.toString_eq_repr, ← Nat.toString_eq_repr, h]
  have hi := Nat.ofDigitChars_toDigits (b := 10) (n := i) (by decide) (by decide)
  rw [hd, Nat.ofDigitChars_toDigits (by decide) (by decide)] at hi
  exact hi.symm

end Egglog
