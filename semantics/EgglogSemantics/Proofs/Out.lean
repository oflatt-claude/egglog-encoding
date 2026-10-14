import EgglogSemantics.Proofs.Step

/-! Monotonicity of mathematical table lookup. -/

namespace Egglog

/-- `Out` is monotone, because both of its conjuncts are. A rule body reading a table
never *loses* a match — the property an overwriting merge would destroy, and the one
seminaive evaluation rests on. -/
theorem Database.Out.mono {d₁ d₂ : Database} (h : d₁.Contained d₂)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  exact ⟨bs, CongList.mono h hl, h.terms hrow⟩

end Egglog
