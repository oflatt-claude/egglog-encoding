import EgglogSemantics.Proofs.Step

/-! Monotonicity of mathematical table lookup. -/

namespace Egglog

/-- Lookup persists when assertions grow at a fixed signature. -/
theorem Database.Out.mono {d₁ d₂ : Database} (h : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  exact ⟨bs, CongList.mono h hl, ⟨hsig ▸ hrow.1, h.eqs hrow.2⟩⟩

end Egglog
