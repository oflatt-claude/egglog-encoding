import EgglogSemantics.Proofs.Match

/-! Positive queries preserve their matches when the mathematical state grows. -/

namespace Egglog

theorem congOn_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {ts : List Term} {a b : Term}
    (hc : CongOn d₁ ts a b) : CongOn d₂ ts a b := Cong.mono (h.addTerms_mono ts) hc

theorem ValidEnv.mono {d₁ d₂ : Database} (h : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) {vars : List Var}
    {σ : Env} (hv : ValidEnv vars d₁ σ) : ValidEnv vars d₂ σ :=
  ⟨hv.1, fun b hb => ⟨h.terms (hv.mem_terms b hb), hsig ▸ (hv.mem_values b hb).2⟩⟩

/- Matches persist under assertion inclusion at a fixed signature. -/
theorem ValidSubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    (_henv : d₂.env = d₁.env) {p : Pattern} {σ : Env} (h : ValidSubst d₁ p σ) :
    ValidSubst d₂ p σ := by
  refine ⟨h.1.mono hc hsig, ?_⟩
  cases h.2 with
  | expr hw he hcong =>
    exact .expr (hc.terms hw) (by rw [← hsig]; exact he) (congOn_mono hc hcong)
  | eq hw he₁ he₂ hc₁ hc₂ =>
    exact .eq (hc.terms hw) (by rw [← hsig]; exact he₁)
      (by rw [← hsig]; exact he₂) (congOn_mono hc hc₁) (congOn_mono hc hc₂)

theorem ValidQuerySubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) (henv : d₂.env = d₁.env) {q : Query} {σ : Env}
    (h : ValidQuerySubst d₁ q σ) : ValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, hall.imp fun _ _ hv => ValidSubst.mono hc hsig henv hv, hu⟩

end Egglog
