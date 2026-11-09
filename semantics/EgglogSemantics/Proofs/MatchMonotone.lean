import EgglogSemantics.Proofs.SourceMeaning

/-! Positive patterns persist under growth. A fixed substitution remains valid only
when its bindings remain representatives. -/

namespace Egglog

theorem Matches.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hl : d₁.live ⊆ d₂.live)
    {p : Pattern} {σ : Env} (hp : p.monotoneB = true) (h : Matches d₁ p σ) :
    Matches d₂ p σ := by
  cases h with
  | atom hr =>
    obtain ⟨t, he⟩ := hr.eval_exists
    exact .atom (Lookup.mono_live hl ⟨he, hr⟩).2
  | equal hr₁ hr₂ he₁ he₂ hh =>
    exact .equal (Lookup.mono_live hl ⟨he₁, hr₁⟩).2 (Lookup.mono_live hl ⟨he₂, hr₂⟩).2
      he₁ he₂ (hh.mono hc)
  | unequal _ _ _ _ _ => simp [Pattern.monotoneB] at hp

open SourceMeaning InferredFacts

/-- Growth may change a representative, so transport chooses congruent bindings. -/
theorem ValidEnv.transport {d e : Database} (hc : d.Contained e) (he : e.WF)
    (hr : e.HasReps) {vars : List Var} {σ : Env} (hv : ValidEnv vars d σ) :
    ∃ τ, ValidEnv vars e τ ∧ EnvRelated e σ τ := by
  let w := representative e he
  have hw : ∀ t ∈ d.terms, w t ∈ e.reps ∧ e.Infers t (w t) :=
    fun t ht => representative_spec he hr (infers_of_held (hc.terms ht))
  refine ⟨Env.mapVals w σ, ⟨?_, ?_⟩,
    envRelated_map hv.mem_terms (fun t ht => (hw t ht).2)⟩
  · simpa [dom_mapVals] using hv.1
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_mapVals hb
    exact (hw a.2 (hv.mem_terms a ha)).1

theorem Matches.transport {d e : Database} (hc : d.Contained e) (hl : d.live ⊆ e.live) (he : e.WF)
    {p : Pattern} {σ τ : Env} (hr : EnvRelated e σ τ)
    (hn : p.OrderingFree) (hp : p.monotoneB = true) (hm : Matches d p σ) :
    Matches e p τ :=
  matches_transport he he (.refl _) hr hn (hm.mono hc hl hp)

theorem QueryMatches.transport {d e : Database} (hc : d.Contained e) (hl : d.live ⊆ e.live) (he : e.WF)
    (hr : e.HasReps) {q : Query} {σ : Env}
    (hn : ∀ p ∈ q, p.OrderingFree) (hp : ∀ p ∈ q, p.monotoneB = true)
    (hm : QueryMatches d q σ) :
    ∃ τ, QueryMatches e q τ ∧ EnvRelated e σ τ := by
  obtain ⟨τ, hτ, hrel⟩ := hm.1.transport hc he hr
  exact ⟨τ, ⟨hτ, fun p h => (hm.2 p h).transport hc hl he hrel (hn p h) (hp p h)⟩, hrel⟩

end Egglog
