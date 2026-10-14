import EgglogSemantics.Proofs.Congruence.Match

/-! Exact evaluation of source rule heads reconstructed from target matches. -/

namespace Egglog.Congruence

mutual

/-- **An evaluation transports along `Signature.IsCtor` at the names it applies.** -/
theorem eval_transport {s₁ s₂ : Signature} :
    ∀ (e : Expr) {ρ₁ ρ₂ : Env} {t : Term}, (∀ f ∈ e.fns, s₁.IsCtor f → s₂.IsCtor f) →
      (∀ v ∈ e.vars, Env.lookup v ρ₁ = Env.lookup v ρ₂) → e.eval s₁ ρ₁ = some t →
      e.eval s₂ ρ₂ = some t
  | .lit _, _, _, _, _, _, h => h
  | .var v, _, _, _, _, hv, h => by
      rw [Expr.eval] at h ⊢
      rw [← hv v (by simp [Expr.vars]), h]
  | .app f args, _, _, _, hc, hv, h => by
      have hfn : ∀ g ∈ Expr.fnsList args, s₁.IsCtor g → s₂.IsCtor g :=
        fun g hg => hc g (by simp [Expr.fns, hg])
      have hvl : ∀ v ∈ Expr.varsList args, Env.lookup v _ = Env.lookup v _ :=
        fun w hw => hv w (by simpa [Expr.vars] using hw)
      simp only [Expr.eval] at h ⊢
      by_cases hct : s₁.IsCtor f
      · rw [if_pos hct] at h
        obtain ⟨ts, hts, hap⟩ := Option.map_eq_some_iff.mp h
        rw [if_pos (hc f (by simp [Expr.fns]) hct),
          evalList_transport args hfn hvl hts]
        exact congrArg some hap
      · rw [if_neg hct] at h
        exact absurd h (by simp)
  | .min a b, _, _, _, hc, hv, h => by
      rw [Expr.eval_min, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, hmap⟩ := h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rw [Expr.eval_min,
        eval_transport a (fun g hg => hc g (by simp [Expr.fns, hg]))
          (fun w hw => hv w (by simp [Expr.vars, hw])) hx,
        Option.bind_some,
        eval_transport b (fun g hg => hc g (by simp [Expr.fns, hg]))
          (fun w hw => hv w (by simp [Expr.vars, hw])) hy,
        Option.map_some]

@[inherit_doc eval_transport]
theorem evalList_transport {s₁ s₂ : Signature} :
    ∀ (es : List Expr) {ρ₁ ρ₂ : Env} {ts : List Term},
      (∀ f ∈ Expr.fnsList es, s₁.IsCtor f → s₂.IsCtor f) →
      (∀ v ∈ Expr.varsList es, Env.lookup v ρ₁ = Env.lookup v ρ₂) →
      Expr.evalList s₁ es ρ₁ = some ts → Expr.evalList s₂ es ρ₂ = some ts
  | [], _, _, _, _, _, h => h
  | e :: es, _, _, _, hc, hv, h => by
      rw [Expr.evalList] at h ⊢
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, hcons⟩ := Option.map_eq_some_iff.mp hrest
      rw [eval_transport e (fun g hg => hc g (by simp [Expr.fnsList, hg]))
          (fun w hw => hv w (by simp [Expr.varsList, hw])) ht,
        evalList_transport es (fun g hg => hc g (by simp [Expr.fnsList, hg]))
          (fun w hw => hv w (by simp [Expr.varsList, hw])) hts]
      exact congrArg some hcons

end

/-- The source match preserves every evaluation a scoped rule head performs. Since
source heads have no let-bound globals, only the query's variables need transporting. -/
theorem sourceMatch_evaluations {src tgt : Database} (hb : src.TermsBuild)
    (hs : ViewsSound tgt src) (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hof : ∀ p ∈ q, p.OrderingFree) (hg : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∃ τ, ValidQuerySubst src q τ ∧
      ∀ (e : Expr), (∀ f ∈ e.fns, tgt.sig.IsCtor f ↔ src.sig.IsCtor f) →
        (∀ v ∈ e.vars, v ∈ Query.vars q) →
        e.eval tgt.sig (σ ++ tgt.env) = e.eval src.sig (τ ++ src.env) := by
  obtain ⟨τ, hτ, _, hlookup⟩ := sourceMatch_of_encodedQuery hb hs hd hsc hof hg hk h
  have hread := patternReads_of_encodeQuery hd hsc hof hk h
  have henv : ∀ v ∈ Query.vars q,
      Env.lookup v (σ ++ tgt.env) = Env.lookup v (τ ++ src.env) := by
    intro v hv
    obtain ⟨p, hp, hvp⟩ := hk v hv
    obtain ⟨i, hi, _⟩ := mem_terms_of_patternArgVar hs (hread p hp) hvp
    rw [Env.lookup_append_of_some hi, hlookup v hv i hi]
  refine ⟨τ, hτ, fun e hf hv => ?_⟩
  have hvars := fun v hv' => henv v (hv v hv')
  cases ht : e.eval tgt.sig (σ ++ tgt.env) with
  | some t =>
      exact (eval_transport e (fun f hm => (hf f hm).mp) hvars ht).symm
  | none =>
      cases hs : e.eval src.sig (τ ++ src.env) with
      | none => rfl
      | some t =>
          have hback := eval_transport e (fun f hm => (hf f hm).mpr)
            (fun v hm => (hvars v hm).symm) hs
          rw [ht] at hback
          contradiction

end Egglog.Congruence
