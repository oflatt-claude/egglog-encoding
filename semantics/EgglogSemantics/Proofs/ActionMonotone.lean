import EgglogSemantics.Proofs.Eval

/-! Actions preserve inclusion of mathematical states sharing an evaluation context. -/

namespace Egglog

/-- **An action available at `db` is available at any `D` containing it, with the same
effect.** The result is an existential over a database containing the smaller one, not
the exact join `MergeStep.diamond_of_join` asks for; the evaluation reads only `sig` and
`env`, which is what makes the witnesses survive. -/
theorem evalAction_mono {db D d : Database} (hc : db.Contained D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {a : Action}
    (h : evalAction db a = some d) :
    ∃ D', evalAction D a = some D' ∧ d.Contained D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  rcases evalAction_eq_some h with ⟨e, t, rfl, hv, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, hlit, rfl⟩
  · refine ⟨D.addTerm t, ?_, hc.addTerm_mono t, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · simpa using hsig
    · simpa using henv
  · refine ⟨D.addEq t₁ t₂, ?_, hc.addEq_mono t₁ t₂, ?_, ?_⟩
    · simp only [not_or, Bool.not_eq_true] at hlit
      simp [evalAction, ← hsig, ← henv, hv₁, hv₂, hlit.1, hlit.2]
    · simpa using hsig
    · simpa using henv

/-- `evalAction_mono` over a block: each step re-bases onto the previous one's larger
result. -/
theorem evalActions_mono {db D d : Database} (hc : db.Contained D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {as : List Action}
    (h : evalActions db as = some d) :
    ∃ D', evalActions D as = some D' ∧ d.Contained D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  induction as generalizing db D with
  | nil =>
    rw [evalActions_nil, Option.some.injEq] at h
    exact ⟨D, rfl, h ▸ hc, h ▸ hsig, h ▸ henv⟩
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      rw [evalActions_cons, hv, Option.bind_some] at h
      obtain ⟨D₀, hD₀, hc₀, hs₀, he₀⟩ := evalAction_mono hc hsig henv hv
      obtain ⟨D₁, hD₁, hc₁, hs₁, he₁⟩ := ih hc₀ hs₀ he₀ h
      exact ⟨D₁, by rw [evalActions_cons, hD₀, Option.bind_some]; exact hD₁, hc₁, hs₁, he₁⟩

end Egglog
