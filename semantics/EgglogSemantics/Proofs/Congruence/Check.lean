import EgglogSemantics.Proofs.Congruence.Source
import EgglogSemantics.Proofs.Congruence.QueryCorr

/-! The final check: at a canonical compiled state, the compiled check holds on the state
with subsumption forgotten exactly when the source check holds on the partner. -/

namespace Egglog.Congruence

variable {P : Program}

/-! ### Compiled queries are monotone -/

mutual

theorem flat_monotone : ∀ (e : Expr) (n : Nat),
    ∀ p ∈ (encodeQueryExprWith {} e n).2.1, p.monotoneB = true
  | .lit _, _, _, hp => by rw [flat_lit] at hp; simp at hp
  | .var _, _, _, hp => by rw [flat_var] at hp; simp at hp
  | .min _ _, _, _, hp => by rw [flat_min] at hp; simp at hp
  | .app f args, n, p, hp => by
      rcases hr : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      rw [flat_app hr] at hp
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (hp | rfl | hp) | rfl
      · have := flatArgs_monotone args n p
        rw [hr] at this
        exact this hp
      · rfl
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
        rfl
      · rfl

theorem flatArgs_monotone : ∀ (es : List Expr) (n : Nat),
    ∀ p ∈ (encodeQueryArgsWith {} es n).2.1, p.monotoneB = true
  | [], _, _, hp => by rw [flatArgs_nil] at hp; simp at hp
  | e :: es, n, p, hp => by
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂] at hp
      simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · have := flat_monotone e n p
        rw [h₁] at this
        exact this hp
      · have := flatArgs_monotone es next p
        rw [h₂] at this
        exact this hp

end

theorem pattern_monotone {p : Pattern} (hp : p.monotoneB = true) (n : Nat) :
    ∀ q ∈ (encodePatternWith {} p n).1, q.monotoneB = true := by
  cases p with
  | expr e => exact flat_monotone e n
  | eq l r =>
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    rw [pattern_eq h₁ h₂]
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | hq) | rfl
    · have := flat_monotone l n q
      rw [h₁] at this
      exact this hq
    · have := flat_monotone r next q
      rw [h₂] at this
      exact this hq
    · rfl
  | ne _ _ => simp [Pattern.monotoneB] at hp

theorem query_monotone {q : Query} (hq : ∀ p ∈ q, p.monotoneB = true) (n : Nat) :
    ∀ p ∈ (encodeQueryWith {} q n).1, p.monotoneB = true := by
  induction q generalizing n with
  | nil => rw [query_nil]; simp
  | cons p ps ih =>
    rcases h₁ : encodePatternWith {} p n with ⟨qs, next⟩
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    rw [query_cons h₁ h₂]
    intro r hr
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · have := pattern_monotone (hq p (by simp)) n r
      rw [h₁] at this
      exact this hr
    · have := ih (fun p hp => hq p (by simp [hp])) next r
      rw [h₂] at this
      exact this hr

/-! ### Forgetting subsumption -/

theorem matches_forget {d : Database} {p : Pattern} {σ : Env} (hp : p.monotoneB = true)
    (h : Matches d p σ) : Matches d.forgetSubsumed p σ := by
  have hl : d.live ⊆ d.forgetSubsumed.live := by
    rw [Database.live_forgetSubsumed]
    intro t ht
    exact ht.1
  cases h with
  | atom hr =>
    obtain ⟨t, he⟩ := hr.eval_exists
    exact .atom (Expr.Matches.mono_live hl ⟨he, hr⟩).2
  | equal hr₁ hr₂ he₁ he₂ hh =>
    exact .equal (Expr.Matches.mono_live hl ⟨he₁, hr₁⟩).2 (Expr.Matches.mono_live hl ⟨he₂, hr₂⟩).2 he₁ he₂
      ((Cong.iff_of_eqs_eq (d := d) (e := d.forgetSubsumed) rfl).mp hh)
  | unequal => simp [Pattern.monotoneB] at hp

theorem queryMatches_forget {d : Database} (hd : d.Diag) {q : Query}
    (hq : ∀ p ∈ q, p.monotoneB = true) {σ : Env} (h : QueryMatches d q σ) :
    QueryMatches d.forgetSubsumed q σ := by
  refine ⟨⟨h.1.1, fun b hb => ?_⟩, fun p hp => matches_forget (hq p hp) (h.2 p hp)⟩
  rw [hd.forgetSubsumed.reps_eq_terms, Database.terms_eq_of_eqs_eq (d₁ := d.forgetSubsumed)
    (d₂ := d) rfl]
  exact (h.1.2 b hb).1

/-! ### The check -/

/-- The source check on the partner holds exactly when the compiled check holds on the
compiled state with subsumption forgotten. -/
theorem check_corr (hP : P.Fragment) {x d : Database} (hx : SrcInv P x) (h : Rel x d)
    (hc : Canon d) :
    QueryHolds x P.check ↔ QueryHolds d.forgetSubsumed (encodeQueryWith {} P.check 0).1 := by
  have hq := queryOk_check hP
  have hmono := check_monotone hP
  have hof := check_orderingFree hP
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨σ', hσ', _⟩ := fire_complete h hc hx.wf hq hσ
    exact ⟨σ', queryMatches_forget h.diag (query_monotone hmono 0) hσ'⟩
  · rintro ⟨σ', hσ'⟩
    have hreads := h.reads_forget
    have hbound : ∀ v ∈ Query.vars P.check, (Env.lookup v σ').isSome := by
      intro v hv
      apply Env.lookup_isSome_iff_mem_dom.mpr
      exact hσ'.1.1.mem_iff.mpr ((query_vars_iff hq.shape 0).mpr (Or.inl hv))
    set σ := restrict (Query.vars P.check) σ' with hσdef
    have hlook : ∀ v ∈ Query.vars P.check, Env.lookup v σ = Env.lookup v σ' :=
      fun v hv => lookup_restrict (Query.vars_nodup _) hv
    have hvals : ∀ v t, Env.lookup v σ = some t → t ∈ x.terms := by
      intro v t hvt
      obtain ⟨hv, hlk⟩ := mem_restrict (vs := Query.vars P.check) (σ := σ') (b := (v, t))
        (Env.mem_of_lookup hvt)
      obtain ⟨p, hp, hpv⟩ := check_keyed hP v hv
      obtain ⟨a, ha⟩ := query_argVar_atom 0 hq.minOverVars hp hpv
      obtain ⟨a', t', ha', ht', hedge⟩ := matches_uf_var_var_iff.mp (hσ'.2 _ ha)
      obtain rfl : t = t' := Option.some.inj (hlk.symm.trans ht')
      exact (hreads.edge _ _ hedge).2.2
    have hm : ∀ p ∈ P.check, Matches x p σ :=
      sound_query hreads hx.subsumed 0 hq.minOverVars hq.shape hq.names (Or.inl hmono)
        (fun v hv => (hlook v hv).symm) hvals hσ'.2
    have hdom : (Env.dom σ).Perm (Query.vars P.check) := by
      rw [hσdef, dom_restrict hbound]
    have hnd : (Env.dom σ).Nodup := hdom.symm.nodup (Query.vars_nodup _)
    obtain ⟨τ, hτ, _⟩ := SourceMeaning.querySubst_of_matches_transport hx.wf hx.wf
      (Database.SameMeaning.refl x) hx.hasReps hdom
      (fun b hb => hvals b.1 b.2 ((Env.lookup_eq_some_iff_mem hnd).mpr hb))
      hof hm
    exact queryHolds_iff_validQuerySubst.mpr ⟨τ, hτ⟩

end Egglog.Congruence
