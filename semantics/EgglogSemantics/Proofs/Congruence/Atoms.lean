import EgglogSemantics.Proofs.Congruence.Target
import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.MatchEval
import EgglogSemantics.Proofs.Bindings

/-! Matching the atoms the compiler emits: an application over variables, a union-find
edge, and the equality and disequality tests of the maintenance rules. -/

namespace Egglog.Congruence

theorem Expr.matches_var_iff {d : Database} {σ : Env} {v : Var} :
    Expr.Matches d σ (.var v) ↔ ∃ t, Env.lookup v σ = some t := by
  constructor
  · intro h; cases h with | var hv => exact ⟨_, hv⟩
  · rintro ⟨t, ht⟩; exact .var ht

theorem Expr.matches_min_iff {d : Database} {σ : Env} {a b : Expr} :
    Expr.Matches d σ (.min a b) ↔ Expr.Matches d σ a ∧ Expr.Matches d σ b := by
  constructor
  · intro h; cases h with | min ha hb => exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩; exact .min ha hb

theorem Expr.matchesList_cons_iff {d : Database} {σ : Env} {e : Expr} {es : List Expr} :
    Expr.MatchesList d σ (e :: es) ↔ Expr.Matches d σ e ∧ Expr.MatchesList d σ es := by
  constructor
  · intro h; cases h with | cons he hes => exact ⟨he, hes⟩
  · rintro ⟨he, hes⟩; exact .cons he hes

/-- A list of bound variables matches. -/
theorem matchesList_map_var {d : Database} {σ : Env} : ∀ {vs : List Var},
    (∀ v ∈ vs, (Env.lookup v σ).isSome) → Expr.MatchesList d σ (vs.map Expr.var)
  | [], _ => .nil
  | v :: vs, h => by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h v (by simp))
      exact .cons (.var ht) (matchesList_map_var fun w hw => h w (by simp [hw]))

/-- An application atom: its arguments match and evaluate, and the instance is live. -/
theorem matches_app_iff {d : Database} {σ : Env} {f : FnName} {es : List Expr} :
    Matches d (.expr (.app f es)) σ ↔ ∃ ts, Expr.MatchesList d σ es ∧
      Expr.evalList es σ = some ts ∧ Term.app f ts ∈ d.live := by
  constructor
  · intro h
    cases h with
    | atom hl =>
      cases hl with
      | app hes hev hlive => exact ⟨_, hes, hev, hlive⟩
  · rintro ⟨ts, hes, hev, hlive⟩
    exact .atom (.app hes hev hlive)

/-- A union-find atom: both operands match and evaluate, and the edge is live. -/
theorem matches_uf_iff {d : Database} {σ : Env} {e₁ e₂ : Expr} :
    Matches d (.expr (ufRow e₁ e₂)) σ ↔ ∃ a b, Expr.Matches d σ e₁ ∧ Expr.Matches d σ e₂ ∧
      e₁.eval σ = some a ∧ e₂.eval σ = some b ∧ Edge d a b := by
  rw [ufRow, matches_app_iff]
  constructor
  · rintro ⟨ts, hes, hev, hlive⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := Expr.evalList_pair hev
    rw [Expr.matchesList_cons_iff, Expr.matchesList_cons_iff] at hes
    exact ⟨a, b, hes.1, hes.2.1, ha, hb, hlive⟩
  · rintro ⟨a, b, h₁, h₂, ha, hb, hlive⟩
    refine ⟨[a, b], .cons h₁ (.cons h₂ .nil), ?_, hlive⟩
    simp [Expr.evalList, ha, hb]

/-- A union-find atom over two variables. -/
theorem matches_uf_var_var_iff {d : Database} {σ : Env} {x y : Var} :
    Matches d (.expr (ufRow (.var x) (.var y))) σ ↔
      ∃ a b, Env.lookup x σ = some a ∧ Env.lookup y σ = some b ∧ Edge d a b := by
  rw [matches_uf_iff]
  constructor
  · rintro ⟨a, b, _, _, ha, hb, he⟩
    exact ⟨a, b, ha, hb, he⟩
  · rintro ⟨a, b, ha, hb, he⟩
    exact ⟨a, b, .var ha, .var hb, ha, hb, he⟩

theorem matches_eq_iff {d : Database} {σ : Env} {e₁ e₂ : Expr} :
    Matches d (.eq e₁ e₂) σ ↔ ∃ a b, Expr.Matches d σ e₁ ∧ Expr.Matches d σ e₂ ∧
      e₁.eval σ = some a ∧ e₂.eval σ = some b ∧ Cong d a b := by
  constructor
  · intro h
    cases h with
    | equal h₁ h₂ ha hb hc => exact ⟨_, _, h₁, h₂, ha, hb, hc⟩
  · rintro ⟨a, b, h₁, h₂, ha, hb, hc⟩
    exact .equal h₁ h₂ ha hb hc

theorem matches_ne_iff {d : Database} {σ : Env} {e₁ e₂ : Expr} :
    Matches d (.ne e₁ e₂) σ ↔ ∃ a b, Expr.Matches d σ e₁ ∧ Expr.Matches d σ e₂ ∧
      e₁.eval σ = some a ∧ e₂.eval σ = some b ∧ ¬ Cong d a b := by
  constructor
  · intro h
    cases h with
    | unequal h₁ h₂ ha hb hc => exact ⟨_, _, h₁, h₂, ha, hb, hc⟩
  · rintro ⟨a, b, h₁, h₂, ha, hb, hc⟩
    exact .unequal h₁ h₂ ha hb hc

/-- The disequality test of two variables. -/
theorem matches_ne_var_var_iff {d : Database} {σ : Env} {x y : Var} :
    Matches d (.ne (.var x) (.var y)) σ ↔
      ∃ a b, Env.lookup x σ = some a ∧ Env.lookup y σ = some b ∧ ¬ Cong d a b := by
  rw [matches_ne_iff]
  constructor
  · rintro ⟨a, b, _, _, ha, hb, hc⟩
    exact ⟨a, b, ha, hb, hc⟩
  · rintro ⟨a, b, ha, hb, hne⟩
    exact ⟨a, b, .var ha, .var hb, ha, hb, hne⟩

/-- On a diagonal state a held term is incongruent only to other terms. -/
theorem ne_of_not_cong {d : Database} {a b : Term} (ha : a ∈ d.terms)
    (h : ¬ Cong d a b) : a ≠ b := by
  rintro rfl
  exact h (Database.toCong ha)

theorem not_cong_of_ne {d : Database} (hd : d.Diag) {a b : Term} (h : a ≠ b) : ¬ Cong d a b :=
  fun hc => h (hc.eq_of_diag hd)

/-- The minimum test `x = min(x, y)` of the maintenance rules, on a diagonal state. -/
theorem matches_eq_min_iff {d : Database} (hd : d.Diag) {σ : Env} {x y : Var} :
    Matches d (.eq (.var x) (.min (.var x) (.var y))) σ ↔
      ∃ a b, Env.lookup x σ = some a ∧ Env.lookup y σ = some b ∧ a ∈ d.terms ∧
        a = Term.least a b := by
  rw [matches_eq_iff]
  constructor
  · rintro ⟨a, m, _, hm, ha, hmin, hc⟩
    rw [Expr.matches_min_iff, Expr.matches_var_iff, Expr.matches_var_iff] at hm
    obtain ⟨_, ⟨b, hb⟩⟩ := hm
    have hev : m = Term.least a b := by
      rw [Expr.eval_min] at hmin
      simp only [Expr.eval_var, ha, hb, Option.bind_some, Option.map_some,
        Option.some.injEq] at hmin
      exact hmin.symm
    obtain ⟨heq, hmem⟩ := (Cong.iff_eq_and_mem_of_diag hd).mp hc
    exact ⟨a, b, ha, hb, hmem, hev ▸ heq⟩
  · rintro ⟨a, b, ha, hb, hmem, heq⟩
    refine ⟨a, Term.least a b, .var ha, .min (.var ha) (.var hb), ha, ?_, ?_⟩
    · simp [Expr.eval, ha, hb]
    · rw [← heq]; exact Database.toCong hmem

end Egglog.Congruence
