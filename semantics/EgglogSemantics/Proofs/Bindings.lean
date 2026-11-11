import EgglogSemantics.Proofs.Match

/-! Evaluating variables and constructing tuple substitutions. -/

namespace Egglog

theorem Env.dom_zip_subset : ∀ (vs : List Var) (as : List Term), Env.dom (vs.zip as) ⊆ vs
  | [], _ => by simp [Env.dom]
  | _ :: _, [] => by simp [Env.dom]
  | v :: vs, a :: as => by
      intro w hw
      rw [List.zip_cons_cons, Env.dom_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Env.dom_zip_subset vs as hw)

theorem Env.lookup_zip : ∀ (vs : List Var) (as : List Term), vs.length = as.length →
    vs.Nodup → ∀ (i : Nat) (hi : i < vs.length) (hi' : i < as.length),
      Env.lookup vs[i] (vs.zip as) = some as[i]
  | [], [], _, _, i, hi, _ => by simp at hi
  | v :: vs, a :: as, hlen, hnd, 0, _, _ => by
      rw [List.zip_cons_cons, Env.lookup_cons]
      simp
  | v :: vs, a :: as, hlen, hnd, i + 1, hi, hi' => by
      rw [List.nodup_cons] at hnd
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi hi'
      have hne : vs[i] ≠ v := fun hc => hnd.1 (hc ▸ List.getElem_mem hi)
      rw [List.zip_cons_cons]
      simp only [List.getElem_cons_succ]
      rw [Env.lookup_cons, if_neg hne]
      exact Env.lookup_zip vs as (by simpa using hlen) hnd.2 i hi hi'

/-- **A list of variables evaluates to what the environment binds them to.** -/
theorem Expr.evalList_map_var : ∀ (vs : List Var) (as : List Term) (ρ : Env),
    vs.length = as.length →
    (∀ (i : Nat) (hi : i < vs.length) (hi' : i < as.length), Env.lookup vs[i] ρ = some as[i]) →
    Expr.evalList (vs.map Expr.var) ρ = some as
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | v :: vs, a :: as, ρ, hlen, h => by
      have h0 : Env.lookup v ρ = some a := h 0 (by simp) (by simp)
      have hrest : Expr.evalList (vs.map Expr.var) ρ = some as :=
        Expr.evalList_map_var vs as ρ (by simpa using hlen)
          (fun i hi hi' => h (i + 1) (by simpa using hi) (by simpa using hi'))
      have hev : Expr.eval (.var v) ρ = some a := h0
      rw [List.map_cons, Expr.evalList, hev, Option.bind_some, hrest]
      rfl

/-- The value at one position is that operand's. -/
theorem Expr.getElem?_of_evalList {ρ : Env} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList es ρ = some ts →
      ∀ (i : Nat) {e : Expr}, es[i]? = some e →
        ∃ t, ts[i]? = some t ∧ e.eval ρ = some t
  | [], _, _, i, _, hi => by simp at hi
  | e :: es, _, h, 0, e', hi => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain rfl : e = e' := by simpa using hi
      exact ⟨u, by simp, hu⟩
  | e :: es, _, h, i + 1, e', hi => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain ⟨t, ht, hev⟩ := Expr.getElem?_of_evalList hus i (by simpa using hi)
      exact ⟨t, by simpa using ht, hev⟩

/-- A one-element operand list. -/
theorem Expr.evalList_singleton {σ : Env} {e : Expr} {ts : List Term}
    (h : Expr.evalList [e] σ = some ts) : ∃ t, e.eval σ = some t ∧ ts = [t] := by
  rw [Expr.evalList] at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
  rw [Expr.evalList, Option.map_some, Option.some.injEq] at h
  exact ⟨t, ht, h.symm⟩

/-- Evaluate a pair of operands. -/
theorem Expr.evalList_pair {σ : Env} {e₁ e₂ : Expr} {ts : List Term}
    (h : Expr.evalList [e₁, e₂] σ = some ts) :
    ∃ t₁ t₂, e₁.eval σ = some t₁ ∧ e₂.eval σ = some t₂ ∧ ts = [t₁, t₂] := by
  rw [Expr.evalList] at h
  obtain ⟨t₁, ht₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨t₂, ht₂, rfl⟩ := Expr.evalList_singleton hus
  exact ⟨t₁, t₂, ht₁, ht₂, rfl⟩

end Egglog
