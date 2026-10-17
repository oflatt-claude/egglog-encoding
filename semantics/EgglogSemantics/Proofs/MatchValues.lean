import EgglogSemantics.Proofs.Match

/-! Keyed, order-free queries bind constructor values in typed stores. -/

namespace Egglog

/-- Every query variable is witnessed below an application, without a discarded computation arm. -/
def Query.Safe (q : Query) : Prop := q.VarsKeyed ∧ ∀ p ∈ q, p.OrderingFree

def Database.RulesSafe (d : Database) : Prop := ∀ r ∈ d.rules, r.query.Safe

@[simp] def Term.ChildrenValues (sig : Signature) : Term → Prop
  | .lit _ => True
  | .app _ ts => ∀ t ∈ ts, t.IsValue sig

theorem Term.IsValue.childrenValues {sig : Signature} {t : Term}
    (ht : t.IsValue sig) : t.ChildrenValues sig := by
  cases t with
  | lit => trivial
  | app => exact (Term.isValue_app_iff.mp ht).2

theorem Term.Stored.childrenValues {sig : Signature} {t : Term}
    (ht : t.Stored sig) : t.ChildrenValues sig := by
  rcases ht with ht | ⟨row, hr, rfl⟩
  · exact ht.childrenValues
  · exact hr.column_values

private def ValueShapeEq (sig : Signature) (a b : Term) : Prop :=
  (a.IsValue sig ↔ b.IsValue sig) ∧ (a.ChildrenValues sig ↔ b.ChildrenValues sig)

private theorem congr_valueShape {db : Database} {sig : Signature}
    (hdb : ∀ p ∈ db.eqs, ValueShapeEq sig p.1 p.2) {a b : Term} (h : StoredCong db a b) :
    ValueShapeEq sig a b := by
  induction h using StoredCong.rec
      (motive_2 := fun as bs _ => (∀ a ∈ as, a.IsValue sig) ↔ ∀ b ∈ bs, b.IsValue sig) with
  | direct h => exact hdb _ h
  | subterm => exact ⟨Iff.rfl, Iff.rfl⟩
  | symm _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₁.2.trans ih₂.2⟩
  | congr _ _ _ _ _ ih =>
      exact ⟨by simp only [Term.isValue_app_iff, ih], ih⟩
  | nil => rfl
  | cons _ _ ih ihs =>
      simpa only [List.forall_mem_cons] using and_congr ih.1 ihs

private theorem Database.StoreOk.valueShape {db : Database} (hs : db.StoreOk) :
    ∀ p ∈ db.eqs, ValueShapeEq db.sig p.1 p.2 := by
  intro p hp
  rcases hs.typed p hp with ⟨ha, hb⟩ | ⟨row, _, rfl⟩
  · exact ⟨iff_of_true ha hb, iff_of_true ha.childrenValues hb.childrenValues⟩
  · exact ⟨Iff.rfl, Iff.rfl⟩

private theorem valueShape_addTerms {db : Database} {sig : Signature}
    (hdb : ∀ p ∈ db.eqs, ValueShapeEq sig p.1 p.2) (ts : List Term) :
    ∀ p ∈ (db.addTerms ts).eqs, ValueShapeEq sig p.1 p.2 := by
  induction ts generalizing db with
  | nil => exact hdb
  | cons t ts ih =>
      apply ih
      rintro p (rfl | hp)
      · exact ⟨Iff.rfl, Iff.rfl⟩
      · exact hdb p hp

theorem StoredCongOn.childrenValues {db : Database} {ts : List Term} {a b : Term}
    (hs : db.StoreOk) (h : StoredCongOn db ts a b) (ha : a.ChildrenValues db.sig) :
    b.ChildrenValues db.sig :=
  (congr_valueShape (valueShape_addTerms hs.valueShape ts) h).2.mp ha

mutual

private theorem Expr.eval_vars_values {sig : Signature} {σ : Env} {e : Expr} {t : Term}
    (ho : e.OrderingFree) (he : e.eval sig σ = some t) (ht : t.IsValue sig) :
    ∀ v ∈ e.vars, ∀ u, Env.lookup v σ = some u → u.IsValue sig := by
  match e with
  | .lit _ => simp [Expr.vars]
  | .var x =>
      intro v hv u hu
      obtain rfl : v = x := List.mem_singleton.mp hv
      obtain rfl : t = u := Option.some.inj (he.symm.trans hu)
      exact ht
  | .app f args =>
      by_cases hc : sig.IsCtor f
      · rw [Expr.eval_app_ctor hc] at he
        obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
        exact Expr.evalList_vars_values ho hts (Term.isValue_app_iff.mp ht).2
      · simp [Expr.eval_app_not_ctor hc] at he
  | .min _ _ | .ite _ _ _ _ => simp [Expr.OrderingFree, Expr.hasMin] at ho

private theorem Expr.evalList_vars_values {sig : Signature} {σ : Env}
    {es : List Expr} {ts : List Term} (ho : Expr.OrderingFreeList es)
    (he : Expr.evalList sig es σ = some ts) (ht : ∀ t ∈ ts, t.IsValue sig) :
    ∀ v ∈ Expr.varsList es, ∀ u, Env.lookup v σ = some u → u.IsValue sig := by
  match es with
  | [] => simp [Expr.varsList]
  | e :: es =>
      obtain ⟨t, hte, hrest⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ho' : e.OrderingFree ∧ Expr.OrderingFreeList es :=
        Bool.or_eq_false_iff.mp ho
      intro v hv u hu
      rcases List.mem_union_iff.mp hv with hv | hv
      · exact Expr.eval_vars_values ho'.1 hte (ht t List.mem_cons_self) v hv u hu
      · exact Expr.evalList_vars_values ho'.2 hus
          (fun t hm => ht t (List.mem_cons_of_mem _ hm)) v hv u hu

end

private theorem Expr.var_mem_varsList {v : Var} :
    ∀ {es : List Expr}, Expr.var v ∈ es → v ∈ Expr.varsList es
  | [], h => by simp at h
  | e :: es, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp [Expr.varsList, Expr.vars]
      · exact List.mem_union_iff.mpr (Or.inr (Expr.var_mem_varsList h))

mutual

private theorem Expr.argVar_mem_vars {v : Var} : ∀ {e : Expr}, e.ArgVar v → v ∈ e.vars
  | .lit _, h => h.elim
  | .var _, h => h.elim
  | .ite _ _ _ _, h => h.elim
  | .app _ _, h => h.elim Expr.var_mem_varsList Expr.argVarList_mem_vars
  | .min _ _, h => h.elim
      (fun h => List.mem_union_iff.mpr (Or.inl (Expr.argVar_mem_vars h)))
      (fun h => List.mem_union_iff.mpr (Or.inr (Expr.argVar_mem_vars h)))

private theorem Expr.argVarList_mem_vars {v : Var} :
    ∀ {es : List Expr}, Expr.ArgVarList v es → v ∈ Expr.varsList es
  | [], h => h.elim
  | _ :: _, h => h.elim
      (fun h => List.mem_union_iff.mpr (Or.inl (Expr.argVar_mem_vars h)))
      (fun h => List.mem_union_iff.mpr (Or.inr (Expr.argVarList_mem_vars h)))

end

private theorem Expr.eval_argVar_values {sig : Signature} {σ : Env} {e : Expr} {t : Term}
    (ho : e.OrderingFree) (he : e.eval sig σ = some t) (ht : t.ChildrenValues sig)
    {v : Var} (hv : e.ArgVar v) {u : Term} (hu : Env.lookup v σ = some u) : u.IsValue sig := by
  cases e with
  | lit | var => exact hv.elim
  | min | ite => simp [Expr.OrderingFree, Expr.hasMin] at ho
  | app f args =>
      by_cases hc : sig.IsCtor f
      · rw [Expr.eval_app_ctor hc] at he
        obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
        exact Expr.evalList_vars_values ho hts ht v (Expr.argVar_mem_vars hv) u hu
      · simp [Expr.eval_app_not_ctor hc] at he

private theorem Expr.evalAtom_argVar_values {sig : Signature} {σ : Env} {e : Expr} {t : Term}
    (ho : e.OrderingFree) (he : e.evalAtom sig σ = some t) (ht : t.ChildrenValues sig)
    {v : Var} (hv : e.ArgVar v) {u : Term} (hu : Env.lookup v σ = some u) : u.IsValue sig := by
  cases e with
  | lit | var => exact hv.elim
  | min | ite => simp [Expr.OrderingFree, Expr.hasMin] at ho
  | app f args =>
      obtain ⟨ts, hts, rfl⟩ := Expr.evalAtom_app_inv he
      exact Expr.evalList_vars_values ho hts ht v (Expr.argVar_mem_vars hv) u hu

theorem Matches.argVar_value {db : Database} {p : Pattern} {σ : Env}
    (h : Matches db p σ) (hs : db.StoreOk) (ho : p.OrderingFree)
    {v : Var} (hv : p.ArgVar v) {u : Term} (hu : Env.lookup v σ = some u) : u.IsValue db.sig := by
  cases h using Matches.storedCases with
  | expr hw he hc =>
      exact Expr.evalAtom_argVar_values ho he
        (hc.childrenValues hs (hs.term hw).childrenValues) hv hu
  | eq hw he₁ he₂ hc₁ hc₂ =>
      have ht₁ := hc₁.childrenValues hs (hs.term hw).childrenValues
      exact hv.elim (fun hv => Expr.eval_argVar_values ho.1 he₁ ht₁ hv hu)
        (fun hv => Expr.eval_argVar_values ho.2 he₂ (hc₂.childrenValues hs ht₁) hv hu)

theorem ValidQuerySubst.mem_values {db : Database} {q : Query} {σ : Env}
    (h : ValidQuerySubst db q σ) (hs : db.StoreOk) (hq : q.Safe) :
    ∀ b ∈ σ, b.2 ∈ db.values := by
  have hr : Env.Refines σ σ := by
    obtain ⟨σs, hall, hu⟩ := h
    apply (hu.refines_of_mem ?_).2
    intro τ hτ
    obtain ⟨p, _, hp⟩ := hall.exists_left hτ
    exact Env.Refines.self_of_nodup (hp.validEnv.1.symm.nodup (p.freeVars_nodup []))
  intro b hb
  obtain ⟨p, hp, hv⟩ := h.mem_dom_iff.mp (Env.mem_dom_of_mem hb)
  obtain ⟨p', hp', hv'⟩ := hq.1 b.1 (Query.mem_vars.mpr ⟨p, hp, (p.mem_freeVars.mp hv).1⟩)
  exact ⟨h.mem_terms b hb, (h.matches_of_mem hp').argVar_value hs (hq.2 p' hp') hv' (hr b hb)⟩

end Egglog
