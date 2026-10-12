import EgglogSemantics.Congruence.Encode

/-! The flattening pass emits only flat entry atoms and equalities of leaves. -/

namespace Egglog.Congruence

/-- An id expression usable as one column of a flat query. -/
def Leaf : Expr → Prop
  | .lit _ | .var _ => True
  | .app _ _ => False

/-- Complete entry atoms have only leaf columns; equalities compare leaves. -/
def FlatPattern : Pattern → Prop
  | .expr (.app _ es) => ∀ e ∈ es, Leaf e
  | .expr _ => False
  | .eq a b => Leaf a ∧ Leaf b

mutual

/-- The returned id is a leaf and all emitted atoms are flat. -/
theorem encodeQueryExpr_flat : ∀ (e : Expr) (n : Nat),
    Leaf (encodeQueryExpr e n).1 ∧ ∀ p ∈ (encodeQueryExpr e n).2.1, FlatPattern p
  | .lit _, _ | .var _, _ => ⟨trivial, by simp [encodeQueryExpr]⟩
  | .app f es, n => by
      obtain ⟨hids, hps⟩ := encodeQueryArgs_flat es n
      refine ⟨trivial, ?_⟩
      intro p hp
      change p ∈ (encodeQueryArgs es n).2.1 ++ [_] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hps p hp
      · obtain rfl := List.mem_singleton.mp hp
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hids e he
        · obtain rfl := List.mem_singleton.mp he
          trivial

/-- Argument ids and their emitted atoms satisfy the same invariant. -/
theorem encodeQueryArgs_flat : ∀ (es : List Expr) (n : Nat),
    (∀ e ∈ (encodeQueryArgs es n).1, Leaf e) ∧
      ∀ p ∈ (encodeQueryArgs es n).2.1, FlatPattern p
  | [], _ => ⟨by simp [encodeQueryArgs], by simp [encodeQueryArgs]⟩
  | e :: es, n => by
      obtain ⟨he, hp⟩ := encodeQueryExpr_flat e n
      obtain ⟨hes, hps⟩ := encodeQueryArgs_flat es (encodeQueryExpr e n).2.2
      constructor
      · intro x hx
        change x ∈ (encodeQueryExpr e n).1 :: _ at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he
        · exact hes x hx
      · intro p h
        change p ∈ (encodeQueryExpr e n).2.1 ++ _ at h
        rcases List.mem_append.mp h with h | h
        · exact hp p h
        · exact hps p h

end

theorem encodePattern_flat (p : Pattern) (n : Nat) :
    ∀ q ∈ (encodePattern p n).1, FlatPattern q := by
  cases p with
  | expr e => exact (encodeQueryExpr_flat e n).2
  | eq a b =>
      obtain ⟨ha, hpa⟩ := encodeQueryExpr_flat a n
      obtain ⟨hb, hpb⟩ := encodeQueryExpr_flat b (encodeQueryExpr a n).2.2
      intro q hq
      change q ∈ (_ ++ _) ++ [_] at hq
      rcases List.mem_append.mp hq with hq | hq
      · rcases List.mem_append.mp hq with hq | hq
        · exact hpa q hq
        · exact hpb q hq
      · obtain rfl := List.mem_singleton.mp hq
        exact ⟨ha, hb⟩

/-- Every source query compiles to flat atoms, independent of source-domain assumptions. -/
theorem encodeQuery_flat (q : Query) (n : Nat) :
    ∀ p ∈ (encodeQuery q n).1, FlatPattern p := by
  induction q generalizing n with
  | nil => simp [encodeQuery]
  | cons p ps ih =>
      intro q hq
      change q ∈ (encodePattern p n).1 ++ _ at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact encodePattern_flat p n q hq
      · exact ih (encodePattern p n).2 q hq

mutual

/-- Exactly one fresh id per application occurrence. This fixes the recursion's premise
positions without retaining any extra flattening metadata. -/
theorem encodeQueryExpr_next : ∀ (e : Expr) (n : Nat),
    (encodeQueryExpr e n).2.2 = n + e.ctors.length
  | .lit _, _ | .var _, _ => rfl
  | .app _ es, n => by
      change (encodeQueryArgs es n).2.2 + 1 = _
      rw [encodeQueryArgs_next]
      simp only [Expr.ctors, List.length_cons]
      omega

@[inherit_doc encodeQueryExpr_next]
theorem encodeQueryArgs_next : ∀ (es : List Expr) (n : Nat),
    (encodeQueryArgs es n).2.2 = n + (Expr.ctorsList es).length
  | [], _ => rfl
  | e :: es, n => by
      change (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.2 = _
      rw [encodeQueryArgs_next, encodeQueryExpr_next]
      simp [Expr.ctorsList, Nat.add_assoc]

end

end Egglog.Congruence
