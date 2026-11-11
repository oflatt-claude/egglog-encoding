import EgglogSemantics.Proofs.Congruence.Atoms
import EgglogSemantics.Proofs.Presentation
import EgglogSemantics.Proofs.Writes

/-! The maintenance rules of the view-free encoding: the rebuild is one saturation of the
list `maintenance P`, and a firing of each rule is characterized by the live edges it
matched and the rows it writes and marks. -/

namespace Egglog.Congruence

/-- The maintenance rules without their origins. -/
def maintenance (P : Program) : List Rule := (maintenanceRules P).map Prod.fst

theorem rebuild_eq (P : Program) : (rebuildWith {} P).1 = .saturate (.run (maintenance P)) := by
  simp only [rebuildWith, maintenanceGroups, maintenance, maintenanceRules]
  have hrekey : ∀ fk : FnName × Nat, rekeyRules {} fk.1 fk.2 = [] := fun _ => rfl
  have hmerge : ∀ fk : FnName × Nat, mergeRules {} fk.1 fk.2 = rebuildRules fk.1 fk.2 :=
    fun _ => rfl
  have h0 : P.ctors.flatMap (fun _ => ([] : List (Rule × RuleOrigin))) = [] :=
    List.flatMap_eq_nil_iff.mpr fun _ _ => rfl
  simp only [hrekey, hmerge, h0, Bool.false_eq_true, ↓reduceIte,
    List.flatten_filter_not_isEmpty, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.nil_append, List.cons_append, List.map_cons]

theorem mem_maintenance {P : Program} {r : Rule} :
    r ∈ maintenance P ↔ r = pathCompressRule ∨ r = ufCollideRule ∨
      ∃ fk ∈ P.ctors, fk.2 ≠ 0 ∧ r = congruenceRule fk.1 fk.2 := by
  simp only [maintenance, maintenanceRules, List.map_cons, List.mem_cons, List.map_flatMap,
    List.mem_flatMap, rebuildRules]
  apply or_congr_right
  apply or_congr_right
  constructor
  · rintro ⟨fk, hfk, hr⟩
    split at hr
    · simp at hr
    · next hne =>
      rw [List.map_singleton, List.mem_singleton] at hr
      exact ⟨fk, hfk, hne, hr⟩
  · rintro ⟨fk, hfk, hne, rfl⟩
    refine ⟨fk, hfk, ?_⟩
    rw [if_neg hne]
    simp

/-! ### Path compression -/

theorem compress_inv {d : Database} {σ : Env} (hq : QueryMatches d pathCompressRule.query σ) :
    ∃ a b c, Env.lookup "@a" σ = some a ∧ Env.lookup "@b" σ = some b ∧
      Env.lookup "@c" σ = some c ∧ Edge d a b ∧ Edge d b c ∧ ¬ Cong d b c := by
  have h₁ := hq.2 (.expr (ufRow (.var "@a") (.var "@b"))) (by simp [pathCompressRule])
  have h₂ := hq.2 (.expr (ufRow (.var "@b") (.var "@c"))) (by simp [pathCompressRule])
  have h₃ := hq.2 (.ne (.var "@b") (.var "@c")) (by simp [pathCompressRule])
  obtain ⟨a, b, ha, hb, hab⟩ := matches_uf_var_var_iff.mp h₁
  obtain ⟨b', c, hb', hc, hbc⟩ := matches_uf_var_var_iff.mp h₂
  obtain ⟨b'', c', hb'', hc', hne⟩ := matches_ne_var_var_iff.mp h₃
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : b = b'' := Option.some.inj (hb.symm.trans hb'')
  obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
  exact ⟨a, b, c, ha, hb, hc, hab, hbc, hne⟩

theorem compress_writes {σ : Env} {a b c : Term} (ha : Env.lookup "@a" σ = some a)
    (hb : Env.lookup "@b" σ = some b) (hc : Env.lookup "@c" σ = some c) :
    Action.writes σ pathCompressRule.actions =
      some ({(ufRowT a b, ufRowT a b)} ∪ ({(ufRowT a c, ufRowT a c)} ∪ ∅)) := by
  simp [pathCompressRule, Action.writes, Action.write, subsumeUf, ufRow, Expr.eval,
    Expr.evalList, ha, hb, hc]

theorem compress_marks {σ : Env} {a b : Term} (ha : Env.lookup "@a" σ = some a)
    (hb : Env.lookup "@b" σ = some b) (hc : (Env.lookup "@c" σ).isSome) :
    Action.marks σ pathCompressRule.actions = some ({ufRowT a b} ∪ (∅ ∪ ∅)) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
  simp [pathCompressRule, Action.marks, Action.mark, Action.write, subsumeUf, ufRow, Expr.eval,
    Expr.evalList, ha, hb, hc]

/-! ### Collisions -/

theorem collide_query : ufCollideRule.query =
    [.expr (ufRow (.var "@a") (.var "@b")), .expr (ufRow (.var "@a") (.var "@c")),
     .eq (.var "@b") (.min (.var "@b") (.var "@c")), .ne (.var "@b") (.var "@c")] := rfl

theorem collide_actions : ufCollideRule.actions =
    [subsumeUf (.var "@a") (.var "@c"), .expr (ufRow (.var "@c") (.var "@b"))] := rfl

theorem collide_inv {d : Database} (hd : d.Diag) {σ : Env}
    (hq : QueryMatches d ufCollideRule.query σ) :
    ∃ a b c, Env.lookup "@a" σ = some a ∧ Env.lookup "@b" σ = some b ∧
      Env.lookup "@c" σ = some c ∧ Edge d a b ∧ Edge d a c ∧ b = Term.least b c ∧ ¬ Cong d b c := by
  have h₁ := hq.2 (.expr (ufRow (.var "@a") (.var "@b"))) (by rw [collide_query]; simp)
  have h₂ := hq.2 (.expr (ufRow (.var "@a") (.var "@c"))) (by rw [collide_query]; simp)
  have h₃ := hq.2 (.eq (.var "@b") (.min (.var "@b") (.var "@c"))) (by rw [collide_query]; simp)
  have h₄ := hq.2 (.ne (.var "@b") (.var "@c")) (by rw [collide_query]; simp)
  obtain ⟨a, b, ha, hb, hab⟩ := matches_uf_var_var_iff.mp h₁
  obtain ⟨a', c, ha', hc, hac⟩ := matches_uf_var_var_iff.mp h₂
  obtain ⟨b', c', hb', hc', _, hmin⟩ := (matches_eq_min_iff hd).mp h₃
  obtain ⟨b'', c'', hb'', hc'', hne⟩ := matches_ne_var_var_iff.mp h₄
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
  obtain rfl : b = b'' := Option.some.inj (hb.symm.trans hb'')
  obtain rfl : c = c'' := Option.some.inj (hc.symm.trans hc'')
  exact ⟨a, b, c, ha, hb, hc, hab, hac, hmin, hne⟩

theorem collide_writes {σ : Env} {a b c : Term} (ha : Env.lookup "@a" σ = some a)
    (hb : Env.lookup "@b" σ = some b) (hc : Env.lookup "@c" σ = some c) :
    Action.writes σ ufCollideRule.actions =
      some ({(ufRowT a c, ufRowT a c)} ∪ ({(ufRowT c b, ufRowT c b)} ∪ ∅)) := by
  rw [collide_actions]
  simp [Action.writes, Action.write, subsumeUf, ufRow, Expr.eval, Expr.evalList, ha, hb, hc]

theorem collide_marks {σ : Env} {a b c : Term} (ha : Env.lookup "@a" σ = some a)
    (hb : Env.lookup "@b" σ = some b) (hc : Env.lookup "@c" σ = some c) :
    Action.marks σ ufCollideRule.actions = some ({ufRowT a c} ∪ (∅ ∪ ∅)) := by
  rw [collide_actions]
  simp [Action.marks, Action.mark, Action.write, subsumeUf, ufRow, Expr.eval, Expr.evalList,
    ha, hb, hc]

/-! ### Congruence -/

theorem congruenceVars_length (stem : String) (n : Nat) : (congruenceVars stem n).length = n := by
  simp [congruenceVars]

theorem congruenceVars_getElem (stem : String) {n i : Nat} (hi : i < n) :
    (congruenceVars stem n)[i]'(by rw [congruenceVars_length]; exact hi) =
      .var ("@" ++ stem ++ toString i) := by
  simp [congruenceVars]

theorem congruenceVars_getElem? (stem : String) {n i : Nat} (hi : i < n) :
    (congruenceVars stem n)[i]? = some (.var ("@" ++ stem ++ toString i)) := by
  rw [List.getElem?_eq_getElem (by rw [congruenceVars_length]; exact hi),
    congruenceVars_getElem stem hi]

theorem congruence_query (f : FnName) (n : Nat) : (congruenceRule f n).query =
    [.expr (.app f (congruenceVars "a" n)), .expr (.app f (congruenceVars "b" n))] ++
      (((congruenceVars "a" n).zip (congruenceVars "b" n)).zip (congruenceVars "r" n)).flatMap
        (fun abr => [.expr (ufRow abr.1.1 abr.2), .expr (ufRow abr.1.2 abr.2)]) ++
      [.expr (ufRow (.app f (congruenceVars "a" n)) (.var "@y")),
       .expr (ufRow (.app f (congruenceVars "b" n)) (.var "@z")),
       .eq (.var "@y") (.min (.var "@y") (.var "@z")), .ne (.var "@y") (.var "@z")] := rfl

theorem congruence_actions (f : FnName) (n : Nat) :
    (congruenceRule f n).actions = [.expr (ufRow (.var "@z") (.var "@y"))] := rfl

/-- The edge atoms of the congruence rule, one pair per column. -/
theorem congruence_edge_atoms_mem {f : FnName} {n i : Nat} (hi : i < n) :
    Pattern.expr (ufRow (.var ("@" ++ "a" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈
        (congruenceRule f n).query ∧
      Pattern.expr (ufRow (.var ("@" ++ "b" ++ toString i)) (.var ("@" ++ "r" ++ toString i))) ∈
        (congruenceRule f n).query := by
  rw [congruence_query]
  have hlen : i < (((congruenceVars "a" n).zip (congruenceVars "b" n)).zip
      (congruenceVars "r" n)).length := by
    simp [congruenceVars_length, hi]
  have hmem : ((Expr.var ("@" ++ "a" ++ toString i), Expr.var ("@" ++ "b" ++ toString i)),
      Expr.var ("@" ++ "r" ++ toString i)) ∈
      ((congruenceVars "a" n).zip (congruenceVars "b" n)).zip (congruenceVars "r" n) := by
    rw [List.mem_iff_getElem]
    refine ⟨i, hlen, ?_⟩
    rw [List.getElem_zip, List.getElem_zip, congruenceVars_getElem "a" hi,
      congruenceVars_getElem "b" hi, congruenceVars_getElem "r" hi]
  constructor
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_, hmem, by simp⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_, hmem, by simp⟩

/-- The value of a congruence variable from the evaluated list. -/
theorem congruence_lookup {σ : Env} {stem : String} {n : Nat} {ts : List Term}
    (hts : Expr.evalList (congruenceVars stem n) σ = some ts) {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ stem ++ toString i) σ = ts[i]? := by
  obtain ⟨t, ht, hev⟩ := Expr.getElem?_of_evalList hts i (congruenceVars_getElem? stem hi)
  rw [ht]
  exact hev

theorem congruence_inv {d : Database} (hd : d.Diag) {σ : Env} {f : FnName} {n : Nat}
    (hq : QueryMatches d (congruenceRule f n).query σ) :
    ∃ as bs rs y z, Expr.evalList (congruenceVars "a" n) σ = some as ∧
      Expr.evalList (congruenceVars "b" n) σ = some bs ∧
      Expr.evalList (congruenceVars "r" n) σ = some rs ∧
      Env.lookup "@y" σ = some y ∧ Env.lookup "@z" σ = some z ∧
      Term.app f as ∈ d.live ∧ Term.app f bs ∈ d.live ∧
      List.Forall₂ (Edge d) as rs ∧ List.Forall₂ (Edge d) bs rs ∧
      Edge d (.app f as) y ∧ Edge d (.app f bs) z ∧ y = Term.least y z ∧ ¬ Cong d y z := by
  have hm := hq.2
  rw [congruence_query] at hm
  have hA := hm (.expr (.app f (congruenceVars "a" n))) (by simp)
  have hB := hm (.expr (.app f (congruenceVars "b" n))) (by simp)
  have hY := hm (.expr (ufRow (.app f (congruenceVars "a" n)) (.var "@y"))) (by simp)
  have hZ := hm (.expr (ufRow (.app f (congruenceVars "b" n)) (.var "@z"))) (by simp)
  have hmin := hm (.eq (.var "@y") (.min (.var "@y") (.var "@z"))) (by simp)
  have hne := hm (.ne (.var "@y") (.var "@z")) (by simp)
  obtain ⟨as, _, has, hliveA⟩ := matches_app_iff.mp hA
  obtain ⟨bs, _, hbs, hliveB⟩ := matches_app_iff.mp hB
  obtain ⟨ta, y, _, _, hta, hy, hey⟩ := matches_uf_iff.mp hY
  obtain ⟨tb, z, _, _, htb, hz, hez⟩ := matches_uf_iff.mp hZ
  obtain ⟨y', z', hy', hz', _, hyz⟩ := (matches_eq_min_iff hd).mp hmin
  obtain ⟨y'', z'', hy'', hz'', hnyz⟩ := matches_ne_var_var_iff.mp hne
  obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : y = y'' := Option.some.inj (hy.symm.trans hy'')
  obtain rfl : z = z'' := Option.some.inj (hz.symm.trans hz'')
  obtain rfl : ta = Term.app f as := by
    rw [Expr.eval_app_ctor, has] at hta
    exact (Option.some.inj hta).symm
  obtain rfl : tb = Term.app f bs := by
    rw [Expr.eval_app_ctor, hbs] at htb
    exact (Option.some.inj htb).symm
  -- The column variables are all bound, so the parents evaluate.
  have hdom : ∀ v ∈ Expr.varsList (congruenceVars "r" n), v ∈ Env.dom σ := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Expr.mem_varsList hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    rw [congruenceVars_length] at hi
    rw [congruenceVars_getElem "r" hi] at hve
    simp only [Expr.vars_var, List.mem_singleton] at hve
    subst hve
    apply hq.1.1.mem_iff.mpr
    rw [Query.mem_vars]
    refine ⟨_, (congruence_edge_atoms_mem (f := f) hi).1, ?_⟩
    simp [Pattern.vars, ufRow, Expr.vars, Expr.varsList]
  obtain ⟨rs, hrs⟩ := Expr.evalList_isSome (congruenceVars "r" n) hdom
  have hlenA : as.length = n := by rw [Expr.evalList_length has, congruenceVars_length]
  have hlenB : bs.length = n := by rw [Expr.evalList_length hbs, congruenceVars_length]
  have hlenR : rs.length = n := by rw [Expr.evalList_length hrs, congruenceVars_length]
  have edges : ∀ (stem : String) (ts : List Term),
      Expr.evalList (congruenceVars stem n) σ = some ts →
      (∀ i, i < n → Pattern.expr (ufRow (.var ("@" ++ stem ++ toString i))
        (.var ("@" ++ "r" ++ toString i))) ∈ (congruenceRule f n).query) →
      List.Forall₂ (Edge d) ts rs := by
    intro stem ts hts hatoms
    have hlen : ts.length = n := by rw [Expr.evalList_length hts, congruenceVars_length]
    rw [List.forall₂_iff_get]
    refine ⟨by rw [hlen, hlenR], fun i h₁ h₂ => ?_⟩
    have hi : i < n := hlen ▸ h₁
    obtain ⟨u, r, hu, hr, hur⟩ := matches_uf_var_var_iff.mp (hq.2 _ (hatoms i hi))
    have hu' := congruence_lookup hts hi
    have hr' := congruence_lookup hrs hi
    rw [hu, List.getElem?_eq_getElem h₁] at hu'
    rw [hr, List.getElem?_eq_getElem h₂] at hr'
    simp only [List.get_eq_getElem]
    rw [← Option.some.inj hu', ← Option.some.inj hr']
    exact hur
  refine ⟨as, bs, rs, y, z, has, hbs, hrs, hy, hz, hliveA, hliveB, ?_, ?_, hey, hez, hyz, hnyz⟩
  · exact edges "a" as has fun i hi => (congruence_edge_atoms_mem hi).1
  · exact edges "b" bs hbs fun i hi => (congruence_edge_atoms_mem hi).2

theorem congruence_writes {σ : Env} {f : FnName} {n : Nat} {y z : Term}
    (hy : Env.lookup "@y" σ = some y) (hz : Env.lookup "@z" σ = some z) :
    Action.writes σ (congruenceRule f n).actions = some ({(ufRowT z y, ufRowT z y)} ∪ ∅) := by
  rw [congruence_actions]
  simp [Action.writes, Action.write, ufRow, Expr.eval, Expr.evalList, hy, hz]

theorem congruence_marks {σ : Env} {f : FnName} {n : Nat} {y z : Term}
    (hy : Env.lookup "@y" σ = some y) (hz : Env.lookup "@z" σ = some z) :
    Action.marks σ (congruenceRule f n).actions = some (∅ ∪ ∅) := by
  rw [congruence_actions]
  simp [Action.marks, Action.mark, Action.write, ufRow, Expr.eval, Expr.evalList, hy, hz]

end Egglog.Congruence
