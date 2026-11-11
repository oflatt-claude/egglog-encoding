import EgglogSemantics.Proofs.Congruence.Invariant
import EgglogSemantics.Proofs.Congruence.Rules
import EgglogSemantics.Proofs.Source.RebuildVars
import EgglogSemantics.Proofs.Query

/-! Firing the maintenance rules: from live edges that a rule's query describes, the
substitution the rule matches. Used to show that a rebuild fixpoint is canonical. -/

namespace Egglog.Congruence

/-! ### Path compression and collisions -/

/-- The substitution of the two union-find rules. -/
def ufEnv (a b c : Term) : Env := [("@a", a), ("@b", b), ("@c", c)]

theorem ufEnv_lookup_a (a b c : Term) : Env.lookup "@a" (ufEnv a b c) = some a := rfl
theorem ufEnv_lookup_b (a b c : Term) : Env.lookup "@b" (ufEnv a b c) = some b := rfl
theorem ufEnv_lookup_c (a b c : Term) : Env.lookup "@c" (ufEnv a b c) = some c := rfl

theorem ufEnv_mem {a b c : Term} {x : Var × Term} (h : x ∈ ufEnv a b c) :
    x.2 = a ∨ x.2 = b ∨ x.2 = c := by
  simp only [ufEnv, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp

theorem compress_fire {d : Database} (hd : d.Diag) {a b c : Term} (hab : Edge d a b)
    (hbc : Edge d b c) (hne : b ≠ c) (ha : a ∈ d.terms) (hb : b ∈ d.terms) (hc : c ∈ d.terms) :
    QueryMatches d pathCompressRule.query (ufEnv a b c) := by
  refine ⟨⟨?_, fun x hx => ?_⟩, fun p hp => ?_⟩
  · change (["@a", "@b", "@c"] : List Var).Perm (Query.vars pathCompressRule.query)
    decide
  · rw [hd.reps_eq_terms]
    rcases ufEnv_mem hx with h | h | h <;> rw [h] <;> assumption
  · simp only [pathCompressRule, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact matches_uf_var_var_iff.mpr ⟨a, b, rfl, rfl, hab⟩
    · exact matches_uf_var_var_iff.mpr ⟨b, c, rfl, rfl, hbc⟩
    · exact matches_ne_var_var_iff.mpr ⟨b, c, rfl, rfl, not_cong_of_ne hd hne⟩

theorem collide_fire {d : Database} (hd : d.Diag) {a b c : Term} (hab : Edge d a b)
    (hac : Edge d a c) (hmin : b = Term.least b c) (hne : b ≠ c)
    (ha : a ∈ d.terms) (hb : b ∈ d.terms) (hc : c ∈ d.terms) :
    QueryMatches d ufCollideRule.query (ufEnv a b c) := by
  refine ⟨⟨?_, fun x hx => ?_⟩, fun p hp => ?_⟩
  · change (["@a", "@b", "@c"] : List Var).Perm (Query.vars ufCollideRule.query)
    decide
  · rw [hd.reps_eq_terms]
    rcases ufEnv_mem hx with h | h | h <;> rw [h] <;> assumption
  · rw [collide_query] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact matches_uf_var_var_iff.mpr ⟨a, b, rfl, rfl, hab⟩
    · exact matches_uf_var_var_iff.mpr ⟨a, c, rfl, rfl, hac⟩
    · exact (matches_eq_min_iff hd).mpr ⟨b, c, rfl, rfl, hb, hmin⟩
    · exact matches_ne_var_var_iff.mpr ⟨b, c, rfl, rfl, not_cong_of_ne hd hne⟩

/-! ### The congruence rule -/

/-- The variable names of one column group of the congruence rule. -/
def congNames (stem : String) (n : Nat) : List Var :=
  (List.range n).map fun i => "@" ++ stem ++ toString i

theorem congruenceVars_eq_map (stem : String) (n : Nat) :
    congruenceVars stem n = (congNames stem n).map Expr.var := by
  simp [congruenceVars, congNames]

theorem congNames_length (stem : String) (n : Nat) : (congNames stem n).length = n := by
  simp [congNames]

theorem congNames_getElem (stem : String) {n i : Nat} (hi : i < n) :
    (congNames stem n)[i]'(by rw [congNames_length]; exact hi) = "@" ++ stem ++ toString i := by
  simp [congNames]

theorem mem_congNames {stem : String} {n : Nat} {v : Var} :
    v ∈ congNames stem n ↔ ∃ i, i < n ∧ v = "@" ++ stem ++ toString i := by
  simp only [congNames, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem congName_toList (stem : String) (i : Nat) :
    ("@" ++ stem ++ toString i).toList = '@' :: (stem.toList ++ (toString i).toList) := by
  rw [String.toList_append, String.toList_append, show ("@").toList = ['@'] from by decide]
  rfl

theorem congName_inj {stem : String} {i j : Nat}
    (h : "@" ++ stem ++ toString i = "@" ++ stem ++ toString j) : i = j := by
  have h2 := congrArg String.toList h
  rw [congName_toList, congName_toList] at h2
  exact toString_nat_inj (String.toList_inj.mp (List.append_cancel_left (List.cons.inj h2).2))

theorem congNames_nodup (stem : String) (n : Nat) : (congNames stem n).Nodup := by
  refine (List.nodup_map_iff_inj_on List.nodup_range).mpr fun i _ j _ h => congName_inj h

/-- Column groups with different stems share no name. -/
theorem congName_ne_of_stem {s s' : String} {c c' : Char} (hs : s.toList = [c])
    (hs' : s'.toList = [c']) (hne : c ≠ c') (i j : Nat) :
    "@" ++ s ++ toString i ≠ "@" ++ s' ++ toString j := by
  intro h
  have h2 := congrArg String.toList h
  rw [congName_toList, congName_toList, hs, hs'] at h2
  exact hne (List.cons.inj (List.cons.inj h2).2).1

/-- A two-character generated name is in no column group. -/
theorem short_ne_congName {w : String} {c₂ : Char} (hw : w.toList = ['@', c₂]) {s : String}
    {c : Char} (hs : s.toList = [c]) (hne : c₂ ≠ c) (i : Nat) : w ≠ "@" ++ s ++ toString i := by
  intro h
  have h2 := congrArg String.toList h
  rw [congName_toList, hs, hw] at h2
  exact hne (List.cons.inj (List.cons.inj h2).2).1

theorem not_mem_congNames_of_stem {s s' : String} {c c' : Char} (hs : s.toList = [c])
    (hs' : s'.toList = [c']) (hne : c ≠ c') {n i : Nat} :
    "@" ++ s ++ toString i ∉ congNames s' n := by
  rw [mem_congNames]
  rintro ⟨j, _, hj⟩
  exact congName_ne_of_stem hs hs' hne i j hj

theorem short_not_mem_congNames {w : String} {c₂ : Char} (hw : w.toList = ['@', c₂]) {s : String}
    {c : Char} (hs : s.toList = [c]) (hne : c₂ ≠ c) {n : Nat} : w ∉ congNames s n := by
  rw [mem_congNames]
  rintro ⟨j, _, hj⟩
  exact short_ne_congName hw hs hne j hj

theorem toList_a : ("a" : String).toList = ['a'] := by decide
theorem toList_b : ("b" : String).toList = ['b'] := by decide
theorem toList_r : ("r" : String).toList = ['r'] := by decide
theorem toList_y : ("@y" : String).toList = ['@', 'y'] := by decide
theorem toList_z : ("@z" : String).toList = ['@', 'z'] := by decide

/-- The substitution of the congruence rule: the two rows' children, the parents, and the
two roots. -/
def congEnv (as bs rs : List Term) (y z : Term) (n : Nat) : Env :=
  (congNames "a" n).zip as ++ ((congNames "b" n).zip bs ++
    ((congNames "r" n).zip rs ++ [("@y", y), ("@z", z)]))

theorem lookup_zip_eq_none {vs : List Var} {ts : List Term} {v : Var} (hv : v ∉ vs) :
    Env.lookup v (vs.zip ts) = none :=
  Env.lookup_eq_none_iff.mpr fun h => hv (Env.dom_zip_subset vs ts h)

theorem lookup_zip_congNames {stem : String} {n : Nat} {ts : List Term} (hlen : ts.length = n)
    {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ stem ++ toString i) ((congNames stem n).zip ts) =
      some (ts[i]'(by rw [hlen]; exact hi)) := by
  have := Env.lookup_zip (congNames stem n) ts (by rw [congNames_length, hlen])
    (congNames_nodup stem n) i (by rw [congNames_length]; exact hi) (by rw [hlen]; exact hi)
  rwa [congNames_getElem stem hi] at this

section

variable {as bs rs : List Term} {y z : Term} {n : Nat}
  (hla : as.length = n) (hlb : bs.length = n) (hlr : rs.length = n)
include hla hlb hlr

omit hlb hlr in
theorem congEnv_lookup_a {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "a" ++ toString i) (congEnv as bs rs y z n) =
      some (as[i]'(by rw [hla]; exact hi)) :=
  Env.lookup_append_of_some (lookup_zip_congNames hla hi)

omit hla hlr in
theorem congEnv_lookup_b {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "b" ++ toString i) (congEnv as bs rs y z n) =
      some (bs[i]'(by rw [hlb]; exact hi)) := by
  unfold congEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_b toList_a (by decide)))]
  exact Env.lookup_append_of_some (lookup_zip_congNames hlb hi)

omit hla hlb in
theorem congEnv_lookup_r {i : Nat} (hi : i < n) :
    Env.lookup ("@" ++ "r" ++ toString i) (congEnv as bs rs y z n) =
      some (rs[i]'(by rw [hlr]; exact hi)) := by
  unfold congEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_r toList_a (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (not_mem_congNames_of_stem toList_r toList_b (by decide)))]
  exact Env.lookup_append_of_some (lookup_zip_congNames hlr hi)

omit hla hlb hlr in
theorem congEnv_lookup_y : Env.lookup "@y" (congEnv as bs rs y z n) = some y := by
  unfold congEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_y toList_a (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_y toList_b (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_y toList_r (by decide)))]
  rfl

omit hla hlb hlr in
theorem congEnv_lookup_z : Env.lookup "@z" (congEnv as bs rs y z n) = some z := by
  unfold congEnv
  rw [Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_z toList_a (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_z toList_b (by decide))),
    Env.lookup_append_of_none
    (lookup_zip_eq_none (short_not_mem_congNames toList_z toList_r (by decide)))]
  rfl

theorem congEnv_dom : Env.dom (congEnv as bs rs y z n) =
    congNames "a" n ++ (congNames "b" n ++ (congNames "r" n ++ ["@y", "@z"])) := by
  unfold congEnv Env.dom
  rw [List.map_append, List.map_append, List.map_append, List.map_fst_zip, List.map_fst_zip,
    List.map_fst_zip]
  · rfl
  all_goals rw [congNames_length]; omega

theorem congEnv_dom_nodup : (Env.dom (congEnv as bs rs y z n)).Nodup := by
  rw [congEnv_dom hla hlb hlr]
  have disj : ∀ {s s' : String} {c c' : Char}, s.toList = [c] → s'.toList = [c'] → c ≠ c' →
      List.Disjoint (congNames s n) (congNames s' n) := by
    intro s s' c c' hs hs' hne v hv hv'
    obtain ⟨i, _, rfl⟩ := mem_congNames.mp hv
    exact not_mem_congNames_of_stem hs hs' hne hv'
  have hyz : (["@y", "@z"] : List Var).Nodup := by decide
  refine List.Nodup.append (congNames_nodup _ _) (List.Nodup.append (congNames_nodup _ _)
    (List.Nodup.append (congNames_nodup _ _) hyz ?_) ?_) ?_
  · intro v hv hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl
    · exact short_not_mem_congNames toList_y toList_r (by decide) hv
    · exact short_not_mem_congNames toList_z toList_r (by decide) hv
  · intro v hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_b toList_r (by decide) hv hv'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
      rcases hv' with rfl | rfl
      · exact short_not_mem_congNames toList_y toList_b (by decide) hv
      · exact short_not_mem_congNames toList_z toList_b (by decide) hv
  · intro v hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_a toList_b (by decide) hv hv'
    rcases List.mem_append.mp hv' with hv' | hv'
    · exact disj toList_a toList_r (by decide) hv hv'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
      rcases hv' with rfl | rfl
      · exact short_not_mem_congNames toList_y toList_a (by decide) hv
      · exact short_not_mem_congNames toList_z toList_a (by decide) hv

omit hla hlb hlr in
theorem congEnv_mem_values {x : Var × Term} (hx : x ∈ congEnv as bs rs y z n) :
    x.2 ∈ as ∨ x.2 ∈ bs ∨ x.2 ∈ rs ∨ x.2 = y ∨ x.2 = z := by
  unfold congEnv at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx | rfl | rfl
  · exact Or.inl (List.of_mem_zip hx).2
  · exact Or.inr (Or.inl (List.of_mem_zip hx).2)
  · exact Or.inr (Or.inr (Or.inl (List.of_mem_zip hx).2))
  · simp
  · simp

end

/-- The variables of the congruence rule's query. -/
theorem mem_congruence_vars {f : FnName} {n : Nat} {v : Var} :
    v ∈ Query.vars (congruenceRule f n).query ↔
      v ∈ congNames "a" n ∨ v ∈ congNames "b" n ∨ v ∈ congNames "r" n ∨ v = "@y" ∨ v = "@z" := by
  have hvars : ∀ stem, v ∈ Expr.varsList (congruenceVars stem n) ↔ v ∈ congNames stem n := by
    intro stem
    rw [congruenceVars_eq_map]
    constructor
    · intro hv
      obtain ⟨e, he, hve⟩ := Expr.mem_varsList hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
      simp only [Expr.vars_var, List.mem_singleton] at hve
      exact hve ▸ hw
    · exact fun hv => Expr.var_mem_varsList (List.mem_map_of_mem hv)
  rw [Query.mem_vars]
  constructor
  · rintro ⟨p, hp, hv⟩
    rw [congruence_query] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap] at hp
    rcases hp with ((rfl | rfl) | ⟨abr, habr, hp⟩) | rfl | rfl | rfl | rfl
    · exact Or.inl ((hvars "a").mp hv)
    · exact Or.inr (Or.inl ((hvars "b").mp hv))
    · obtain ⟨hab, hr⟩ := List.of_mem_zip habr
      obtain ⟨ha, hb⟩ := List.of_mem_zip hab
      rw [congruenceVars_eq_map] at ha hb hr
      obtain ⟨wa, hwa, hwa'⟩ := List.mem_map.mp ha
      obtain ⟨wb, hwb, hwb'⟩ := List.mem_map.mp hb
      obtain ⟨wr, hwr, hwr'⟩ := List.mem_map.mp hr
      rcases hp with rfl | rfl
      · simp only [Pattern.vars, ufRow, Expr.vars, Expr.varsList, ← hwa', ← hwr',
          List.mem_union_iff, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact Or.inl hwa
        · exact Or.inr (Or.inr (Or.inl hwr))
      · simp only [Pattern.vars, ufRow, Expr.vars, Expr.varsList, ← hwb', ← hwr',
          List.mem_union_iff, List.mem_singleton, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact Or.inr (Or.inl hwb)
        · exact Or.inr (Or.inr (Or.inl hwr))
    · simp only [Pattern.vars, ufRow, Expr.vars, Expr.varsList, List.mem_union_iff,
        List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with hv | rfl
      · exact Or.inl ((hvars "a").mp hv)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · simp only [Pattern.vars, ufRow, Expr.vars, Expr.varsList, List.mem_union_iff,
        List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with hv | rfl
      · exact Or.inr (Or.inl ((hvars "b").mp hv))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · simp only [Pattern.vars, Expr.vars, List.mem_union_iff, List.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · simp only [Pattern.vars, Expr.vars, List.mem_union_iff, List.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · rintro (hv | hv | hv | rfl | rfl)
    · refine ⟨.expr (.app f (congruenceVars "a" n)), by rw [congruence_query]; simp, ?_⟩
      exact (hvars "a").mpr hv
    · refine ⟨.expr (.app f (congruenceVars "b" n)), by rw [congruence_query]; simp, ?_⟩
      exact (hvars "b").mpr hv
    · obtain ⟨i, hi, rfl⟩ := mem_congNames.mp hv
      refine ⟨_, (congruence_edge_atoms_mem (f := f) hi).1, ?_⟩
      simp [Pattern.vars, ufRow, Expr.vars, Expr.varsList]
    · refine ⟨.ne (.var "@y") (.var "@z"), by rw [congruence_query]; simp, ?_⟩
      simp [Pattern.vars, Expr.vars]
    · refine ⟨.ne (.var "@y") (.var "@z"), by rw [congruence_query]; simp, ?_⟩
      simp [Pattern.vars, Expr.vars]

/-- The congruence rule fires on two live applications with the same live child parents. -/
theorem congruence_fire {src d : Database} (h : Rel src d) {f : FnName} {as bs rs : List Term}
    {y z : Term} (hla : Term.app f as ∈ d.live) (hlb : Term.app f bs ∈ d.live)
    (hra : List.Forall₂ (Edge d) as rs) (hrb : List.Forall₂ (Edge d) bs rs)
    (hey : Edge d (.app f as) y) (hez : Edge d (.app f bs) z) (hmin : y = Term.least y z)
    (hne : y ≠ z) :
    QueryMatches d (congruenceRule f as.length).query (congEnv as bs rs y z as.length) := by
  set n := as.length with hn
  have hlen_a : as.length = n := rfl
  have hlen_r : rs.length = n := hra.length_eq.symm
  have hlen_b : bs.length = n := hrb.length_eq.trans hlen_r
  have hterms : ∀ x ∈ congEnv as bs rs y z n, x.2 ∈ d.terms := by
    intro x hx
    rcases congEnv_mem_values hx with hx | hx | hx | hx | hx
    · obtain ⟨r, _, he⟩ := hra.flip.exists_left hx
      exact Keys.subset_terms d (h.key_of_edge he)
    · obtain ⟨r, _, he⟩ := hrb.flip.exists_left hx
      exact Keys.subset_terms d (h.key_of_edge he)
    · obtain ⟨a, _, he⟩ := hra.exists_left hx
      exact Keys.subset_terms d (h.parent_of_edge he)
    · rw [hx]; exact Keys.subset_terms d (h.parent_of_edge hey)
    · rw [hx]; exact Keys.subset_terms d (h.parent_of_edge hez)
  have hsome : ∀ stem (ts : List Term) (hlen : ts.length = n),
      (∀ i (hi : i < n), Env.lookup ("@" ++ stem ++ toString i) (congEnv as bs rs y z n) =
        some (ts[i]'(by rw [hlen]; exact hi))) →
      Expr.evalList (congruenceVars stem n) (congEnv as bs rs y z n) = some ts := by
    intro stem ts hlen hlook
    rw [congruenceVars_eq_map]
    apply Expr.evalList_map_var _ _ _ (by rw [congNames_length, hlen])
    intro i hi hi'
    rw [congNames_length] at hi
    rw [congNames_getElem stem hi]
    exact hlook i hi
  have evalA := hsome "a" as hlen_a fun i hi => congEnv_lookup_a hlen_a hi
  have evalB := hsome "b" bs hlen_b fun i hi => congEnv_lookup_b hlen_b hi
  have evalR := hsome "r" rs hlen_r fun i hi => congEnv_lookup_r hlen_r hi
  have matchesVars : ∀ stem (ts : List Term),
      Expr.evalList (congruenceVars stem n) (congEnv as bs rs y z n) = some ts →
      Expr.MatchesList d (congEnv as bs rs y z n) (congruenceVars stem n) := by
    intro stem ts hts
    rw [congruenceVars_eq_map]
    apply matchesList_map_var
    intro v hv
    rw [congruenceVars_eq_map] at hts
    exact Expr.lookup_isSome_of_mem_evalList hts (List.mem_map_of_mem hv)
  refine ⟨⟨?_, fun x hx => mem_reps_of_diag h.diag (hterms x hx)⟩, fun p hp => ?_⟩
  · rw [List.perm_ext_iff_of_nodup (congEnv_dom_nodup hlen_a hlen_b hlen_r) (Query.vars_nodup _)]
    intro v
    rw [congEnv_dom hlen_a hlen_b hlen_r, mem_congruence_vars]
    simp
  · rw [congruence_query] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap] at hp
    rcases hp with ((rfl | rfl) | ⟨abr, habr, hp⟩) | rfl | rfl | rfl | rfl
    · exact matches_app_iff.mpr ⟨as, matchesVars "a" as evalA, evalA, hla⟩
    · exact matches_app_iff.mpr ⟨bs, matchesVars "b" bs evalB, evalB, hlb⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp habr
      simp only [List.length_zip, congruenceVars_length, Nat.min_self] at hi
      rw [List.getElem_zip, List.getElem_zip, congruenceVars_getElem "a" hi,
        congruenceVars_getElem "b" hi, congruenceVars_getElem "r" hi] at hp
      have hedge_a : Edge d (as[i]'(by rw [hlen_a]; exact hi)) (rs[i]'(by rw [hlen_r]; exact hi)) :=
        (List.forall₂_iff_get.mp hra).2 i _ _
      have hedge_b : Edge d (bs[i]'(by rw [hlen_b]; exact hi)) (rs[i]'(by rw [hlen_r]; exact hi)) :=
        (List.forall₂_iff_get.mp hrb).2 i _ _
      simp only at hp
      rcases hp with rfl | rfl
      · exact matches_uf_var_var_iff.mpr ⟨_, _, congEnv_lookup_a hlen_a hi,
          congEnv_lookup_r hlen_r hi, hedge_a⟩
      · exact matches_uf_var_var_iff.mpr ⟨_, _, congEnv_lookup_b hlen_b hi,
          congEnv_lookup_r hlen_r hi, hedge_b⟩
    · refine matches_uf_iff.mpr ⟨.app f as, y, .app (matchesVars "a" as evalA) evalA hla,
        .var congEnv_lookup_y, ?_, congEnv_lookup_y, hey⟩
      rw [Expr.eval_app_ctor, evalA]; rfl
    · refine matches_uf_iff.mpr ⟨.app f bs, z, .app (matchesVars "b" bs evalB) evalB hlb,
        .var congEnv_lookup_z, ?_, congEnv_lookup_z, hez⟩
      rw [Expr.eval_app_ctor, evalB]; rfl
    · exact (matches_eq_min_iff h.diag).mpr ⟨y, z, congEnv_lookup_y, congEnv_lookup_z,
        Keys.subset_terms d (h.parent_of_edge hey), hmin⟩
    · exact matches_ne_var_var_iff.mpr ⟨y, z, congEnv_lookup_y, congEnv_lookup_z,
        not_cong_of_ne h.diag hne⟩

end Egglog.Congruence
