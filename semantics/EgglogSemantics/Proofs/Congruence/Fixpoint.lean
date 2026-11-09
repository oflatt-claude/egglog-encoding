import EgglogSemantics.Proofs.Congruence.Maintenance
import EgglogSemantics.Proofs.Congruence.Firing
import EgglogSemantics.Proofs.FiniteSaturation
import EgglogSemantics.Proofs.DiagonalRound
import Mathlib.Data.Set.Card

/-! The rebuild saturation: it terminates, because rows and marks only grow inside the
finite square of the keys, and its fixpoint is canonical, because any maintenance firing
would mark a live row or add a row. -/

namespace Egglog.Congruence

variable {P : Program} {src d : Database}

/-- A row marked by some firing of the round is not live afterwards. -/
theorem not_live_of_runMarks (h : Rel src d) {t : Term}
    (ht : t ∈ RunMarks (maintenance P) d) : t ∉ (RunRules (maintenance P) d).live := by
  intro hl
  have h' := maint_round (P := P) h
  obtain ⟨k, p, q, rfl, _⟩ := mem_runMarks_maint h ht
  have he : Edge (RunRules (maintenance P) d) k p := hl
  exact (h'.edge_iff.mp he).2 (by rw [RunRules.eq_pair]; exact Or.inr ht)

/-- The write set of a firing is among the round's writes. -/
theorem writes_subset_runWrites {R : List Rule} {d : Database} {r : Rule} (hr : r ∈ R) {σ : Env}
    (hσ : QueryMatches d r.query σ) {W : Set (Term × Term)}
    (hW : Action.writes σ r.actions = some W) : W ⊆ RunWrites R d :=
  fun _ hq => Set.mem_sUnion.mpr ⟨W, ⟨r, hr, σ, hσ, hW⟩, hq⟩

theorem marks_subset_runMarks {R : List Rule} {d : Database} {r : Rule} (hr : r ∈ R) {σ : Env}
    (hσ : QueryMatches d r.query σ) {X : Set Term}
    (hX : Action.marks σ r.actions = some X) : X ⊆ RunMarks R d :=
  fun _ ht => Set.mem_sUnion.mpr ⟨X, ⟨r, hr, σ, hσ, hX⟩, ht⟩

theorem least_swap {p q : Term} (hl : Term.least p q = q) (hne : p ≠ q) : q = Term.least q p := by
  rw [Term.least_eq_ite] at hl ⊢
  have hnpq : ¬ Term.blt p q = true := by
    intro hpq
    rw [if_pos hpq] at hl
    exact hne hl
  rcases Term.blt_total p q hne with hpq | hqp
  · exact (hnpq hpq).elim
  · rw [if_pos hqp]

/-- A meaning-preserving maintenance round means no maintenance rule fires: the state is
canonical. -/
theorem canon_of_fixpoint (h : Rel src d) (hcs : src.CtorsIn P)
    (hfix : d.SameMeaning (RunRules (maintenance P) d)) : Canon d := by
  have h' := maint_round (P := P) h
  have hterms_eq := hfix.terms_eq_of_diag h.diag h'.diag
  -- Two live edges of one key collide.
  have unique : ∀ k p q, Edge d k p → Edge d k q → p = q := by
    intro k p q hp hq
    by_contra hne
    have main : ∀ p q, Edge d k p → Edge d k q → p = Term.least p q → p ≠ q → False := by
      intro p q hp hq hmin hne
      have hfire := collide_fire h.diag hp hq hmin hne (Keys.subset_terms d (h.key_of_edge hp))
        (Keys.subset_terms d (h.parent_of_edge hp)) (Keys.subset_terms d (h.parent_of_edge hq))
      have hmark : ufRowT k q ∈ RunMarks (maintenance P) d :=
        marks_subset_runMarks (mem_maintenance.mpr (Or.inr (Or.inl rfl))) hfire
          (collide_marks (ufEnv_lookup_a k p q) (ufEnv_lookup_b k p q) (ufEnv_lookup_c k p q))
          (by simp)
      exact not_live_of_runMarks h hmark ((hfix.live _).mp hq)
    rcases Term.least_eq_or p q with hl | hl
    · exact main p q hp hq hl.symm hne
    · exact main q p hq hp (least_swap hl hne) (Ne.symm hne)
  -- A live parent is a root.
  have root : ∀ k p, Edge d k p → Edge d p p := by
    intro k p hkp
    obtain ⟨m, hpm, _⟩ := h.least_parent (h.parent_of_edge hkp)
    by_cases hmp : p = m
    · exact hmp ▸ hpm
    · exfalso
      have hfire := compress_fire h.diag hkp hpm hmp (Keys.subset_terms d (h.key_of_edge hkp))
        (Keys.subset_terms d (h.parent_of_edge hkp)) (Keys.subset_terms d (h.parent_of_edge hpm))
      have hmark : ufRowT k p ∈ RunMarks (maintenance P) d :=
        marks_subset_runMarks (mem_maintenance.mpr (Or.inl rfl)) hfire
          (compress_marks (ufEnv_lookup_a k p m) (ufEnv_lookup_b k p m)
            (by rw [ufEnv_lookup_c]; rfl)) (by simp)
      exact not_live_of_runMarks h hmark ((hfix.live _).mp hkp)
  refine ⟨unique, root, ?_⟩
  intro f as bs rs y z hla hlb hra hrb hey hez
  by_contra hne
  have main : ∀ (as bs : List Term) (y z : Term), Term.app f as ∈ d.live →
      Term.app f bs ∈ d.live → List.Forall₂ (Edge d) as rs → List.Forall₂ (Edge d) bs rs →
      Edge d (.app f as) y → Edge d (.app f bs) z → y = Term.least y z → y ≠ z → False := by
    intro as bs y z hla hlb hra hrb hey hez hmin hne
    by_cases hn : as.length = 0
    · have has : as = [] := List.length_eq_zero_iff.mp hn
      have hbs : bs = [] :=
        List.length_eq_zero_iff.mp (hrb.length_eq.trans (hra.length_eq.symm.trans hn))
      subst has hbs
      exact hne (unique _ _ _ hey hez)
    · have hctor : (f, as.length) ∈ P.ctors :=
        hcs f as (h.key_mem_src (h.key_of_edge hey))
      have hrule : congruenceRule f as.length ∈ maintenance P :=
        mem_maintenance.mpr (Or.inr (Or.inr ⟨(f, as.length), hctor, hn, rfl⟩))
      have hfire := congruence_fire h hla hlb hra hrb hey hez hmin hne
      have hwrite : (ufRowT z y, ufRowT z y) ∈ RunWrites (maintenance P) d :=
        writes_subset_runWrites hrule hfire
          (congruence_writes (f := f) (n := as.length) congEnv_lookup_y congEnv_lookup_z) (by simp)
      have hmem : ufRowT z y ∈ (RunRules (maintenance P) d).terms := by
        refine ⟨(ufRowT z y, ufRowT z y), ?_, Or.inl (Term.self_mem_subterms _)⟩
        rw [RunRules.eq_pair]
        exact Or.inr hwrite
      rw [← hterms_eq, uf_mem_terms_iff h.ufOnly h.endsFree] at hmem
      obtain ⟨m, hzm, hleast⟩ := h.least_parent (h.parent_of_edge hez)
      have hmz : m = z := unique z m z hzm (root _ _ hez)
      subst hmz
      have hyz : Term.blt y m = true := by
        rw [Term.least_eq_ite] at hmin
        by_contra hlt
        rw [if_neg hlt] at hmin
        exact hne hmin
      rcases hleast y hmem with heq | hlt
      · exact hne heq.symm
      · rw [Term.blt_asymm _ _ hlt] at hyz
        exact Bool.false_ne_true hyz
  rcases Term.least_eq_or y z with hl | hl
  · exact main as bs y z hla hlb hra hrb hey hez hl.symm hne
  · exact main bs as z y hlb hla hrb hra hez hey (least_swap hl hne) (Ne.symm hne)

/-- At a meaning-preserving round the next round changes nothing at all. -/
theorem fixpoint_stable (h : Rel src d)
    (hfix : d.SameMeaning (RunRules (maintenance P) d)) :
    RunRules (maintenance P) (RunRules (maintenance P) d) = RunRules (maintenance P) d := by
  have h' := maint_round (P := P) h
  have hterms := hfix.terms_eq_of_diag h.diag h'.diag
  have hw := RunWrites.eq_of_sameMeaning_terms hfix hterms (maintenance P)
  have hm := RunMarks.eq_of_sameMeaning_terms hfix hterms (maintenance P)
  conv_lhs => rw [RunRules.eq_pair]
  rw [← hw, ← hm]
  apply Database.ext
  · change (RunRules (maintenance P) d).eqs ∪ _ = (RunRules (maintenance P) d).eqs
    rw [RunRules.eq_pair]
    exact Set.union_eq_left.mpr Set.subset_union_right
  · change (RunRules (maintenance P) d).subsumed ∪ _ = (RunRules (maintenance P) d).subsumed
    rw [RunRules.eq_pair]
    exact Set.union_eq_left.mpr Set.subset_union_right

/-! ### Termination -/

/-- Rows only grow along a schedule. -/
theorem Reach.contained {S : Schedule} {d e : Database} (h : Reach d S e) : d.Contained e := by
  induction h with
  | run => rw [RunRules.eq_pair]; exact ⟨Set.subset_union_left, Set.subset_union_left⟩
  | seq _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | fixpoint _ _ ih => exact ih
  | again _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The rows of a state: the terms asserted reflexively. -/
def rowsOf (e : Database) : Set Term := {t | (t, t) ∈ e.eqs}

theorem rowsOf_mono {d e : Database} (h : d.eqs ⊆ e.eqs) : rowsOf d ⊆ rowsOf e :=
  fun _ ht => h ht

/-- On union-find states the rows determine the equations. -/
theorem eqs_eq_of_rowsOf_eq {d e : Database} (hd : UfOnly d) (he : UfOnly e)
    (h : rowsOf d = rowsOf e) : d.eqs = e.eqs := by
  ext q
  constructor
  · intro hq
    obtain ⟨k, p, rfl⟩ := hd q hq
    exact (show ufRowT k p ∈ rowsOf e from h ▸ hq)
  · intro hq
    obtain ⟨k, p, rfl⟩ := he q hq
    exact (show ufRowT k p ∈ rowsOf d from h ▸ hq)

/-- Along maintenance rounds the relation and the keys are kept. -/
theorem rel_of_rounds (h : Rel src d) {e : Database}
    (he : Relation.ReflTransGen (fun a b => b = RunRules (maintenance P) a) d e) :
    Rel src e ∧ Keys e = Keys d := by
  induction he with
  | refl => exact ⟨h, rfl⟩
  | tail _ hbc ih =>
    subst hbc
    exact ⟨maint_round ih.1, (maint_keys ih.1).trans ih.2⟩

/-- The rebuild saturation reaches a state. -/
theorem rebuild_exists (h : Rel src d) : ∃ e, Reach d (.saturate (.run (maintenance P))) e := by
  classical
  let RU : Set Term := Set.image2 ufRowT (Keys d) (Keys d)
  have hRU : RU.Finite := h.keys_finite.image2 ufRowT h.keys_finite
  let rank : Database → Nat := fun e => (RU \ rowsOf e).ncard + (RU \ e.subsumed).ncard
  apply saturateReach_exists_of_measure (maintenance P) d rank
  intro e he hne
  obtain ⟨hre, hkeys⟩ := rel_of_rounds h he
  have hre' := maint_round (P := P) hre
  have hkeys' : Keys (RunRules (maintenance P) e) = Keys d := (maint_keys hre).trans hkeys
  set e' := RunRules (maintenance P) e with he'
  have hrows : rowsOf e' ⊆ RU := by
    intro t ht
    obtain ⟨k, p, heq⟩ := hre'.ufOnly _ ht
    obtain rfl : t = ufRowT k p := (Prod.mk.inj heq).1
    have hr : Row e' k p := ht
    exact ⟨k, hkeys' ▸ hr.mem_keys, p, hkeys' ▸ hre'.parent_mem_keys hr, rfl⟩
  have hmarks : e'.subsumed ⊆ RU := by
    intro t ht
    obtain ⟨k, p, q, rfl, hr, _⟩ := hre'.marks t ht
    exact ⟨k, hkeys' ▸ hr.mem_keys, p, hkeys' ▸ hre'.parent_mem_keys hr, rfl⟩
  have heqs : e.eqs ⊆ e'.eqs := maint_eqs_mono e
  have hsub : e.subsumed ⊆ e'.subsumed := maint_subsumed_mono e
  have hdiff : e.eqs ≠ e'.eqs ∨ e.subsumed ≠ e'.subsumed := by
    by_contra hc
    push Not at hc
    have : e = e' := Database.ext hc.1 hc.2
    exact hne (this ▸ Database.SameMeaning.refl e)
  have hle₁ : (RU \ rowsOf e').ncard ≤ (RU \ rowsOf e).ncard :=
    Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right (rowsOf_mono heqs)) hRU.sdiff
  have hle₂ : (RU \ e'.subsumed).ncard ≤ (RU \ e.subsumed).ncard :=
    Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right hsub) hRU.sdiff
  rcases hdiff with hdiff | hdiff
  · have hss : RU \ rowsOf e' ⊂ RU \ rowsOf e := by
      refine LE.le.ssubset_of_ne (Set.sdiff_subset_sdiff_right (rowsOf_mono heqs)) ?_
      intro heq
      apply hdiff
      apply eqs_eq_of_rowsOf_eq hre.ufOnly hre'.ufOnly
      apply Set.Subset.antisymm (rowsOf_mono heqs)
      intro t ht
      by_contra hnt
      have h₁ : t ∈ RU \ rowsOf e := ⟨hrows ht, hnt⟩
      rw [← heq] at h₁
      exact h₁.2 ht
    have := Set.ncard_lt_ncard hss hRU.sdiff
    change (RU \ rowsOf e').ncard + (RU \ e'.subsumed).ncard <
      (RU \ rowsOf e).ncard + (RU \ e.subsumed).ncard
    omega
  · have hss : RU \ e'.subsumed ⊂ RU \ e.subsumed := by
      refine LE.le.ssubset_of_ne (Set.sdiff_subset_sdiff_right hsub) ?_
      intro heq
      apply hdiff
      apply Set.Subset.antisymm hsub
      intro t ht
      by_contra hnt
      have h₁ : t ∈ RU \ e.subsumed := ⟨hmarks ht, hnt⟩
      rw [← heq] at h₁
      exact h₁.2 ht
    have := Set.ncard_lt_ncard hss hRU.sdiff
    change (RU \ rowsOf e').ncard + (RU \ e'.subsumed).ncard <
      (RU \ rowsOf e).ncard + (RU \ e.subsumed).ncard
    omega

/-- The measure of a union-find state inside a finite universe of keys: the rows not yet
asserted and the rows not yet marked. -/
noncomputable def rank (U : Set Term) (e : Database) : Nat :=
  (Set.image2 ufRowT U U \ rowsOf e).ncard + (Set.image2 ufRowT U U \ e.subsumed).ncard

/-- A meaning-changing step of a union-find state inside the universe lowers the rank. -/
theorem rank_lt {U : Set Term} (hU : U.Finite) {d d' : Database} (hud : UfOnly d)
    (hud' : UfOnly d') (hkeys : ∀ k p, Row d' k p → k ∈ U ∧ p ∈ U)
    (hmarks : ∀ t ∈ d'.subsumed, ∃ k p, t = ufRowT k p ∧ Row d' k p)
    (heqs : d.eqs ⊆ d'.eqs) (hsub : d.subsumed ⊆ d'.subsumed) (hne : ¬ d.SameMeaning d') :
    rank U d' < rank U d := by
  classical
  have hRU : (Set.image2 ufRowT U U).Finite := hU.image2 ufRowT hU
  have hrows : rowsOf d' ⊆ Set.image2 ufRowT U U := by
    intro t ht
    obtain ⟨k, p, heq⟩ := hud' _ ht
    obtain rfl : t = ufRowT k p := (Prod.mk.inj heq).1
    have hr : Row d' k p := ht
    exact ⟨k, (hkeys k p hr).1, p, (hkeys k p hr).2, rfl⟩
  have hmarks' : d'.subsumed ⊆ Set.image2 ufRowT U U := by
    intro t ht
    obtain ⟨k, p, rfl, hr⟩ := hmarks t ht
    exact ⟨k, (hkeys k p hr).1, p, (hkeys k p hr).2, rfl⟩
  have hdiff : d.eqs ≠ d'.eqs ∨ d.subsumed ≠ d'.subsumed := by
    by_contra hc
    push Not at hc
    have : d = d' := Database.ext hc.1 hc.2
    exact hne (this ▸ Database.SameMeaning.refl d)
  have hle₁ : (Set.image2 ufRowT U U \ rowsOf d').ncard ≤
      (Set.image2 ufRowT U U \ rowsOf d).ncard :=
    Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right (rowsOf_mono heqs)) hRU.sdiff
  have hle₂ : (Set.image2 ufRowT U U \ d'.subsumed).ncard ≤
      (Set.image2 ufRowT U U \ d.subsumed).ncard :=
    Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right hsub) hRU.sdiff
  unfold rank
  rcases hdiff with hdiff | hdiff
  · have hss : Set.image2 ufRowT U U \ rowsOf d' ⊂ Set.image2 ufRowT U U \ rowsOf d := by
      refine LE.le.ssubset_of_ne (Set.sdiff_subset_sdiff_right (rowsOf_mono heqs)) ?_
      intro heq
      apply hdiff
      apply eqs_eq_of_rowsOf_eq hud hud'
      apply Set.Subset.antisymm (rowsOf_mono heqs)
      intro t ht
      by_contra hnt
      have h₁ : t ∈ Set.image2 ufRowT U U \ rowsOf d := ⟨hrows ht, hnt⟩
      rw [← heq] at h₁
      exact h₁.2 ht
    have := Set.ncard_lt_ncard hss hRU.sdiff
    omega
  · have hss : Set.image2 ufRowT U U \ d'.subsumed ⊂ Set.image2 ufRowT U U \ d.subsumed := by
      refine LE.le.ssubset_of_ne (Set.sdiff_subset_sdiff_right hsub) ?_
      intro heq
      apply hdiff
      apply Set.Subset.antisymm hsub
      intro t ht
      by_contra hnt
      have h₁ : t ∈ Set.image2 ufRowT U U \ d.subsumed := ⟨hmarks' ht, hnt⟩
      rw [← heq] at h₁
      exact h₁.2 ht
    have := Set.ncard_lt_ncard hss hRU.sdiff
    omega

/-- The result of the rebuild saturation is related, canonical, and has the same keys. -/
theorem rebuild_rel (h : Rel src d) (hcs : src.CtorsIn P) {e : Database}
    (hr : Reach d (.saturate (.run (maintenance P))) e) :
    Rel src e ∧ Canon e ∧ Keys e = Keys d := by
  generalize hS : Schedule.saturate (.run (maintenance P)) = S at hr
  induction hr with
  | run => cases hS
  | seq => cases hS
  | @fixpoint d e S hp heq _ =>
    cases hS
    cases hp
    have he := maint_round (P := P) h
    refine ⟨he, ?_, maint_keys h⟩
    apply canon_of_fixpoint he hcs
    rw [fixpoint_stable h heq]
    exact Database.SameMeaning.refl _
  | @again d e _ S hp _ _ _ ih =>
    cases hS
    cases hp
    obtain ⟨h₁, h₂, h₃⟩ := ih (maint_round h) rfl
    exact ⟨h₁, h₂, h₃.trans (maint_keys h)⟩

end Egglog.Congruence
