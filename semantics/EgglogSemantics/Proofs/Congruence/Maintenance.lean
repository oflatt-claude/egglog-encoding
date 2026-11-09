import EgglogSemantics.Proofs.Congruence.Invariant
import EgglogSemantics.Proofs.Congruence.Rules

/-! One round of the maintenance rules preserves the simulation relation: every row it
writes is derivable from the rows it read, every row it marks has a strictly smaller
replacement, and the live rows still generate every row. -/

namespace Egglog.Congruence

/-- A row one maintenance firing asserts: an existing row, or the replacement a rule writes
for the live edges it matched. -/
inductive MaintRow (d : Database) : Term → Term → Prop
  | old {k p : Term} : Row d k p → MaintRow d k p
  | compress {a b c : Term} : Edge d a b → Edge d b c → b ≠ c → MaintRow d a c
  | collide {a b c : Term} : Edge d a b → Edge d a c → b = Term.least b c → b ≠ c →
      MaintRow d c b
  | congr {f : FnName} {as bs rs : List Term} {y z : Term} :
      Term.app f as ∈ d.live → Term.app f bs ∈ d.live →
      List.Forall₂ (Edge d) as rs → List.Forall₂ (Edge d) bs rs →
      Edge d (.app f as) y → Edge d (.app f bs) z → y = Term.least y z → y ≠ z → MaintRow d z y

variable {P : Program} {src d : Database}

theorem mem_runWrites_maint (h : Rel src d) {q : Term × Term}
    (hq : q ∈ RunWrites (maintenance P) d) :
    ∃ k p, q = (ufRowT k p, ufRowT k p) ∧ MaintRow d k p := by
  obtain ⟨W, ⟨r, hr, σ, hσ, hW⟩, hqW⟩ := Set.mem_sUnion.mp hq
  rcases mem_maintenance.mp hr with rfl | rfl | ⟨fk, _, _, rfl⟩
  · obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hnc⟩ := compress_inv hσ
    rw [compress_writes ha hb hc] at hW
    obtain rfl := Option.some.inj hW
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hqW
    rcases hqW with rfl | rfl
    · exact ⟨a, b, rfl, .old (h.row_of_edge hab)⟩
    · exact ⟨a, c, rfl, .compress hab hbc
        (ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hab)) hnc)⟩
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hmin, hnc⟩ := collide_inv h.diag hσ
    rw [collide_writes ha hb hc] at hW
    obtain rfl := Option.some.inj hW
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hqW
    rcases hqW with rfl | rfl
    · exact ⟨a, c, rfl, .old (h.row_of_edge hac)⟩
    · exact ⟨c, b, rfl, .collide hab hac hmin
        (ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hab)) hnc)⟩
  · obtain ⟨as, bs, rs, y, z, _, _, _, hy, hz, hla, hlb, hra, hrb, hey, hez, hmin, hnc⟩ :=
      congruence_inv h.diag hσ
    rw [congruence_writes hy hz] at hW
    obtain rfl := Option.some.inj hW
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hqW
    subst hqW
    exact ⟨z, y, rfl, .congr hla hlb hra hrb hey hez hmin
      (ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hey)) hnc)⟩

theorem mem_runMarks_maint (h : Rel src d) {t : Term} (ht : t ∈ RunMarks (maintenance P) d) :
    ∃ k p q, t = ufRowT k p ∧ Edge d k p ∧ Term.blt q p = true ∧
      Row (RunRules (maintenance P) d) k q ∧ Row (RunRules (maintenance P) d) p q := by
  have heqs : (RunRules (maintenance P) d).eqs = d.eqs ∪ RunWrites (maintenance P) d := by
    rw [RunRules.eq_pair]
  obtain ⟨X, ⟨r, hr, σ, hσ, hX⟩, htX⟩ := Set.mem_sUnion.mp ht
  have hwrite : ∀ W, Action.writes σ r.actions = some W → W ⊆ RunWrites (maintenance P) d :=
    fun W hW q hq => Set.mem_sUnion.mpr ⟨W, ⟨r, hr, σ, hσ, hW⟩, hq⟩
  rcases mem_maintenance.mp hr with rfl | rfl | ⟨fk, _, _, rfl⟩
  · obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hnc⟩ := compress_inv hσ
    rw [compress_marks ha hb (by rw [hc]; rfl)] at hX
    obtain rfl := Option.some.inj hX
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at htX
    subst htX
    have hne : b ≠ c := ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hab)) hnc
    refine ⟨a, b, c, rfl, hab, ?_, ?_, ?_⟩
    · rcases h.edge_down hbc with heq | hlt
      · exact (hne heq.symm).elim
      · exact hlt
    · change (ufRowT a c, ufRowT a c) ∈ (RunRules (maintenance P) d).eqs
      rw [heqs]
      exact Or.inr (hwrite _ (compress_writes ha hb hc) (by simp))
    · exact (h.row_of_edge hbc).mono (heqs ▸ Set.subset_union_left)
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hmin, hnc⟩ := collide_inv h.diag hσ
    rw [collide_marks ha hb hc] at hX
    obtain rfl := Option.some.inj hX
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at htX
    subst htX
    have hne : b ≠ c := ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hab)) hnc
    refine ⟨a, c, b, rfl, hac, ?_, ?_, ?_⟩
    · rw [Term.least_eq_ite] at hmin
      by_contra hlt
      rw [if_neg hlt] at hmin
      exact hne hmin
    · exact (h.row_of_edge hab).mono (heqs ▸ Set.subset_union_left)
    · change (ufRowT c b, ufRowT c b) ∈ (RunRules (maintenance P) d).eqs
      rw [heqs]
      exact Or.inr (hwrite _ (collide_writes ha hb hc) (by simp))
  · obtain ⟨as, bs, rs, y, z, _, _, _, hy, hz, -⟩ := congruence_inv h.diag hσ
    rw [congruence_marks hy hz] at hX
    obtain rfl := Option.some.inj hX
    simp at htX

namespace MaintRow

variable (h : Rel src d)
include h

theorem key_mem {k p : Term} (hm : MaintRow d k p) : k ∈ Keys d := by
  cases hm with
  | old hr => exact hr.mem_keys
  | compress hab _ _ => exact h.key_of_edge hab
  | collide _ hac _ _ => exact h.parent_of_edge hac
  | congr _ _ _ _ _ hez _ _ => exact h.parent_of_edge hez

theorem parent_mem {k p : Term} (hm : MaintRow d k p) : p ∈ Keys d := by
  cases hm with
  | old hr => exact h.parent_mem_keys hr
  | compress _ hbc _ => exact h.parent_of_edge hbc
  | collide hab _ _ _ => exact h.parent_of_edge hab
  | congr _ _ _ _ hey _ _ _ => exact h.parent_of_edge hey

theorem down {k p : Term} (hm : MaintRow d k p) : p = k ∨ Term.blt p k = true := by
  cases hm with
  | old hr => exact h.down _ _ hr
  | @compress _ b _ hab hbc hne =>
    have hcb : Term.blt p b = true := by
      rcases h.edge_down hbc with heq | hlt
      · exact (hne heq.symm).elim
      · exact hlt
    rcases h.edge_down hab with rfl | hba
    · exact Or.inr hcb
    · exact Or.inr (Term.blt_trans _ _ _ hcb hba)
  | collide _ _ hmin hne =>
    right
    rw [Term.least_eq_ite] at hmin
    by_contra hlt
    rw [if_neg hlt] at hmin
    exact hne hmin
  | congr _ _ _ _ _ _ hmin hne =>
    right
    rw [Term.least_eq_ite] at hmin
    by_contra hlt
    rw [if_neg hlt] at hmin
    exact hne hmin

/-- Every row a maintenance firing asserts is already derivable from the rows. -/
theorem cong_view {k p : Term} (hm : MaintRow d k p) : Cong (view d) k p := by
  cases hm with
  | old hr => exact hr.cong_view
  | compress hab hbc _ =>
    exact (h.row_of_edge hab).cong_view.trans (h.row_of_edge hbc).cong_view
  | collide hab hac _ _ =>
    exact (h.row_of_edge hac).cong_view.symm.trans (h.row_of_edge hab).cong_view
  | @congr f as bs rs _ _ _ _ hra hrb hey hez _ _ =>
    have hself : Cong (view d) (.app f as) (.app f as) :=
      (h.selfLoop _ _ (h.row_of_edge hey)).1.cong_view
    have hargs : CongList (view d) as bs := by
      rw [CongList.forall₂]
      have h₁ : List.Forall₂ (fun a r => Cong (view d) a r) as rs :=
        hra.imp fun _ _ he => (h.row_of_edge he).cong_view
      have h₂ : List.Forall₂ (fun b r => Cong (view d) b r) bs rs :=
        hrb.imp fun _ _ he => (h.row_of_edge he).cong_view
      rw [List.forall₂_iff_get] at h₁ h₂ ⊢
      refine ⟨h₁.1.trans h₂.1.symm, fun i h₁' h₂' => ?_⟩
      exact (h₁.2 i h₁' (h₁.1 ▸ h₁')).trans (h₂.2 i h₂' (h₂.1 ▸ h₂')).symm
    have hab : Cong (view d) (.app f as) (.app f bs) := .congr hself hargs
    exact ((h.row_of_edge hez).cong_view.symm.trans hab.symm).trans
      (h.row_of_edge hey).cong_view

end MaintRow

/-- One maintenance round preserves the simulation relation. -/
theorem maint_round (h : Rel src d) : Rel src (RunRules (maintenance P) d) := by
  set d' := RunRules (maintenance P) d with hd'
  have heqs : d'.eqs = d.eqs ∪ RunWrites (maintenance P) d := by rw [hd', RunRules.eq_pair]
  have hsub : d'.subsumed = d.subsumed ∪ RunMarks (maintenance P) d := by
    rw [hd', RunRules.eq_pair]
  have hmono : d.eqs ⊆ d'.eqs := heqs ▸ Set.subset_union_left
  have hrow : ∀ k p, Row d' k p → MaintRow d k p := by
    intro k p hr
    have hr' : (ufRowT k p, ufRowT k p) ∈ d.eqs ∪ RunWrites (maintenance P) d := heqs ▸ hr
    rcases hr' with hr' | hr'
    · exact .old hr'
    · obtain ⟨k', p', heq, hm⟩ := mem_runWrites_maint h hr'
      obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
      exact hm
  have hufOnly : UfOnly d' := by
    intro q hq
    have hq' : q ∈ d.eqs ∪ RunWrites (maintenance P) d := heqs ▸ hq
    rcases hq' with hq' | hq'
    · exact h.ufOnly q hq'
    · obtain ⟨k, p, heq, _⟩ := mem_runWrites_maint h hq'
      exact ⟨k, p, heq⟩
  have hdiag : d'.Diag := by
    intro q hq
    obtain ⟨k, p, rfl⟩ := hufOnly q hq
    rfl
  have hkeys : Keys d' = Keys d := by
    apply Set.Subset.antisymm
    · rintro k ⟨p, hr⟩
      exact (hrow k p hr).key_mem h
    · exact Keys.mono hmono
  have hself : ∀ k p, Row d' k p → Row d' k k ∧ Row d' p p := by
    intro k p hr
    have hm := hrow k p hr
    obtain ⟨q₁, hk⟩ := hm.key_mem h
    obtain ⟨q₂, hp⟩ := hm.parent_mem h
    exact ⟨(h.selfLoop _ _ hk).1.mono hmono, (h.selfLoop _ _ hp).1.mono hmono⟩
  have hends : EndsFree d' := fun k p hr =>
    ⟨h.avoids k (h.key_mem_src (hkeys ▸ hr.mem_keys)),
      h.avoids p (h.key_mem_src (hkeys ▸ (hself k p hr).2.mem_keys))⟩
  have hcong : ∀ a b, Cong src a b ↔ Cong (view d') a b := by
    intro a b
    rw [h.cong]
    constructor
    · exact Cong.mono_eqs (view_mono hmono)
    · exact fun hab => Cong.replay (D := view d') (E := view d)
        (fun q hq => (hrow q.1 q.2 hq).cong_view h) hab
  have hlive : ∀ p ∈ Keys d, ∀ k, Row d' k p → Cong (liveView d') k p := by
    intro p hp
    refine (h.keys_finite.wellFoundedOn (r := fun s t => Term.blt s t = true)).induction hp
      (P := fun p => ∀ k, Row d' k p → Cong (liveView d') k p) ?_
    intro p _ ih k hkp
    by_cases hs : ufRowT k p ∈ d'.subsumed
    · rw [hsub] at hs
      rcases hs with hs | hs
      · obtain ⟨k', p', q, heq, _, hkq, hpq, hlt⟩ := h.marks _ hs
        obtain ⟨rfl, rfl⟩ := ufRowT_inj heq
        have hq : q ∈ Keys d := h.parent_mem_keys hkq
        exact (ih q hq hlt k (hkq.mono hmono)).trans (ih q hq hlt p (hpq.mono hmono)).symm
      · obtain ⟨k', p', q, heq, _, hlt, hkq, hpq⟩ := mem_runMarks_maint h hs
        obtain ⟨rfl, rfl⟩ := ufRowT_inj heq
        have hq : q ∈ Keys d := hkeys ▸ (hself _ _ hkq).2.mem_keys
        exact (ih q hq hlt k hkq).trans (ih q hq hlt p hpq).symm
    · exact (Edge.of_row hdiag hufOnly hends hkp hs).cong_liveView
  exact {
    diag := hdiag
    ufOnly := hufOnly
    finite := RunRules.finite_eqs h.finite _
    marks := by
      intro t ht
      rw [hsub] at ht
      rcases ht with ht | ht
      · obtain ⟨k, p, q, heq, hkp, hkq, hpq, hlt⟩ := h.marks t ht
        exact ⟨k, p, q, heq, hkp.mono hmono, hkq.mono hmono, hpq.mono hmono, hlt⟩
      · obtain ⟨k, p, q, heq, hkp, hlt, hkq, hpq⟩ := mem_runMarks_maint h ht
        exact ⟨k, p, q, heq, (h.row_of_edge hkp).mono hmono, hkq, hpq, hlt⟩
    down := fun k p hr => (hrow k p hr).down h
    selfLoop := hself
    keys := hkeys.trans h.keys
    avoids := h.avoids
    cong := hcong
    liveCong := fun k p hr => hlive p (hkeys ▸ (hself k p hr).2.mem_keys) k hr
    srcSubsumed := h.srcSubsumed }

/-- Rows only grow along a maintenance round. -/
theorem maint_eqs_mono (d : Database) : d.eqs ⊆ (RunRules (maintenance P) d).eqs := by
  rw [RunRules.eq_pair]; exact Set.subset_union_left

theorem maint_subsumed_mono (d : Database) :
    d.subsumed ⊆ (RunRules (maintenance P) d).subsumed := by
  rw [RunRules.eq_pair]; exact Set.subset_union_left

/-- The keys are unchanged by a maintenance round. -/
theorem maint_keys (h : Rel src d) : Keys (RunRules (maintenance P) d) = Keys d :=
  (maint_round (P := P) h).keys.trans h.keys.symm

end Egglog.Congruence
