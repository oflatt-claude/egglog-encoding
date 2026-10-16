import EgglogSemantics.Proofs.StatePreservation
import EgglogSemantics.Proofs.DiagonalPreservation
import EgglogSemantics.Proofs.LiveTables

/-! Redundant value assertions commute with completed diagonal rounds. -/

namespace Egglog

theorem Database.StoreOk.entries_eq_of_terms_eq {d e : Database}
    (hd : d.StoreOk) (he : e.StoreOk) (hsig : d.sig = e.sig)
    (ht : d.terms = e.terms) : d.entries = e.entries := by
  ext row
  constructor
  · intro hr
    exact he.entry_of_held_atom (hsig ▸ hr.1) (ht ▸ Cong.direct hr.2)
  · intro hr
    exact hd.entry_of_held_atom (hsig.symm ▸ hr.1) (ht.symm ▸ Cong.direct hr.2)

private def overlay (d : Database) (E : Set (Term × Term)) : Database :=
  { d with eqs := d.eqs ∪ E }

private theorem overlay_contained (d : Database) (E : Set (Term × Term)) :
    d.Contained (overlay d E) := ⟨Set.subset_union_left⟩

private theorem overlay_entries {d : Database} {E : Set (Term × Term)}
    (hE : ∀ p ∈ E, p.1.IsValue d.sig) : (overlay d E).entries = d.entries := by
  ext row
  constructor
  · rintro ⟨hv, hp | hp⟩
    · exact ⟨hv, hp⟩
    · exact (hv.atom_not_value (hE _ hp)).elim
  · rintro ⟨hv, hp⟩
    exact ⟨hv, Or.inl hp⟩

private theorem overlay_addTerm (d : Database) (E : Set (Term × Term)) (t : Term) :
    (overlay d E).addTerm t = overlay (d.addTerm t) E := by
  apply Database.ext <;> try rfl
  exact Set.insert_union.symm

private theorem overlay_addEq (d : Database) (E : Set (Term × Term)) (a b : Term) :
    (overlay d E).addEq a b = overlay (d.addEq a b) E := by
  apply Database.ext <;> try rfl
  exact Set.insert_union.symm

private theorem evalAction_overlay (d : Database) (E : Set (Term × Term)) (a : Action) :
    evalAction (overlay d E) a = (evalAction d a).map (overlay · E) := by
  cases a with
  | expr e =>
      simp only [evalAction, overlay, Option.map_map]
      congr 1
      funext t
      exact overlay_addTerm d E t
  | union a b =>
      simp only [evalAction, overlay]
      cases ha : a.eval d.sig d.env <;> simp only [Option.bind_none, Option.map_none,
        Option.bind_some]
      rename_i ta
      cases hb : b.eval d.sig d.env <;> simp only [Option.bind_none, Option.map_none,
        Option.bind_some]
      split <;> simp only [Option.map_none, Option.map_some]
      exact congrArg some (overlay_addEq d E _ _)

private theorem evalActions_overlay (d : Database) (E : Set (Term × Term))
    (as : List Action) :
    evalActions (overlay d E) as = (evalActions d as).map (overlay · E) := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih =>
      simp only [evalActions, evalAction_overlay]
      cases he : evalAction d a <;> simp only [Option.map_none, Option.bind_none,
        Option.map_some, Option.bind_some]
      exact ih _

private theorem evalLocalActions_overlay (d : Database) (E : Set (Term × Term))
    (as : List Action) (σ : Env) :
    evalLocalActions (overlay d E) as σ = (evalLocalActions d as σ).map (overlay · E) := by
  change (evalActions (overlay { d with env := σ ++ d.env } E) as).map _ = _
  rw [evalActions_overlay]
  simp only [evalLocalActions, Option.map_map]
  rfl

private theorem overlay_eraseEntry {d : Database} {E : Set (Term × Term)}
    (hE : ∀ p ∈ E, p.1.IsValue d.sig) {row : Entry} (hv : row.Valid d.sig) :
    (overlay d E).eraseEntry row = overlay (d.eraseEntry row) E := by
  apply Database.ext <;> try rfl
  ext p
  have hn : p ∈ E → p ≠ (row.atom, row.atom) := by
    rintro hp rfl
    exact hv.atom_not_value (hE _ hp)
  simp only [Database.eraseEntry_eqs, overlay, Set.mem_union, Set.mem_sdiff,
    Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (⟨hp | hp, hne⟩ | hp)
    · exact Or.inl (Or.inl ⟨hp, hne⟩)
    · exact Or.inr hp
    · exact Or.inl (Or.inr hp)
  · rintro ((⟨hp, hne⟩ | hp) | hp)
    · exact Or.inl ⟨Or.inl hp, hne⟩
    · exact Or.inr hp
    · exact Or.inl ⟨Or.inr hp, hn hp⟩

private theorem MergeValues.with_overlay {d e : Database} {decl : FnDecl}
    {old new vs : List Term} (hm : MergeValues d decl old new e vs)
    (E : Set (Term × Term)) : MergeValues (overlay d E) decl old new (overlay e E) vs := by
  cases hm with
  | unchanged hd hc => exact .unchanged hd hc
  | @changed post vs ovs nvs body res hd hc hb hr =>
      apply MergeValues.changed (d := overlay post E) hd hc
      · change evalActions (overlay { d with env := mergeEnv ovs nvs old new } E) body = _
        rw [evalActions_overlay, hb]
        rfl
      · exact hr

private theorem MergeStep.with_overlay {d e : Database} (hm : MergeStep d e)
    {E : Set (Term × Term)} (hE : ∀ p ∈ E, p.1.IsValue d.sig) :
    MergeStep (overlay d E) (overlay e E) := by
  cases hm with
  | @collide post old new decl vs ho hn hne hname hd hk hv =>
      change MergeStep (overlay d E) (overlay (post.addTerm _) E)
      rw [← overlay_addTerm]
      apply MergeStep.collide (db := overlay d E)
        ((overlay_entries hE).symm ▸ ho) ((overlay_entries hE).symm ▸ hn)
        hne hname hd (hk.mono (overlay_contained d E))
      rw [overlay_eraseEntry hE ho.1,
        overlay_eraseEntry (d := d.eraseEntry old) hE hn.1]
      exact hv.with_overlay E

private theorem MergeClosure.with_overlay {d e : Database} (hm : MergeClosure d e)
    {E : Set (Term × Term)} (hE : ∀ p ∈ E, p.1.IsValue d.sig) :
    MergeClosure (overlay d E) (overlay e E) := by
  induction hm with
  | refl => exact .refl
  | tail hc hs ih => exact ih.tail (hs.with_overlay (by simpa only [MergeClosure.sig hc] using hE))

private theorem MergeStep.value_eqs {d e : Database} (hm : MergeStep d e)
    {p : Term × Term} (hv : p.1.IsValue d.sig) (hp : p ∈ d.eqs) : p ∈ e.eqs := by
  cases hm with
  | @collide post old new decl vs ho hn hne hname hd hk hvals =>
      have keep : p ∈ ((d.eraseEntry old).eraseEntry new).eqs := by
        apply Or.inl
        refine ⟨Or.inl ⟨hp, ?_⟩, ?_⟩ <;> intro he
        · have he := Set.mem_singleton_iff.mp he
          subst p
          exact ho.1.atom_not_value hv
        · have he := Set.mem_singleton_iff.mp he
          subst p
          exact hn.1.atom_not_value hv
      apply Or.inr
      cases hvals with
      | unchanged => exact keep
      | changed _ _ hb _ => exact (evalActions_contained hb).eqs keep

private theorem MergeClosure.value_eqs {d e : Database} (hm : MergeClosure d e)
    {p : Term × Term} (hv : p.1.IsValue d.sig) (hp : p ∈ d.eqs) : p ∈ e.eqs := by
  induction hm with
  | refl => exact hp
  | tail hc hs ih => exact hs.value_eqs ((MergeClosure.sig hc).symm ▸ hv) ih

private theorem matches_of_diag_terms {d e : Database} (hd : d.Diag)
    (hsig : d.sig = e.sig) (ht : d.terms = e.terms) {p : Pattern} {σ : Env}
    (hm : Matches d p σ) : Matches e p σ := by
  cases hm with
  | expr hw he hc =>
      have hwt := congOn_eq_of_diag hd hc
      subst hwt
      exact .expr (ht ▸ hw) (hsig ▸ he)
        ((ht ▸ hw).mono (Database.Contained.addTerms [_] e))
  | eq hw ha hb hwa hab =>
      have hwt := congOn_eq_of_diag hd hwa
      have hab := congOn_eq_of_diag hd hab
      subst hwt
      subst hab
      apply Matches.eq (ht ▸ hw) (hsig ▸ ha) (hsig ▸ hb)
      · exact (ht ▸ hw).mono (Database.Contained.addTerms _ e)
      · exact (ht ▸ hw).mono (Database.Contained.addTerms _ e)

private theorem query_of_diag_terms {d e : Database} (hd : d.Diag)
    (hsig : d.sig = e.sig) (ht : d.terms = e.terms) {q : Query} {σ : Env}
    (hq : ValidQuerySubst d q σ) : ValidQuerySubst e q σ := by
  obtain ⟨σs, hσs, hu⟩ := hq
  refine ⟨σs, hσs.imp ?_, hu⟩
  intro p σ hp
  exact ⟨⟨hp.1.1, fun b hb => ⟨ht ▸ (hp.1.2 b hb).1,
    hsig ▸ (hp.1.2 b hb).2⟩⟩, matches_of_diag_terms hd hsig ht hp.2⟩

private theorem runRules_overlay (d : Database) (E : Set (Term × Term))
    (hquery : ∀ q σ, ValidQuerySubst (overlay d E) q σ ↔ ValidQuerySubst d q σ)
    (R : RulesetName) : RunRules R (overlay d E) = overlay (RunRules R d) E := by
  apply Database.ext <;> try rfl
  ext p
  constructor
  · rintro ((hp | hp) | hp)
    · exact Or.inl (Or.inl hp)
    · exact Or.inr hp
    · obtain ⟨out, ⟨r, hr, hR, σ, hσ, he⟩, hp⟩ := Set.mem_iUnion₂.mp hp
      rw [evalLocalActions_overlay] at he
      obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp he
      rcases hp with hp | hp
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr
          ⟨raw, ⟨r, hr, hR, σ, (hquery _ _).mp hσ, hraw⟩, hp⟩))
      · exact Or.inr hp
  · rintro ((hp | hp) | hp)
    · exact Or.inl (Or.inl hp)
    · obtain ⟨out, ⟨r, hr, hR, σ, hσ, he⟩, hp⟩ := Set.mem_iUnion₂.mp hp
      refine Or.inr (Set.mem_iUnion₂.mpr
        ⟨overlay out E, ⟨r, hr, hR, σ, (hquery _ _).mpr hσ, ?_⟩, Or.inl hp⟩)
      rw [evalLocalActions_overlay, he]
      rfl
    · exact Or.inl (Or.inr hp)

/-- A completed unchanged diagonal round has absorbed all redundant root assertions. -/
theorem RunStep.self_of_sameMeaning {d e : Database} {R : RulesetName}
    (hn : d.NoUnions) (hs : d.StoreOk) (hmw : d.sig.MergesWidthOk)
    (hr : RunStep R d e) (heq : d.SameMeaning e) : RunStep R e e := by
  have hen := hr.noUnions hn
  have hes := hr.storeOk hs hmw
  have ht := heq.terms_eq_of_diag hn.diag hen.diag
  have hrows := hs.entries_eq_of_terms_eq hes heq.sig ht
  have hde : d.eqs ⊆ e.eqs := by
    intro p hp
    rcases hs.typed p hp with hv | ⟨row, hv, rfl⟩
    · exact hr.1.value_eqs hv.1 (Or.inl hp)
    · exact (hrows ▸ (show row ∈ d.entries from ⟨hv, hp⟩)).2
  let E := e.eqs \ d.eqs
  have hE : ∀ p ∈ E, p.1.IsValue d.sig ∧ p.1 = p.2 := by
    intro p hp
    refine ⟨?_, hen.diag p hp.1⟩
    rcases hes.typed p hp.1 with hv | ⟨row, hv, he⟩
    · exact heq.sig.symm ▸ hv.1
    · subst p
      exact (hp.2 ((hrows.symm ▸ (show row ∈ e.entries from ⟨hv, hp.1⟩)).2)).elim
  have hover : e = overlay d E := by
    apply Database.ext
    · exact hr.1.sig
    · change e.eqs = d.eqs ∪ (e.eqs \ d.eqs)
      exact (Set.union_sdiff_cancel hde).symm
    · exact hr.1.envRules.1
    · exact hr.1.envRules.2
  have hquery : ∀ q σ, ValidQuerySubst (overlay d E) q σ ↔ ValidQuerySubst d q σ := by
    rw [← hover]
    intro q σ
    exact ⟨query_of_diag_terms hen.diag heq.sig.symm ht.symm,
      query_of_diag_terms hn.diag heq.sig ht⟩
  have hraw : RunRules R e = overlay (RunRules R d) E := by
    rw [hover]
    exact runRules_overlay d E hquery R
  have hfinish : overlay e E = e := by
    apply Database.ext <;> try rfl
    exact Set.union_eq_self_of_subset_right Set.sdiff_subset
  refine ⟨?_, hr.2⟩
  rw [hraw, ← hfinish]
  exact MergeClosure.with_overlay hr.1 (fun p hp => (hE p hp).1)

end Egglog
