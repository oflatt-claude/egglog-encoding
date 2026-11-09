import EgglogSemantics.Impl.Closure
import EgglogSemantics.Proofs.SameMeaning

namespace Egglog
theorem mem_candidates {terms : Finset Term} {p : Term × Term} :
    p ∈ candidates terms ↔ p.1 ∈ terms ∧ p.2 ∈ terms := Finset.mem_product

theorem congrPair_app_iff {rel : Finset (Term × Term)} {f g : FnName} {as bs : List Term} :
    congrPair rel (.app f as) (.app g bs) = true ↔
      f = g ∧ List.Forall₂ (fun a b => (a, b) ∈ rel) as bs := by
  simp only [congrPair, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.forall₂_iff_zip]
  constructor
  · rintro ⟨⟨hf, hl⟩, hz⟩
    exact ⟨hf, hl, fun {a b} hab => hz (a, b) hab⟩
  · rintro ⟨hf, hl, hz⟩
    exact ⟨⟨hf, hl⟩, fun _ hq => hz hq⟩

theorem congrPair_elim {rel : Finset (Term × Term)} {a b : Term}
    (h : congrPair rel a b = true) :
    ∃ f as bs, a = .app f as ∧ b = .app f bs ∧
      List.Forall₂ (fun x y => (x, y) ∈ rel) as bs := by
  cases a with
  | lit _ => cases b <;> simp [congrPair] at h
  | app f as =>
    cases b with
    | lit _ => simp [congrPair] at h
    | app g bs =>
      obtain ⟨rfl, hz⟩ := congrPair_app_iff.mp h
      exact ⟨f, as, bs, rfl, rfl, hz⟩

theorem subset_congStep {terms : Finset Term} {rel : Finset (Term × Term)} :
    rel ⊆ congStep terms rel := Finset.subset_union_left

theorem mem_congStep {terms : Finset Term} {rel : Finset (Term × Term)} {p : Term × Term} :
    p ∈ congStep terms rel ↔
      p ∈ rel ∨ (p ∈ candidates terms ∧ stepAdds terms rel p = true) := by
  simp [congStep, Finset.mem_union, Finset.mem_filter]

/-! ### The closure is a fixpoint containing `rel` -/
theorem closure_fixpoint {terms : Finset Term} {rel : Finset (Term × Term)}
    (h : rel ⊆ candidates terms) :
    congStep terms (closure terms rel h) = closure terms rel h := by
  induction rel, h using closure.induct with
  | case1 rel h hfix => rw [closure, dif_pos hfix]; exact hfix
  | case2 rel h hfix ih => rw [closure, dif_neg hfix]; exact ih

theorem subset_closure {terms : Finset Term} {rel : Finset (Term × Term)}
    (h : rel ⊆ candidates terms) : rel ⊆ closure terms rel h := by
  induction rel, h using closure.induct with
  | case1 rel h hfix => rw [closure, dif_pos hfix]
  | case2 rel h hfix ih =>
    rw [closure, dif_neg hfix]
    exact subset_congStep.trans ih

theorem closure_subset {terms : Finset Term} {rel : Finset (Term × Term)}
    (h : rel ⊆ candidates terms) : closure terms rel h ⊆ candidates terms := by
  induction rel, h using closure.induct with
  | case1 rel h hfix => rw [closure, dif_pos hfix]; exact h
  | case2 rel h hfix ih => rw [closure, dif_neg hfix]; exact ih

/-! ### Correctness

Soundness is an induction over the iteration; completeness is `Cong.le` applied to the
fixpoint, one closure rule per premise. -/
theorem congStep_sound {db : Database} {terms : Finset Term} {rel : Finset (Term × Term)}
    (hterms : db.terms = ↑terms) (hrel : ∀ p ∈ rel, Cong db p.1 p.2) :
    ∀ p ∈ congStep terms rel, Cong db p.1 p.2 := by
  intro p hp
  obtain ⟨p₁, p₂⟩ := p
  rcases mem_congStep.mp hp with hp | ⟨hcand, hstep⟩
  · exact hrel (p₁, p₂) hp
  · have hmem : p₁ ∈ db.terms ∧ p₂ ∈ db.terms := by
      rw [hterms]; exact mem_candidates.mp hcand
    unfold stepAdds at hstep
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hstep
    rcases hstep with ((heq | hsym) | ⟨m, _, hm₁, hm₂⟩) | hcongr
    · exact heq ▸ Database.toCong hmem.1
    · exact (hrel _ hsym).symm
    · exact (hrel _ hm₁).trans (hrel _ hm₂)
    · obtain ⟨f, as, bs, rfl, rfl, hz⟩ := congrPair_elim hcongr
      exact Cong.congr (Database.toCong hmem.1)
        (CongList.forall₂.mpr (hz.imp fun {x y} hxy => hrel (x, y) hxy))

theorem closure_sound {db : Database} {terms : Finset Term}
    (hterms : db.terms = ↑terms) : ∀ (rel : Finset (Term × Term))
      (h : rel ⊆ candidates terms), (∀ p ∈ rel, Cong db p.1 p.2) →
      ∀ p ∈ closure terms rel h, Cong db p.1 p.2 := by
  intro rel h
  induction rel, h using closure.induct with
  | case1 rel h hfix => intro hrel; rw [closure, dif_pos hfix]; exact hrel
  | case2 rel h hfix ih =>
    intro hrel
    rw [closure, dif_neg hfix]
    exact ih (congStep_sound hterms hrel)

end Egglog
