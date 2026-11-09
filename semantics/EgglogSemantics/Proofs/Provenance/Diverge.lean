import EgglogSemantics.Proofs.Provenance.Simulate
import EgglogSemantics.Proofs.Congruence.Diverge
import EgglogSemantics.Proofs.Divergence

/-! Divergence corresponds: a schedule has a saturation that never settles exactly when
its instrumentation does. An infinite trace is transported pass by pass through the
simulation, and the instrumented passes after the original settles terminate. -/

namespace Egglog.Provenance

variable {P : Program}

/-- The divergence correspondence for a schedule. -/
def Div (P : Program) (S S' : Schedule) : Prop :=
  ∀ {d d' : Database}, Inv P d → RelC P d d' → (Diverges d S ↔ Diverges d' S')

/-- A trace of changing passes of the original gives one of the instrumentation. -/
theorem infinitePasses_fwd (hP : programOk P = true) {S S' : Schedule} (hI : Instr S S')
    (hS : S.rules ⊆ P.rules) (hK : ∀ r ∈ S.rules, Query.VarsKeyed r.query) {d d' : Database}
    (hd : Inv P d) (hrel : RelC P d d') (hi : InfinitePasses S d) : InfinitePasses S' d' := by
  obtain ⟨trace, h0, hstep⟩ := hi
  have hinv : ∀ n, Inv P (trace n) := by
    intro n
    induction n with
    | zero => rw [h0]; exact hd
    | succ n ih => exact ih.reach hP hS (hstep n).1
  -- The instrumented trace, chosen pass by pass.
  let step : ∀ n, {d' // RelC P (trace n) d'} → {d' // RelC P (trace (n + 1)) d'} := fun n p =>
    ⟨Classical.choose (fwd_relC hP hI hS hK (hinv n) p.2 (hstep n).1),
      (Classical.choose_spec (fwd_relC hP hI hS hK (hinv n) p.2 (hstep n).1)).2⟩
  have hstepR : ∀ n (p : {d' // RelC P (trace n) d'}), Reach p.1 S' (step n p).1 :=
    fun n p => (Classical.choose_spec (fwd_relC hP hI hS hK (hinv n) p.2 (hstep n).1)).1
  let chain : ∀ n, {d' // RelC P (trace n) d'} := fun n =>
    Nat.rec (motive := fun n => {d' // RelC P (trace n) d'}) ⟨d', h0 ▸ hrel⟩ step n
  refine ⟨fun n => (chain n).1, rfl, fun n => ⟨?_, ?_⟩⟩
  · exact hstepR n (chain n)
  · intro hsame
    exact (hstep n).2 ((chain n).2.sameMeaning_of_inst hP (chain (n + 1)).2 hsame)

/-- An instrumented trace of passes gives a trace of the original, pass by pass. -/
theorem trace_bwd (hP : programOk P = true) {S S' : Schedule} (hI : Instr S S')
    (hS : S.rules ⊆ P.rules) (hK : ∀ r ∈ S.rules, Query.VarsKeyed r.query) {d d' : Database}
    (hd : Inv P d) (hrel : RelC P d d') {trace' : Nat → Database} (h0 : trace' 0 = d')
    (hstep : ∀ n, Reach (trace' n) S' (trace' (n + 1))) :
    ∃ trace : Nat → Database, trace 0 = d ∧
      (∀ n, Reach (trace n) S (trace (n + 1))) ∧ ∀ n, RelC P (trace n) (trace' n) := by
  let Carrier := fun n => {e // Inv P e ∧ RelC P e (trace' n)}
  let step : ∀ n, Carrier n → Carrier (n + 1) := fun n p =>
    ⟨Classical.choose (bwd_relC hP hI hS hK p.2.1 p.2.2 (hstep n)),
      (p.2.1.reach hP hS (Classical.choose_spec (bwd_relC hP hI hS hK p.2.1 p.2.2 (hstep n))).1),
      (Classical.choose_spec (bwd_relC hP hI hS hK p.2.1 p.2.2 (hstep n))).2⟩
  have hstepR : ∀ n (p : Carrier n), Reach p.1 S (step n p).1 :=
    fun n p => (Classical.choose_spec (bwd_relC hP hI hS hK p.2.1 p.2.2 (hstep n))).1
  let chain : ∀ n, Carrier n := fun n =>
    Nat.rec (motive := Carrier) ⟨d, hd, h0 ▸ hrel⟩ step n
  refine ⟨fun n => (chain n).1, rfl, fun n => ?_, fun n => (chain n).2.2⟩
  exact hstepR n (chain n)

/-- After the original settles, the instrumented saturation does not diverge. -/
theorem not_diverges_after_fixpoint (hP : programOk P = true) {S S' : Schedule} (hI : Instr S S')
    (hS : S.rules ⊆ P.rules) (hK : ∀ r ∈ S.rules, Query.VarsKeyed r.query) {d e d' : Database}
    (hd : Inv P d) (hp : Reach d S e) (heq : d.SameMeaning e) (hrel : RelC P e d') :
    ¬ Diverges d' (.saturate S') := by
  intro hdiv
  have he : Inv P e := hd.reach hP hS hp
  obtain ⟨hstable, hpass⟩ := stable_of_fixpoint hP hS hd hp heq
  obtain ⟨e', he', _, _⟩ := extra_passes hP hS (sim_fwd hP hI hS hK) he hstable hpass e d' he
    (Database.SameMeaning.refl e) hrel
  exact Congruence.Diverges.not_reach hdiv he'

/-- Divergence corresponds for every schedule. -/
theorem sim_div (hP : programOk P = true) : ∀ {S S' : Schedule}, Instr S S' →
    S.rules ⊆ P.rules → (∀ r ∈ S.rules, Query.VarsKeyed r.query) → Div P S S' := by
  intro S S' hI
  induction hI with
  | @run R R' _ =>
    intro _ _ d d' _ _
    exact ⟨fun h => (not_cmdDiverges_of_allConstructors (S := .run R) trivial h).elim,
      fun h => (not_cmdDiverges_of_allConstructors (S := .run R') trivial h).elim⟩
  | @seq S₁ S₂ S₁' S₂' hI₁ _ ih₁ ih₂ =>
    intro hS hK d d' hd hrel
    have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
    have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
    have hK₁ : ∀ r ∈ S₁.rules, Query.VarsKeyed r.query :=
      fun r hr => hK r (List.mem_append_left _ hr)
    have hK₂ : ∀ r ∈ S₂.rules, Query.VarsKeyed r.query :=
      fun r hr => hK r (List.mem_append_right _ hr)
    change Diverges d (.seq S₁ S₂) ↔ Diverges d' (.seq S₁' S₂')
    rw [Diverges.append_iff, Diverges.append_iff]
    constructor
    · rintro (h | ⟨mid, hmid, h⟩)
      · exact Or.inl ((ih₁ hS₁ hK₁ hd hrel).mp h)
      · obtain ⟨d₁, hd₁, hrel₁⟩ := fwd_relC hP hI₁ hS₁ hK₁ hd hrel hmid
        exact Or.inr ⟨d₁, hd₁, (ih₂ hS₂ hK₂ (hd.reach hP hS₁ hmid) hrel₁).mp h⟩
    · rintro (h | ⟨d₁, hd₁, h⟩)
      · exact Or.inl ((ih₁ hS₁ hK₁ hd hrel).mpr h)
      · obtain ⟨mid, hmid, hrel₁⟩ := bwd_relC hP hI₁ hS₁ hK₁ hd hrel hd₁
        exact Or.inr ⟨mid, hmid, (ih₂ hS₂ hK₂ (hd.reach hP hS₁ hmid) hrel₁).mpr h⟩
  | @saturate S S' hI ih =>
    intro hS hK d d' hd hrel
    have hS' : S.rules ⊆ P.rules := hS
    have hK' : ∀ r ∈ S.rules, Query.VarsKeyed r.query := hK
    have ihS : Div P S S' := ih hS' hK'
    constructor
    · intro h
      generalize hT : Schedule.saturate S = T at h
      induction h generalizing d' with
      | seqLeft => cases hT
      | seqRight => cases hT
      | body hb =>
        cases hT
        exact .body ((ihS hd hrel).mp hb)
      | @later d e₁ _ hp hn _ ih₂ =>
        cases hT
        obtain ⟨d₁, hd₁, hrel₁⟩ := fwd_relC hP hI hS' hK' hd hrel hp
        exact .later hd₁ (hrel.not_sameMeaning hP hrel₁ hn) (ih₂ (hd.reach hP hS' hp) hrel₁ rfl)
      | forever hi =>
        cases hT
        exact .forever (infinitePasses_fwd hP hI hS' hK' hd hrel hi)
    · intro h
      generalize hT : Schedule.saturate S' = T at h
      induction h generalizing d with
      | seqLeft => cases hT
      | seqRight => cases hT
      | body hb =>
        cases hT
        exact .body ((ihS hd hrel).mpr hb)
      | @later d' d₁ _ hp hn hdiv ih₂ =>
        cases hT
        obtain ⟨e₁, he₁, hrel₁⟩ := bwd_relC hP hI hS' hK' hd hrel hp
        by_cases hsame : d.SameMeaning e₁
        · exact (not_diverges_after_fixpoint hP hI hS' hK' hd he₁ hsame hrel₁ hdiv).elim
        · exact .later he₁ hsame (ih₂ (hd.reach hP hS' he₁) hrel₁ rfl)
      | @forever d' _ hi =>
        cases hT
        obtain ⟨trace', h0, hstep⟩ := hi
        obtain ⟨trace, h0', hpass, hrel'⟩ :=
          trace_bwd hP hI hS' hK' hd hrel h0 (fun n => (hstep n).1)
        by_cases hall : ∀ n, ¬ (trace n).SameMeaning (trace (n + 1))
        · exact .forever ⟨trace, h0', fun n => ⟨hpass n, hall n⟩⟩
        · exfalso
          push Not at hall
          obtain ⟨n, hn⟩ := hall
          have hinv : Inv P (trace n) := by
            clear hn
            induction n with
            | zero => rw [h0']; exact hd
            | succ n ih => exact ih.reach hP hS' (hpass n)
          -- The instrumented trace from `n + 1` is still infinite, yet the original has
          -- settled.
          have hdiv : Diverges (trace' (n + 1)) (.saturate S') :=
            .forever ⟨fun k => trace' (n + 1 + k), rfl, fun k => by
              have := hstep (n + 1 + k)
              rwa [show n + 1 + k + 1 = n + 1 + (k + 1) by omega] at this⟩
          exact not_diverges_after_fixpoint hP hI hS' hK' hinv (hpass n) hn (hrel' (n + 1)) hdiv

end Egglog.Provenance
