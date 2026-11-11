import EgglogSemantics.Proofs.Provenance.Diverge
import EgglogSemantics.Proofs.Result

/-! Provenance pass correctness from the empty state: preservation of outcomes and
divergence, and recovery of the original final meaning by erasing the log. The paper's
statement is `ExtlogTheorems.provenance_pass_correct`. -/

namespace Egglog.Provenance

variable {P : Program}

/-- The check on the instrumented final state, with subsumption forgotten, holds exactly
when it holds on the original's. -/
theorem check_corr (hP : programOk P = true) (hk : Query.VarsKeyed P.check) {e d' : Database}
    (he : Inv P e) (hrel : RelC P e d') :
    QueryHolds d'.forgetSubsumed P.check ↔ QueryHolds e.forgetSubsumed P.check := by
  obtain ⟨x, hx, hr⟩ := hrel
  rw [queryHolds_iff (hr.forgetSubsumed.shadow hP) hk (logFreeQuery_check hP)]
  have hm : e.forgetSubsumed.SameMeaning x.forgetSubsumed := hx.forgetSubsumed
  have ht : e.forgetSubsumed.terms = x.forgetSubsumed.terms :=
    he.good.forgetSubsumed.terms_eq_of_sameMeaning hr.inv.good.forgetSubsumed hm
  exact ⟨fun ⟨σ, hσ⟩ => ⟨σ, QueryMatches.sameMeaning hm.symm ht.symm hσ⟩,
    fun ⟨σ, hσ⟩ => ⟨σ, QueryMatches.sameMeaning hm ht hσ⟩⟩

/-- The instrumented program's outcomes and divergence agree with the original's, and
erasing the log from its final state gives the original's final state up to meaning. -/
theorem encode_correct {P P' : Program} (hI : Instrumentable P) (h : encode P = some P') :
    (∀ o : Result, Eval Database.empty P' o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty P'.schedule ↔ Diverges Database.empty P.schedule) ∧
    (∀ d e, Reach Database.empty P'.schedule d → Reach Database.empty P.schedule e →
      d.eraseLog.SameMeaning e) := by
  obtain ⟨hP, hsched, hcheck⟩ := encode_some h
  have hinst : Instr P.schedule P'.schedule := hsched ▸ encodeSchedule_instr P.schedule 0
  have hS : P.schedule.rules ⊆ P.rules := fun _ hr => hr
  have hK : ∀ r ∈ P.schedule.rules, Query.VarsKeyed r.query := hI.keyedRules
  have hinv : Inv P Database.empty := Inv.empty
  have hrel : RelC P Database.empty Database.empty := RelC.of_rel (Rel.empty P)
  have hchk : ∀ {e d' : Database}, Inv P e → RelC P e d' →
      (QueryHolds d'.forgetSubsumed P'.check ↔ QueryHolds e.forgetSubsumed P.check) := by
    intro e d' he hr
    rw [hcheck]
    exact check_corr hP hI.keyedCheck he hr
  refine ⟨fun o => ?_, ?_, ?_⟩
  · cases o with
    | ok =>
      rw [Eval.ok_iff, Eval.ok_iff]
      constructor
      · rintro ⟨d, hd, hq⟩
        obtain ⟨e, he, hrel'⟩ := bwd_relC hP hinst hS hK hinv hrel hd
        exact ⟨e, he, (hchk (hinv.reach hP hS he) hrel').mp hq⟩
      · rintro ⟨e, he, hq⟩
        obtain ⟨d, hd, hrel'⟩ := fwd_relC hP hinst hS hK hinv hrel he
        exact ⟨d, hd, (hchk (hinv.reach hP hS he) hrel').mpr hq⟩
    | checkFailed =>
      rw [Eval.failed_iff, Eval.failed_iff]
      constructor
      · rintro ⟨d, hd, hq⟩
        obtain ⟨e, he, hrel'⟩ := bwd_relC hP hinst hS hK hinv hrel hd
        exact ⟨e, he, fun hq' => hq ((hchk (hinv.reach hP hS he) hrel').mpr hq')⟩
      · rintro ⟨e, he, hq⟩
        obtain ⟨d, hd, hrel'⟩ := fwd_relC hP hinst hS hK hinv hrel he
        exact ⟨d, hd, fun hq' => hq ((hchk (hinv.reach hP hS he) hrel').mp hq')⟩
  · exact (sim_div hP hinst hS hK hinv hrel).symm
  · intro d e hd he
    obtain ⟨e₁, he₁, x, hx, hr⟩ := bwd_relC hP hinst hS hK hinv hrel hd
    obtain rfl := he₁.det he
    rw [hr.eraseLog hP]
    exact hx.symm

end Egglog.Provenance
