import EgglogSemantics.Resugar.Lift
import EgglogSemantics.SourceProof.Soundness

namespace Egglog.Resugar

theorem lift_checked {P : Program} {C : SourceProof.Context} {input : Provenance.Certificate}
    {output : SourceProof.Certificate} {fact : Term} {claim : SourceProof.Claim}
    (hC : SourceProof.contextOf P = some C)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P C fact = some claim) (h : lift P input = some output) :
    SourceProof.check P output = some claim := by
  unfold lift at h
  split at h
  · contradiction
  · have hf' : Provenance.check ((Congruence.compile P).map Congruence.Command.command)
        input = some fact := hf
    simp only [hC, hf', hc, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨state, _, hstate⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨root, _, hroot⟩ := Option.bind_eq_some_iff.mp hstate
    split at hroot
    · rename_i hcheck
      cases Option.some.inj hroot
      simpa only [beq_iff_eq] using hcheck
    · contradiction

/-- Lifting establishes the mapped claim against the original source program. -/
theorem lift_supported {P : Program} {C : SourceProof.Context} {db : Database}
    {input : Provenance.Certificate} {output : SourceProof.Certificate}
    {fact : Term} {claim : SourceProof.Claim}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db)
    (hC : SourceProof.contextOf P = some C)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P C fact = some claim) (h : lift P input = some output) :
    claim.Supported db :=
  SourceProof.check_supported hs hw hclosed (lift_checked hC hf hc h)

theorem lift_sound {P : Program} {C : SourceProof.Context} {db : Database}
    {input : Provenance.Certificate} {output : SourceProof.Certificate}
    {fact : Term} {claim : SourceProof.Claim}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db)
    (hC : SourceProof.contextOf P = some C)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P C fact = some claim) (h : lift P input = some output)
    (hl : claim.lhs ∈ db.terms) (hr : claim.rhs ∈ db.terms) :
    Cong db claim.lhs claim.rhs :=
  (lift_supported hs hw hclosed hC hf hc h).holds hw hl hr

end Egglog.Resugar
