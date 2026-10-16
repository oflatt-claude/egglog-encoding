import EgglogSemantics.Proofs.Provenance.GeneratedClaim
import EgglogSemantics.Provenance.Extract

/-! Accepted provenance proves equalities in a reached, saturated source model,
including when the certified rows were replaced. -/

namespace Egglog.Provenance

/-- Accepted generated provenance establishes its mapped claim in the source. -/
theorem check_sound {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src)
    {C : SourceProof.Context} (hC : SourceProof.contextOf P = some C)
    {pf : Proof} {t : Term} {claim : SourceProof.Claim}
    (hc : check (Congruence.encode P) pf = some t)
    (hm : Resugar.factClaim P C t = some claim) : src.Infers claim.lhs claim.rhs :=
  Generated.check_claim_infers hp hs hclosed hC hc hm

theorem extractRow_checked {P : Program} {C : SourceProof.Context} {r : Entry}
    {d : FnDecl} {pf : Proof}
    (hC : SourceProof.contextOf P = some C) (hd : C.sig r.name = some d)
    (h : extractRow P r = some pf) :
    check P pf = some (.app r.name (r.key ++ r.value.take d.outArity)) := by
  simp only [extractRow, hC, Option.bind_eq_bind, Option.bind_some, hd] at h
  split at h
  · contradiction
  · obtain ⟨t, _, ht⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨p, _, hp⟩ := Option.bind_eq_some_iff.mp ht
    split at hp
    · rename_i hcheck
      cases Option.some.inj hp
      simpa only [beq_iff_eq] using hcheck
    · contradiction

/-- Extraction's data columns determine the source claim, independently of proof metadata. -/
theorem extractRow_sound {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src)
    {C target : SourceProof.Context} (hC : SourceProof.contextOf P = some C)
    (hT : SourceProof.contextOf (Congruence.encode P) = some target)
    {r : Entry} {d : FnDecl} {pf : Proof} {claim : SourceProof.Claim}
    (hd : target.sig r.name = some d)
    (h : extractRow (Congruence.encode P) r = some pf)
    (hm : Resugar.factClaim P C (.app r.name (r.key ++ r.value.take d.outArity)) =
      some claim) : src.Infers claim.lhs claim.rhs :=
  check_sound hp hs hclosed hC (extractRow_checked hT hd h) hm

end Egglog.Provenance
