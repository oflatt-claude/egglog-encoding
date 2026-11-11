import EgglogSemantics.Proofs.Provenance.GeneratedClaim

namespace Egglog.Provenance.Generated

/-- A checked lifted UF row proves its two columns equal in the source. -/
theorem check_uf_infers {P : Program} {src : Database}
    (hs : Reach Database.empty P.schedule src)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs src)
    {pf : Proof} {a b : Term} {output : SourceProof.Proof}
    (hc : check (Congruence.encode P) pf = some (.app ufName [a, b]))
    (hl : Resugar.lift P pf = some output) : src.Infers a b := by
  apply check_claim_infers hs hclosed hc (claim := ⟨a, b⟩) _ hl
  simp [Resugar.factClaim]

end Egglog.Provenance.Generated
