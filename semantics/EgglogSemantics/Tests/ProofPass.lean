import EgglogSemantics.Tests.GeneratedProvenance
import EgglogSemantics.Proofs.Resugar.Soundness

namespace Egglog.Tests.ProofPass

open GeneratedProvenance

private def seedCommand : Nat := match oldCertificate with
  | .rule _ command _ _ => command
  | _ => 0

-- The first union emits UF(C, B) at action 5.
def certificateTerm : Term := .app (Provenance.ruleName seedCommand 5) []
def annotatedRow : Entry := ⟨ufName, [c], [b, certificateTerm]⟩

theorem instrumentation_writes_certificate :
    ((Provenance.encode (Congruence.encode program)).bind fun encoded => do
      let C ← SourceProof.contextOf encoded
      some (encoded.any fun cmd => match cmd with
        | .rule r => r.query.isEmpty && r.actions.any fun action =>
            Provenance.actionRoot C.sig [] action == some annotatedRow.atom
        | _ => false)) = some true := by decide +kernel

theorem extracts_seed_certificate :
    ((Provenance.extractRow (Congruence.encode program) annotatedRow).bind
      (Provenance.check (Congruence.encode program))) = some oldRow := by decide +kernel

theorem lifts_seed_certificate :
    ((Resugar.extractRow program annotatedRow).bind (SourceProof.check program)) =
      some ⟨c, b⟩ := by decide +kernel

theorem altered_row_rejected :
    (Provenance.extractRow (Congruence.encode program)
      { annotatedRow with value := [a, certificateTerm] }).isNone = true := by decide +kernel

theorem missing_proof_column_rejected :
    (Provenance.extractRow (Congruence.encode program)
      { annotatedRow with value := [b] }).isNone = true := by decide +kernel

theorem compression_lifts :
    ((Resugar.lift program compressedCertificate).bind (SourceProof.check program)) =
      some ⟨c, a⟩ := by decide +kernel

theorem merge_lifts :
    ((Resugar.lift program mergedCertificate).bind (SourceProof.check program)) =
      some ⟨b, a⟩ := by decide +kernel

/-- The concrete extraction meets every premise of source soundness. -/
theorem extracted_claim_infers : reached.Infers c b := by
  have hw := (source_reached.ctorState Database.CtorState.empty source_fragment.ctorsOnly).wf
  obtain ⟨output, ho, _⟩ := Option.bind_eq_some_iff.mp lifts_seed_certificate
  apply Resugar.extractRow_infers source_reached hw source_saturated
    (C := (SourceProof.contextOf program).getD ⟨fun _ => none⟩)
    (target := (SourceProof.contextOf (Congruence.encode program)).getD ⟨fun _ => none⟩)
    (row := annotatedRow) (decl := Congruence.tableDecl 1)
    (claim := ⟨c, b⟩) (output := output)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ho

end Egglog.Tests.ProofPass
