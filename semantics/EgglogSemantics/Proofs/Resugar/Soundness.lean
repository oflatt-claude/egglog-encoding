import EgglogSemantics.Resugar.Lift
import EgglogSemantics.Proofs.SourceProof.Soundness
import EgglogSemantics.Proofs.Provenance.Soundness

namespace Egglog.Resugar

theorem lift_checked {P : Program} {C : SourceProof.Context} {input : Provenance.Proof}
    {output : SourceProof.Proof} {fact : Term} {claim : SourceProof.Claim}
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
    obtain ⟨result, _, hresult⟩ := Option.bind_eq_some_iff.mp h
    split at hresult
    · rename_i hcheck
      cases Option.some.inj hresult
      simpa only [beq_iff_eq] using hcheck
    · contradiction

/-- Lifting establishes the mapped claim against the original source program. -/
theorem lift_supported {P : Program} {C : SourceProof.Context} {db : Database}
    {input : Provenance.Proof} {output : SourceProof.Proof}
    {fact : Term} {claim : SourceProof.Claim}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db)
    (hC : SourceProof.contextOf P = some C)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P C fact = some claim) (h : lift P input = some output) :
    claim.Supported db :=
  SourceProof.check_supported hs hw hclosed (lift_checked hC hf hc h)

theorem lift_sound {P : Program} {C : SourceProof.Context} {db : Database}
    {input : Provenance.Proof} {output : SourceProof.Proof}
    {fact : Term} {claim : SourceProof.Claim}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db)
    (hC : SourceProof.contextOf P = some C)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P C fact = some claim) (h : lift P input = some output)
    (hl : claim.lhs ∈ db.terms) (hr : claim.rhs ∈ db.terms) :
    Cong db claim.lhs claim.rhs :=
  (lift_supported hs hw hclosed hC hf hc h).holds hw hl hr

/-- Lifted claims have represented existence, even for spellings absent from the store. -/
theorem lift_infers {P : Program} {C : SourceProof.Context} {db : Database}
    {input : Provenance.Proof} {output : SourceProof.Proof}
    {fact : Term} {claim : SourceProof.Claim}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db)
    (hC : SourceProof.contextOf P = some C)
    (hf : Provenance.check (Congruence.encode P) input = some fact)
    (hc : factClaim P C fact = some claim) (h : lift P input = some output) :
    db.Infers claim.lhs claim.rhs :=
  (lift_supported hs hw hclosed hC hf hc h).infers hw

/-- An extracted source proof certifies the row's data columns. -/
theorem extractRow_checked {P : Program} {C target : SourceProof.Context}
    {row : Entry} {decl : FnDecl} {output : SourceProof.Proof} {claim : SourceProof.Claim}
    (hC : SourceProof.contextOf P = some C)
    (hT : SourceProof.contextOf (Congruence.encode P) = some target)
    (hd : target.sig row.name = some decl)
    (hm : factClaim P C (.app row.name (row.key ++ row.value.take decl.outArity)) =
      some claim)
    (h : extractRow P row = some output) : SourceProof.check P output = some claim := by
  obtain ⟨input, hi, hl⟩ := Option.bind_eq_some_iff.mp h
  exact lift_checked hC (Provenance.extractRow_checked hT hd hi) hm hl

/-- Extraction followed by lifting establishes the corresponding source equality. -/
theorem extractRow_infers {P : Program} {C target : SourceProof.Context} {db : Database}
    {row : Entry} {decl : FnDecl} {output : SourceProof.Proof} {claim : SourceProof.Claim}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db)
    (hC : SourceProof.contextOf P = some C)
    (hT : SourceProof.contextOf (Congruence.encode P) = some target)
    (hd : target.sig row.name = some decl)
    (hm : factClaim P C (.app row.name (row.key ++ row.value.take decl.outArity)) =
      some claim)
    (h : extractRow P row = some output) : db.Infers claim.lhs claim.rhs :=
  SourceProof.check_infers hs hw hclosed (extractRow_checked hC hT hd hm h)

end Egglog.Resugar
