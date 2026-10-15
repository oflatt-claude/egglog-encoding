import EgglogSemantics.Provenance.Encode

namespace Egglog.Provenance

/-- A generated merge runs only when its data inputs differ. Proof columns alone
cannot trigger a new merge certificate. -/
theorem encodedMerge_data_distinct {f : FnName} {d : FnDecl}
    {oldVars newVars : List Var} {body : List Action} {res : List Expr}
    (hm : d.merge = some (.merge oldVars newVars body res))
    {old new : List Term} {oldProof newProof : Term} {encodedBody : List Action}
    (hlen : old.length = d.outArity)
    (hconf : MergeConflict (encodeDecl f d) encodedBody
      (old ++ [oldProof]) (new ++ [newProof])) : old ≠ new := by
  intro heq
  subst new
  have hk : min ((d.unchangedWidth body).getD d.outArity) d.outArity ≤ old.length := by
    rw [hlen]
    exact Nat.min_le_right _ _
  simp only [MergeConflict, encodeDecl, hm, FnDecl.unchangedWidth] at hconf
  change (old ++ [oldProof]).take
    (min ((d.unchangedWidth body).getD d.outArity) d.outArity) ≠
    (old ++ [newProof]).take
      (min ((d.unchangedWidth body).getD d.outArity) d.outArity) at hconf
  exact hconf (by rw [List.take_append_of_le_length hk, List.take_append_of_le_length hk])

end Egglog.Provenance
