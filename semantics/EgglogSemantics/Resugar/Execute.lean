import EgglogSemantics.Resugar.Lift
import EgglogSemantics.Impl.Interp
import EgglogSemantics.Congruence.Relational

namespace Egglog.Resugar

open SourceProof (Proof)

/-- Run the instrumented compilation of `P` with `exec` and lift a proof of every row. -/
def certificates (exec : Program → Option FDatabase) (P : Program) :
    Option (List Proof) := do
  let annotated ← Provenance.encode (Congruence.encode P)
  let d ← exec annotated
  sourceProofs P d.terms

/-- A checked source proof of every conjunct of the final check. The compiled check is
matched against the final state, the lifted proof of each compiled premise is looked up
among the certificates, and the source check is rebuilt from them exactly as a rule's
premises are (`query`). A side of the check need not be built as a node: it is matched up
to congruence, and the rebuilt proof carries that congruence. -/
def checkProofs (exec : Program → Option FDatabase) (P : Program) : Option (List Proof) := do
  let compiled := Congruence.compile P
  let annotated ← Provenance.encode compiled.program
  let d ← exec annotated
  let certs ← sourceProofs P d.terms
  let σ ← (Relational.matchQuery d.forgetSubsumed compiled.program.check).head?
  let premises ← compiled.program.check.mapM fun p => do
    let t ← match p with
      | .expr e => e.eval σ
      | .eq a b => do
        let x ← a.eval σ
        let y ← b.eval σ
        if x == y then some x else none
      | .ne _ _ => none
    let c ← factClaim P t
    certs.find? (·.claim == c)
  let pfs ← query P P.check premises
  if pfs.all (fun pf => SourceProof.check P pf == some pf.claim) then some pfs else none

end Egglog.Resugar
