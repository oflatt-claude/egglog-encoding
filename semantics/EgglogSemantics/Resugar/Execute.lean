import EgglogSemantics.Resugar.Lift
import EgglogSemantics.Impl.Interp

namespace Egglog.Resugar

open SourceProof (Proof)

/-- Run the instrumented compilation of `P` with `exec` and lift every retained row. -/
def certificates (exec : Program → Option FDatabase) (P : Program) :
    Option (List Proof) := do
  let target := Congruence.encode P
  let C ← SourceProof.contextOf target
  let annotated ← Provenance.encode target
  let d ← exec annotated
  (Provenance.retainedRows C.sig d.terms).mapM (extractRow P ·)

end Egglog.Resugar
