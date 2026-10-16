import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Congruence.Encode

namespace Egglog.Resugar

open SourceProof (Claim Context)

/-- A view relates its id to its constructor application; UF records an equality. -/
def factClaim (P : Program) (C : Context) (t : Term) : Option Claim := do
  if SourceProof.valueOk C.sig t then some ⟨t, t⟩ else do
    let .app f cols := t | none
    match Congruence.tableRole P f with
    | some .unionFind =>
      let [a, b] := cols | none
      some ⟨a, b⟩
    | some (.view ctor) => do
      let d ← C.sig ctor
      if cols.length != d.arity + 1 then none else do
        let id ← cols[d.arity]?
        some ⟨id, .app ctor (cols.take d.arity)⟩
    | none => none

end Egglog.Resugar
