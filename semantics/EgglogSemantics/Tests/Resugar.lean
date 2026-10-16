import EgglogSemantics.Resugar.Fixtures
import EgglogSemantics.Proofs.Resugar.Soundness

namespace Egglog.Resugar.Tests

open Fixtures
open SourceProof (Proof)

set_option linter.hashCommand false

private def term (f : FnName) : Term := .app f []
private def initial (t : Term) : Proof := .rule ⟨t, t⟩ 4 [] []

def certificates (P : Program) : Option (List Proof) :=
  Resugar.certificates (Relational.execProgram FDatabase.empty) P

private def sourceNames (pf : Proof) : Bool := pf.nodes.all fun n =>
  (n.claim.lhs.toExpr.fns ++ n.claim.rhs.toExpr.fns).all fun f => !"@".isPrefixOf f

def validates (P : Program) : Bool := (certificates P).any fun cs =>
  cs.all fun c => (SourceProof.check P c).isSome && sourceNames c

#guard lifted.all fun np => validates np.2
#guard (certificates nestedUnion).any fun cs => cs.any fun c => c.nodes.any fun n =>
  match n with | .congr _ _ _ _ => true | _ => false
#guard (certificates ruleChain).any fun cs => cs.any fun c => c.nodes.any fun n =>
  match n with | .rule _ 3 [] [] => true | _ => false
#guard (certificates missingPremise).any fun cs => cs.all fun c =>
  SourceProof.check missingPremise c != some (⟨term "A", term "B"⟩ : SourceProof.Claim)
#guard let command := (((Congruence.compile missingPremise).zipIdx.find? fun ci =>
  decide (ci.1.ruleOrigin = some (.source 3))).map Prod.snd).getD 0
  (lift missingPremise
    (.rule (.app (viewName "Missing") [term "Missing"]) command [] [])).isNone

-- The hand-written fixtures have the verdicts their names promise.
#guard accepted.all fun f => f.certificates.all fun c => (SourceProof.check f.program c).isSome
#guard rejected.all fun f => f.certificates.all fun c => (SourceProof.check f.program c).isNone
#guard (Fixtures.all).any fun fs => fs.length == lifted.length + accepted.length + rejected.length

-- A transformed enclosing term's child still needs the derivation that introduced it.
private def supportProof : Proof :=
  .congr ⟨.app "F" [term "A"], .app "F" [.app "G" [term "B"]]⟩ (initial (.app "F" [term "A"])) 0
    (.rule ⟨term "A", .app "G" [term "B"]⟩ 6 [] [])

#guard (SourceProof.contextOf supportCase).any fun C =>
  (support supportCase C (term "B") supportProof).any fun result =>
    SourceProof.check supportCase result ==
      some (⟨term "B", term "B"⟩ : SourceProof.Claim)
#guard (SourceProof.contextOf supportCase).any fun C =>
  (support supportCase C (term "Missing") supportProof).isNone

end Egglog.Resugar.Tests
