import EgglogSemantics.Resugar.Fixtures
import EgglogSemantics.Resugar.Soundness

namespace Egglog.Resugar.Tests

open Fixtures

set_option linter.hashCommand false

private def term (f : FnName) : Term := .app f []

def certificates (P : Program) : Option (List SourceProof.Certificate) :=
  Resugar.certificates (Relational.execProgram FDatabase.empty) P

private def sourceNames (c : SourceProof.Certificate) : Bool := c.nodes.all fun n =>
  (n.claim.lhs.toExpr.fns ++ n.claim.rhs.toExpr.fns).all fun f => !"@".isPrefixOf f

def validates (P : Program) : Bool := (certificates P).any fun cs =>
  cs.all fun c => (SourceProof.check P c).isSome && sourceNames c

#guard lifted.all fun np => validates np.2
#guard (certificates nestedUnion).any fun cs => cs.any fun c => c.nodes.any fun n =>
  match n.reason with | .congr _ _ _ => true | _ => false
#guard (certificates ruleChain).any fun cs => cs.all fun c => c.nodes.all fun n =>
  match n.reason with | .fiat => false | _ => true
#guard (certificates missingPremise).any fun cs => cs.all fun c =>
  SourceProof.check missingPremise c != some (⟨term "A", term "B"⟩ : SourceProof.Claim)
#guard (lift missingPremise ⟨[⟨.app (viewName "Missing") [term "Missing"], .global 0⟩], 0⟩).isNone
#guard (lift ruleChain ⟨[], 0⟩).isNone

-- The hand-written fixtures have the verdicts their names promise.
#guard accepted.all fun f => f.certificates.all fun c => (SourceProof.check f.program c).isSome
#guard rejected.all fun f => f.certificates.all fun c => (SourceProof.check f.program c).isNone
#guard (Fixtures.all).any fun fs => fs.length == lifted.length + accepted.length + rejected.length

-- A transformed enclosing term's child still needs the derivation that introduced it.
private def supportProof : Builder := ⟨[
  ⟨⟨.app "F" [term "A"], .app "F" [term "A"]⟩, .fiat⟩,
  ⟨⟨term "A", .app "G" [term "B"]⟩, .rule 5 [] []⟩,
  ⟨⟨.app "F" [term "A"], .app "F" [.app "G" [term "B"]]⟩, .congr 0 0 1⟩]⟩

#guard (SourceProof.contextOf supportCase).any fun C =>
  (support supportCase C 4 supportProof 2 (term "B")).any fun result =>
    SourceProof.check supportCase ⟨result.2.nodes, result.1⟩ ==
      some (⟨term "B", term "B"⟩ : SourceProof.Claim)
#guard (SourceProof.contextOf supportCase).any fun C =>
  (support supportCase C 4 supportProof 2 (term "Missing")).isNone

end Egglog.Resugar.Tests
