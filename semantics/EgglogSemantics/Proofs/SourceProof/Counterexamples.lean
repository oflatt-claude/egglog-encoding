import EgglogSemantics.Proofs.SourceProof.Support
import EgglogSemantics.Impl.Merge

namespace Egglog.SourceProof.Counterexamples

set_option linter.hashCommand false

private def ctor : FnDecl := ⟨0, 1, none, none⟩
private def a : Term := .app "A" []
private def b : Term := .app "B" []
private def c : Term := .app "C" []
private def row (x : Term) : Term := .app "Table" [x]
private def body : List Action := [.union (.var "old") c.toExpr]

private def program : Program :=
  [.decl "A" ctor, .decl "B" ctor, .decl "C" ctor,
   .decl "Table" ⟨0, 1, some (.merge body [.var "old"]), none⟩,
   .action (.expr (row a).toExpr), .action (.union a.toExpr b.toExpr),
   .action (.expr c.toExpr), .saturate "R"]

-- The original program has one row and does not run the merge body.
#guard (execM program).any fun d =>
  decide (a ∈ d.terms ∧ c ∈ d.terms ∧ (a, c) ∉ d.closureF ∧ row b ∉ d.terms)

-- Both anchors are genuine globals.
#guard (contextOf program).any fun C =>
  decide ((⟨row a, row a⟩ : Claim) ∈ C.globals ∧ (⟨a, b⟩ : Claim) ∈ C.globals)

-- Running the merge body at two row spellings would assert the unsupported equality.
#guard (contextOf program).any fun C =>
  (actionsFacts C.sig (mergeEnv [a] [b]) body).any fun fs =>
    decide ((⟨a, c⟩ : Claim) ∈ fs)

/-- Congruence establishes the second spelling without establishing a collision. -/
private theorem second_spelling {db : Database} (hw : db.WF)
    (hrow : Cong db (row a) (row a)) (hab : Cong db a b) :
    Claim.Supported db ⟨row b, row b⟩ := by
  have base := Claim.Holds.supported (c := ⟨row a, row a⟩) hw hrow
  have child := Claim.Holds.supported (c := ⟨a, b⟩) hw hab
  have rewritten := base.congr (i := 0) child rfl
  exact rewritten.symm.trans rewritten

end Egglog.SourceProof.Counterexamples
