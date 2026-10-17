import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Proofs.Provenance.Countermodel

namespace Egglog.Provenance.Counterexamples

set_option linter.hashCommand false

private def row (n : Int) : Term := .app "T" [.lit (.int n)]
private def write (n : Int) : Cmd := .rule ⟨[], [.expr (row n).toExpr], "init"⟩
private def constant : Program :=
  [.decl "T" ⟨0, 1, some (.merge ["old"] ["new"] [] [.lit (.int 9)])⟩,
   write 1, .run "init", .saturate "R"]
private def original : Proof := .rule (row 1) 1 [] []

-- A self-merge cannot justify a new row.
#guard check constant (.merge (row 9) "T" original original) == none

private def replacement : Program :=
  [.decl "T" ⟨0, 1, some (.merge ["old"] ["new"]
    [] [.min (.var "old") (.var "new")])⟩,
   write 2, write 1, .run "init", .saturate "R"]

-- Acceptance alone does not assert that a certified row is still live.
#guard check replacement (.rule (row 2) 1 [] []) == some (row 2)

end Egglog.Provenance.Counterexamples
