import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Proofs.Provenance.Countermodel

namespace Egglog.Provenance.Counterexamples

set_option linter.hashCommand false

private def row (n : Int) : Term := .app "T" [.lit (.int n)]
private def write (n : Int) : Cmd := .action (.expr (row n).toExpr)
private def constant : Program :=
  [.decl "T" ⟨0, 1, some (.merge ["old"] ["new"] [] [.lit (.int 9)]), none⟩,
   write 1, .saturate "R"]
private def original : Proof := .global (row 1) 1

-- One row does not collide with itself, even with a non-idempotent merge expression.
#guard (execM constant).any fun d => decide (row 1 ∈ d.terms ∧ row 9 ∉ d.terms)

-- The checker nevertheless accepts a merge of that single row with itself.
#guard check constant (.merge (row 9) "T" original original) == some (row 9)

private def replacement : Program :=
  [.decl "T" ⟨0, 1, some (.merge ["old"] ["new"] []
    [.min (.var "old") (.var "new")]), none⟩,
   write 2, write 1, .saturate "R"]

-- A global certificate remains accepted after its live entry has been replaced.
#guard check replacement (.global (row 2) 1) == some (row 2)
#guard (execM replacement).any fun d =>
  decide ((⟨"T", [], [.lit (.int 1)]⟩ : Row) ∈ d.rows ∧
    (⟨"T", [], [.lit (.int 2)]⟩ : Row) ∉ d.rows)

end Egglog.Provenance.Counterexamples
