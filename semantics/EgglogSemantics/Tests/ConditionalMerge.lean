import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Spec.Sequential

namespace Egglog.Tests.ConditionalMerge

private def value (n : Int) : Term := .lit (.int n)
private def expr (n : Int) : Expr := .lit (.int n)

private def inputs (second : Int) : Database :=
  { Database.empty with env :=
      [("old0", value 0), ("old1", value 1), ("new0", value 0), ("new1", value second),
       (Provenance.proofVar 0, value 10), (Provenance.proofVar 1, value 20)] }
    |>.addTerm (value 10)

private def body : List Action :=
  Provenance.encodeMergeBody "T" ["old0", "old1"] ["new0", "new1"]
    [.expr (.var "unbound")]
private def result : List Expr :=
  Provenance.encodeMergeResult "T" ["old0", "old1"] ["new0", "new1"]
    [.var "new0", .var "new1"]

-- Proofs may differ: equal data reasserts its existing proof and avoids the failing branch.
example : evalMerge (inputs 1) body result =
    some (inputs 1, [value 0, value 1, value 10]) := by
  change some ((inputs 1).addTerm (value 10), [value 0, value 1, value 10]) = _
  simp [inputs, Database.addTerm]

-- Every data column participates in the guard.
example : evalMerge (inputs 2) body result = none := rfl

-- Only the chosen result enters the store, including its subterms.
example : evalAction Database.empty (.expr (.ite [] [] (expr 9) (.var "unbound"))) =
    some (Database.empty.addTerm (value 9)) := rfl

private def tables : Database :=
  { Database.empty with
    sig := fun _ => some ⟨0, 1, some (.merge ["old"] ["new"] [] [.var "old"])⟩ }

-- A conditional can select a complete function row.
example : evalAction tables
    (.expr (.ite [] [] (.app "T" [expr 9]) (.app "T" [expr 8]))) =
    some (tables.addTerm (.app "T" [value 9])) := rfl

-- Selecting an atom does not allow function calls inside a row's columns.
example : evalAction tables (.expr (.app "T" [.ite [] [] (.app "T" [expr 9]) (expr 8)])) =
    none := rfl

private def congruent : Database :=
  { Database.empty with sig := fun _ => some ⟨0, 1, none⟩ }
    |>.addEq (.app "a" []) (.app "b" [])

example : Cong congruent (.app "a" []) (.app "b" []) :=
  .direct (Set.mem_insert _ _)

-- Congruence does not change a structural equality test.
example : Expr.eval congruent.sig
    (.ite [.app "a" []] [.app "b" []] (expr 1) (expr 2)) [] = some (value 2) := rfl

end Egglog.Tests.ConditionalMerge
