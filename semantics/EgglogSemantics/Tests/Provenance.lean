import EgglogSemantics.Provenance.Extract
import EgglogSemantics.Proofs.Provenance.Soundness
import EgglogSemantics.Congruence.Relational

namespace Egglog.Provenance.Tests

set_option linter.hashCommand false

private def atom (f : FnName) : Expr := .app f []
private def term (f : FnName) : Term := .app f []
private def int (n : Int) : Expr := .lit (.int n)

/-- Check data preservation and every live function row's extracted certificate. -/
def validates (P : Program) : Bool := (do
  let C ← SourceProof.contextOf P
  let encoded ← encode P
  let original ← Relational.execProgram FDatabase.empty P
  let annotated ← Relational.execProgram FDatabase.empty encoded
  let rows := annotated.rows.filterMap (eraseRow C.sig)
  let proofs := retainedRows C.sig annotated.terms
  some (unionFree encoded && decide (rows.toFinset = original.rows.toFinset) &&
    decide ((annotated.terms.filterMap (eraseFact C.sig)).toFinset = original.terms.toFinset) &&
    proofs.all fun r => (extractRow P r).isSome)).getD false

private def nestedUnion : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "F" (ctor 1),
   .action (.expr (.app "F" [atom "A"])), .action (.expr (.app "F" [atom "B"])),
   .action (.union (atom "A") (atom "B"))]

#guard validates (Congruence.encode nestedUnion)

private def equalityRule : Program :=
  [.decl "A" (ctor 0), .decl "F" (ctor 1), .decl "G" (ctor 1),
   .action (.expr (.app "F" [atom "A"])),
   .rule ⟨[.eq (.app "F" [.var "x"]) (.app "F" [.var "x"])],
     [.expr (.app "G" [.var "x"])], "R"⟩,
   .saturate "R"]

#guard validates (Congruence.encode equalityRule)

private def emptyQuery : Program :=
  [.decl "A" (ctor 0), .rule ⟨[], [.expr (atom "A")], "R"⟩, .saturate "R"]

#guard validates (Congruence.encode emptyQuery)

private def missingPremise : Program :=
  [.decl "A" (ctor 0), .decl "Missing" (ctor 0),
   .rule ⟨[.expr (atom "Missing")], [.expr (atom "A")], "R"⟩, .saturate "R"]

#guard validates (Congruence.encode missingPremise)

private def tables : Program :=
  [.decl "Key" (ctor 0),
   .decl "Audit" ⟨2, 1, some (.merge [] [.var "old"]), none⟩,
   .decl "Bounds" ⟨1, 2, some (.merge
     [.expr (.app "Audit" [.var "old0", .var "new0", .var "new1"])]
     [.app "min" [.var "old0", .var "new0"],
      .app "max" [.var "old1", .var "new1"]]), none⟩,
   .action (.expr (.app "Bounds" [atom "Key", int 2, int 3])),
   .action (.expr (.app "Bounds" [atom "Key", int 4, int 6]))]

#guard validates tables

-- Metadata-only collisions must not execute an otherwise unconditional merge.
private def sameData : Program :=
  [.decl "T" ⟨0, 1, some (.merge [] [.app "max" [.var "old", int 9]]), none⟩,
   .action (.expr (.app "T" [int 1])), .action (.expr (.app "T" [int 1]))]

#guard validates sameData

private def zeroOutputs : Program :=
  [.decl "T" ⟨1, 0, some (.merge [] []), none⟩,
   .action (.expr (.app "T" [int 1])), .action (.expr (.app "T" [int 1]))]

#guard validates zeroOutputs

private def partialIdentity : Program :=
  [.decl "T" ⟨0, 2, some (.merge [] [.var "new0", .var "new1"]), some 1⟩,
   .action (.expr (.app "T" [int 1, int 2])),
   .action (.expr (.app "T" [int 1, int 3]))]

#guard validates partialIdentity

private def bounds (a b : Int) : Term :=
  .app "Bounds" [term "Key", .lit (.int a), .lit (.int b)]

private def old : Proof := .global (bounds 2 3) 3
private def new : Proof := .global (bounds 4 6) 4

#guard (check tables (.merge (bounds 2 6) "Bounds" old new)).isSome
#guard (check tables
  (.merge (.app "Audit" [.lit (.int 2), .lit (.int 4), .lit (.int 6)]) "Bounds" old new)).isSome
#guard (check tables (.merge (bounds 4 3) "Bounds" old new)).isNone
#guard (check tables (.merge (bounds 2 6) "Audit" old new)).isNone
#guard (check tables (.merge (bounds 2 6) "Bounds" old old)).isNone

private def distinctKeys : Program :=
  [.decl "T" ⟨1, 1, some (.merge [] [.var "new"]), none⟩,
   .action (.expr (.app "T" [int 1, int 3])),
   .action (.expr (.app "T" [int 2, int 4]))]

#guard (check distinctKeys (.merge (.app "T" [.lit (.int 1), .lit (.int 4)]) "T"
  (.global (.app "T" [.lit (.int 1), .lit (.int 3)]) 1)
  (.global (.app "T" [.lit (.int 2), .lit (.int 4)]) 2))).isNone

private def table (n : Int) : Term := .app "T" [.lit (.int n)]
private def tProgram : Program :=
  [.decl "T" ⟨0, 1, some (.merge [] [.app "min" [.var "old", .var "new"]]), none⟩,
   .action (.expr (.app "T" [int 3])),
   .rule ⟨[.expr (.app "T" [.var "x"])], [.expr (.app "T" [int 2])], "R"⟩,
   .saturate "R"]
private def stored : Proof := .global (table 3) 1

#guard validates tProgram
#guard check tProgram stored == some (table 3)
#guard (check tProgram (.global (table 2) 1)).isNone
#guard (check tProgram (.global (table 2) 2)).isNone
#guard (check tProgram (.subterm (table 2) stored)).isNone
-- Every node is checked, not only the root.
#guard (check tProgram (.subterm (table 3) (.global (table 2) 1))).isNone
#guard (check tProgram (.rule (table 2) 2 [("x", .lit (.int 3))] [stored])).isSome
#guard (check tProgram (.rule (table 2) 2 [("x", .lit (.int 2))] [stored])).isNone
#guard (check tProgram (.rule (table 2) 2 [] [stored])).isNone
#guard (check tProgram (.rule (table 2) 2 [("x", .lit (.int 3))] [])).isNone
#guard (extract tProgram (.app (globalName 2) [])).isNone
#guard (extract tProgram (.app (globalName 1) [term "Missing"])).isNone
#guard (extract tProgram (.app subtermName [table 2, .app (globalName 1) []])).isNone
#guard (extractRow tProgram ⟨"T", [], [.lit (.int 2), .app (globalName 1) []]⟩).isNone

-- Equality-only variables have no table evidence and are outside this pass's input fragment.
#guard (encode [.rule ⟨[.eq (.var "x") (.var "x")], [], "R"⟩]).isNone
#guard (encode [.decl (namePrefix ++ "user") (ctor 0)]).isNone
#guard (encode [.decl "T" ⟨0, 1, some .noMerge, none⟩]).isNone
#guard (encode nestedUnion).isNone

end Egglog.Provenance.Tests
