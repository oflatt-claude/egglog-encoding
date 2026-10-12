import EgglogSemantics.Congruence.Correspond
import EgglogSemantics.Congruence.Flatten

/-! Executable regressions for rebuilding, existence, and ordered query flattening. -/

namespace Egglog.Congruence

set_option linter.hashCommand false

private def atom (f : FnName) : Expr := .app f []
private def term (f : FnName) : Term := .app f []

private def nestedUnion : Program :=
  [.decl "A" (skolemDecl 0), .decl "B" (skolemDecl 0), .decl "F" (skolemDecl 1),
   .action (.expr (.app "F" [atom "A"])), .action (.expr (.app "F" [atom "B"])),
   .action (.union (atom "A") (atom "B"))]

private def runSameClass (P : Program) (a b : Term) : Bool :=
  (execM P).any fun d => sameClassF d a b

-- Child re-keying and the view collision must make the parents equal.
#guard runSameClass (encode nestedUnion) (.app "F" [term "A"]) (.app "F" [term "B"])

-- This would pass vacuously if the reader ignored the rebuild: removing the schedule
-- must lose the parent equality. The source has no run that could fire maintenance.
#guard !(runSameClass ((encode nestedUnion).filter fun c => match c with
    | .saturate _ => false | _ => true) (.app "F" [term "A"]) (.app "F" [term "B"]))

private def missingPremise : Program :=
  [.decl "A" (skolemDecl 0), .decl "B" (skolemDecl 0), .decl "Missing" (skolemDecl 0),
   .action (.expr (atom "A")), .action (.expr (atom "B")),
   .rule ⟨[.expr (atom "Missing")], [.union (atom "A") (atom "B")], "R"⟩,
   .saturate "R"]

-- Declaration is not existence. An absent premise cannot justify this union.
#guard (execM (encode missingPremise)).isSome
#guard !(runSameClass (encode missingPremise) (term "A") (term "B"))
#guard !(runSameClass (encode missingPremise) (term "Missing") (term "Missing"))

private def orderedQuery : Query :=
  [.eq (.app "F" [.app "G" [.var "x"], .app "G" [.var "x"]])
       (.app "H" [.app "G" [.var "x"]])]

-- Repeated subexpressions are separate occurrences, visited children-first and
-- left-to-right on both sides. These are the positions resugaring will consume.
example : encodeQuery orderedQuery 0 =
  ([.expr (.app (viewName "G") [.var "x", .var "@v0"]),
    .expr (.app (viewName "G") [.var "x", .var "@v1"]),
    .expr (.app (viewName "F") [.var "@v0", .var "@v1", .var "@v2"]),
    .expr (.app (viewName "G") [.var "x", .var "@v3"]),
    .expr (.app (viewName "H") [.var "@v3", .var "@v4"]),
    .eq (.var "@v2") (.var "@v4")], 5) := rfl

-- Source tags are original command positions, even though declarations and builds expand.
#guard ((compile missingPremise).filterMap (·.ruleOrigin)).contains (.source 5)
#guard ((allMaintenanceRules missingPremise).filterMap (·.ruleOrigin)).count
  (.rebuild .compress) == 2
#guard ((rebuildRules "F" 2).filterMap (·.ruleOrigin)) ==
  [.rebuild (.eclass "F"), .rebuild (.child "F" 0), .rebuild (.child "F" 1)]
#guard tableRole nestedUnion ufName == some .unionFind
#guard tableRole nestedUnion (viewName "F") == some (.view "F")
#guard tableRole nestedUnion "F" == none

-- No proof declaration or history relation is emitted, and tables have one value column.
#guard (encode nestedUnion).all fun c => match c with
  | .decl f d => d.outArity == 1 && (f == ufName ||
      nestedUnion.ctors.any fun fk => f == fk.1 || f == viewName fk.1)
  | _ => true

end Egglog.Congruence
