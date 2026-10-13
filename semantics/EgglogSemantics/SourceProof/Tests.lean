import EgglogSemantics.SourceProof.Soundness

namespace Egglog.SourceProof.Tests

set_option linter.hashCommand false

private def ctor (arity : Nat) : FnDecl := ⟨arity, 1, none, none⟩
private def a : Term := .app "A" []
private def b : Term := .app "B" []
private def missing : Term := .app "Missing" []
private def fa : Term := .app "F" [a]
private def fb : Term := .app "F" [b]
private def ga : Term := .app "G" [a]

private def declarations : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "Missing" (ctor 0),
   .decl "F" (ctor 1), .decl "G" (ctor 1)]

private def globals : Program := declarations ++
  [.action (.expr fa.toExpr), .action (.union a.toExpr b.toExpr)]

private def fiat (x : Term) : Node := ⟨⟨x, x⟩, .fiat⟩
private def accepts (P : Program) (ns : List Node) (c : Claim) : Bool :=
  check P ⟨ns, ns.length - 1⟩ == some c

#guard accepts globals [fiat a] ⟨a, a⟩
#guard accepts globals [⟨⟨b, a⟩, .fiat⟩] ⟨b, a⟩
#guard !(check globals ⟨[fiat missing], 0⟩).isSome
#guard !(check globals ⟨[fiat fb], 0⟩).isSome
#guard !(check declarations ⟨[fiat (.lit (.int 3))], 0⟩).isSome

private def childRewrite : List Node :=
  [fiat fa, ⟨⟨a, b⟩, .fiat⟩, ⟨⟨fa, fb⟩, .congr 0 0 1⟩,
   ⟨⟨fb, fa⟩, .symm 2⟩, ⟨⟨fb, fb⟩, .trans 3 2⟩]

#guard accepts globals childRewrite ⟨fb, fb⟩
#guard !(check globals ⟨[⟨⟨a, a⟩, .symm 0⟩], 0⟩).isSome
#guard !(check globals ⟨[⟨⟨a, a⟩, .symm 1⟩, fiat a], 0⟩).isSome
#guard !(check globals ⟨[fiat a], 1⟩).isSome
#guard !(check globals ⟨[fiat a, fiat missing], 0⟩).isSome
#guard !(check globals ⟨[fiat fa, ⟨⟨a, b⟩, .fiat⟩,
  ⟨⟨fa, fb⟩, .congr 0 1 1⟩], 2⟩).isSome
#guard !(check globals ⟨[fiat fa, ⟨⟨b, a⟩, .fiat⟩,
  ⟨⟨fa, fb⟩, .congr 0 0 1⟩], 2⟩).isSome
#guard !(check globals ⟨[fiat a, fiat b, ⟨⟨a, b⟩, .trans 0 1⟩], 2⟩).isSome

private def create : Rule :=
  ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])], "R"⟩
private def program : Program := globals ++ [.rule create, .saturate "R"]
private def creation : Node := ⟨⟨ga, ga⟩, .rule 7 [("x", a)] [0]⟩

#guard accepts program [fiat fa, creation] ⟨ga, ga⟩
#guard !(check program ⟨[fiat ga], 0⟩).isSome
#guard !(check program ⟨[fiat a, creation], 1⟩).isSome
#guard !(check program ⟨[fiat fa, ⟨⟨ga, ga⟩, .rule 0 [("x", a)] [0]⟩], 1⟩).isSome
#guard !(check program ⟨[fiat fa, ⟨⟨ga, ga⟩, .rule 7 [] [0]⟩], 1⟩).isSome
#guard !(check program ⟨[fiat fa,
  ⟨⟨ga, ga⟩, .rule 7 [("x", a), ("x", a)] [0]⟩], 1⟩).isSome
#guard !(check program ⟨[fiat fa,
  ⟨⟨ga, ga⟩, .rule 7 [("x", a), ("unused", b)] [0]⟩], 1⟩).isSome
#guard !(check program ⟨[fiat fa, ⟨⟨a, b⟩, .rule 7 [("x", a)] [0]⟩], 1⟩).isSome
#guard !(check program ⟨[fiat fa, ⟨⟨ga, ga⟩, .rule 7 [("x", a)] []⟩], 1⟩).isSome
#guard !(check program ⟨[fiat fa, ⟨⟨ga, ga⟩, .rule 7 [("x", a)] [0, 0]⟩], 1⟩).isSome

private def absentPremise : Program := declarations ++
  [.action (.expr a.toExpr), .action (.expr b.toExpr),
   .rule ⟨[.expr missing.toExpr], [.union a.toExpr b.toExpr], "R"⟩]

#guard !(check absentPremise ⟨[fiat missing,
  ⟨⟨a, b⟩, .rule 7 [] [0]⟩], 1⟩).isSome

#guard accepts (absentPremise ++ [.action (.expr missing.toExpr)])
  [fiat missing, ⟨⟨a, b⟩, .rule 7 [] [0]⟩] ⟨a, b⟩

private def gb : Term := .app "G" [b]

-- An expression premise may be anchored at another congruent term.
#guard accepts program (childRewrite ++
  [⟨⟨gb, gb⟩, .rule 7 [("x", b)] [2]⟩]) ⟨gb, gb⟩

private def ordered : Program := globals ++
  [.rule ⟨[.expr (.app "F" [.var "x"]), .eq (.var "x") b.toExpr],
    [.expr (.app "G" [.var "x"])], "R"⟩]

#guard accepts ordered [fiat fa, ⟨⟨a, b⟩, .fiat⟩,
  ⟨⟨ga, ga⟩, .rule 7 [("x", a)] [0, 1]⟩] ⟨ga, ga⟩
#guard !(check ordered ⟨[fiat fa, ⟨⟨a, b⟩, .fiat⟩,
  ⟨⟨ga, ga⟩, .rule 7 [("x", a)] [1, 0]⟩], 2⟩).isSome

private def unconditional : Program := declarations ++
  [.rule ⟨[], [.expr missing.toExpr], "R"⟩]

#guard accepts unconditional [⟨⟨missing, missing⟩, .rule 5 [] []⟩] ⟨missing, missing⟩
#guard !(check unconditional ⟨[fiat missing], 0⟩).isSome

private def nested : Program := declarations ++
  [.action (.expr (.app "F" [fa.toExpr])),
   .rule ⟨[.expr (.app "F" [.app "F" [.var "x"]])],
     [.expr (.app "G" [.var "x"])], "R"⟩]

-- One premise for the original nested query, with no flattening in the checker.
#guard accepts nested [fiat (.app "F" [fa]),
  ⟨⟨ga, ga⟩, .rule 6 [("x", a)] [0]⟩] ⟨ga, ga⟩

private def functions : Program := declarations ++
  [.decl "Table" ⟨0, 1, some (.merge [] [.var "old"]), none⟩,
   .action (.expr (.app "Table" [a.toExpr]))]

#guard !sourceOk functions
#guard !(check functions ⟨[fiat (.app "Table" [a])], 0⟩).isSome
#guard !sourceOk (declarations ++
  [.rule ⟨[.expr (.app "ordering-gt" [.var "x", .var "y"])], [], "R"⟩])
-- A bare variable or literal is not a query fact, as in egglog.
#guard !sourceOk (declarations ++ [.rule ⟨[.expr (.var "x")], [], "R"⟩])
#guard !sourceOk (declarations ++ [.rule ⟨[.expr (.lit (.int 3))], [], "R"⟩])
#guard (contextOf (globals ++ [.decl "A" (ctor 0)])).isNone
#guard (contextOf (declarations ++ [.action (.expr (.var "unbound"))])).isNone

end Egglog.SourceProof.Tests
