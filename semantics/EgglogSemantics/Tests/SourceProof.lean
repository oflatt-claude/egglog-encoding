import EgglogSemantics.Proofs.SourceProof.Soundness

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

private def fiat (x : Term) : Proof := .fiat ⟨x, x⟩
private def accepts (P : Program) (pf : Proof) (c : Claim) : Bool := check P pf == some c
private def rejects (P : Program) (pf : Proof) : Bool := (check P pf).isNone

#guard accepts globals (fiat a) ⟨a, a⟩
#guard accepts globals (.fiat ⟨b, a⟩) ⟨b, a⟩
#guard rejects globals (fiat missing)
#guard rejects globals (fiat fb)
#guard rejects declarations (fiat (.lit (.int 3)))

private def rewrite : Proof := .congr ⟨fa, fb⟩ (fiat fa) 0 (.fiat ⟨a, b⟩)
private def childRewrite : Proof := .trans ⟨fb, fb⟩ (.symm ⟨fb, fa⟩ rewrite) rewrite

#guard accepts globals childRewrite ⟨fb, fb⟩
#guard rejects globals (.symm ⟨a, a⟩ (fiat fa))
#guard rejects globals (.congr ⟨fa, fb⟩ (fiat fa) 1 (.fiat ⟨a, b⟩))
#guard rejects globals (.congr ⟨fa, fb⟩ (fiat fa) 0 (.fiat ⟨b, a⟩))
#guard rejects globals (.trans ⟨a, b⟩ (fiat a) (fiat b))
-- Every node is checked, not only the root.
#guard rejects globals (.trans ⟨fb, fb⟩ (.symm ⟨fb, fa⟩ rewrite) (.fiat ⟨fa, fb⟩))

private def create : Rule :=
  ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])], "R"⟩
private def program : Program := globals ++ [.rule create, .saturate "R"]
private def creation (premise : Proof) : Proof := .rule ⟨ga, ga⟩ 7 [("x", a)] [premise]

#guard accepts program (creation (fiat fa)) ⟨ga, ga⟩
#guard rejects program (fiat ga)
#guard rejects program (creation (fiat a))
#guard rejects program (.rule ⟨ga, ga⟩ 0 [("x", a)] [fiat fa])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [] [fiat fa])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [("x", a), ("x", a)] [fiat fa])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [("x", a), ("unused", b)] [fiat fa])
#guard rejects program (.rule ⟨a, b⟩ 7 [("x", a)] [fiat fa])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [("x", a)] [])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [("x", a)] [fiat fa, fiat fa])

private def absentPremise : Program := declarations ++
  [.action (.expr a.toExpr), .action (.expr b.toExpr),
   .rule ⟨[.expr missing.toExpr], [.union a.toExpr b.toExpr], "R"⟩]

#guard rejects absentPremise (.rule ⟨a, b⟩ 7 [] [fiat missing])
#guard accepts (absentPremise ++ [.action (.expr missing.toExpr)])
  (.rule ⟨a, b⟩ 7 [] [fiat missing]) ⟨a, b⟩

private def gb : Term := .app "G" [b]

-- An expression premise may be anchored at another congruent term.
#guard accepts program (.rule ⟨gb, gb⟩ 7 [("x", b)] [rewrite]) ⟨gb, gb⟩

private def ordered : Program := globals ++
  [.rule ⟨[.expr (.app "F" [.var "x"]), .eq (.var "x") b.toExpr],
    [.expr (.app "G" [.var "x"])], "R"⟩]

#guard accepts ordered (.rule ⟨ga, ga⟩ 7 [("x", a)] [fiat fa, .fiat ⟨a, b⟩]) ⟨ga, ga⟩
#guard rejects ordered (.rule ⟨ga, ga⟩ 7 [("x", a)] [.fiat ⟨a, b⟩, fiat fa])

private def unconditional : Program := declarations ++
  [.rule ⟨[], [.expr missing.toExpr], "R"⟩]

#guard accepts unconditional (.rule ⟨missing, missing⟩ 5 [] []) ⟨missing, missing⟩
#guard rejects unconditional (fiat missing)

private def nested : Program := declarations ++
  [.action (.expr (.app "F" [fa.toExpr])),
   .rule ⟨[.expr (.app "F" [.app "F" [.var "x"]])],
     [.expr (.app "G" [.var "x"])], "R"⟩]

-- One premise for the original nested query, with no flattening in the checker.
#guard accepts nested (.rule ⟨ga, ga⟩ 6 [("x", a)] [fiat (.app "F" [fa])]) ⟨ga, ga⟩

private def functions : Program := declarations ++
  [.decl "Table" ⟨0, 1, some (.merge [] [.var "old"]), none⟩,
   .action (.expr (.app "Table" [a.toExpr]))]

#guard !sourceOk functions
#guard rejects functions (fiat (.app "Table" [a]))
#guard !sourceOk (declarations ++
  [.rule ⟨[.expr (.app "F" [.min (.var "x") (.var "y")])], [], "R"⟩])
-- A bare variable or literal is not a query fact, as in egglog.
#guard !sourceOk (declarations ++ [.rule ⟨[.expr (.var "x")], [], "R"⟩])
#guard !sourceOk (declarations ++ [.rule ⟨[.expr (.lit (.int 3))], [], "R"⟩])
#guard (contextOf (globals ++ [.decl "A" (ctor 0)])).isNone
#guard (contextOf (declarations ++ [.action (.expr (.var "unbound"))])).isNone

end Egglog.SourceProof.Tests
