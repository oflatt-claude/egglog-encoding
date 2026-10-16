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

private def seed : Program := declarations ++
  [.rule ⟨[], [.expr fa.toExpr], "R"⟩, .rule ⟨[], [.union a.toExpr b.toExpr], "R"⟩]

private def fact (x : Term) : Proof := .rule ⟨x, x⟩ 5 [] []
private def unionFact (x y : Term) : Proof := .rule ⟨x, y⟩ 6 [] []
private def accepts (P : Program) (pf : Proof) (c : Claim) : Bool := check P pf == some c
private def rejects (P : Program) (pf : Proof) : Bool := (check P pf).isNone

#guard accepts seed (fact a) ⟨a, a⟩
#guard accepts seed (unionFact b a) ⟨b, a⟩
#guard rejects seed (fact missing)
#guard rejects seed (fact fb)
#guard rejects declarations (fact (.lit (.int 3)))

private def rewrite : Proof := .congr ⟨fa, fb⟩ (fact fa) 0 (unionFact a b)
private def childRewrite : Proof := .trans ⟨fb, fb⟩ (.symm ⟨fb, fa⟩ rewrite) rewrite

#guard accepts seed childRewrite ⟨fb, fb⟩
#guard rejects seed (.symm ⟨a, a⟩ (fact fa))
#guard rejects seed (.congr ⟨fa, fb⟩ (fact fa) 1 (unionFact a b))
#guard rejects seed (.congr ⟨fa, fb⟩ (fact fa) 0 (unionFact b a))
#guard rejects seed (.trans ⟨a, b⟩ (fact a) (fact b))
-- Every node is checked, not only the root.
#guard rejects seed (.trans ⟨fb, fb⟩ (.symm ⟨fb, fa⟩ rewrite) (.rule ⟨fa, fb⟩ 5 [] []))

private def create : Rule :=
  ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])], "R"⟩
private def program : Program := seed ++ [.rule create, .saturate "R"]
private def creation (premise : Proof) : Proof := .rule ⟨ga, ga⟩ 7 [("x", a)] [premise]

#guard accepts program (creation (fact fa)) ⟨ga, ga⟩
#guard rejects program (fact ga)
#guard rejects program (creation (fact a))
#guard rejects program (.rule ⟨ga, ga⟩ 0 [("x", a)] [fact fa])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [] [fact fa])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [("x", a), ("x", a)] [fact fa])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [("x", a), ("unused", b)] [fact fa])
#guard rejects program (.rule ⟨a, b⟩ 7 [("x", a)] [fact fa])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [("x", a)] [])
#guard rejects program (.rule ⟨ga, ga⟩ 7 [("x", a)] [fact fa, fact fa])

private def absentPremise : Program := declarations ++
  [.rule ⟨[], [.expr a.toExpr], "R"⟩, .rule ⟨[], [.expr b.toExpr], "R"⟩,
   .rule ⟨[.expr missing.toExpr], [.union a.toExpr b.toExpr], "R"⟩]

#guard rejects absentPremise (.rule ⟨a, b⟩ 7 [] [.rule ⟨missing, missing⟩ 8 [] []])
#guard accepts (absentPremise ++ [.rule ⟨[], [.expr missing.toExpr], "R"⟩])
  (.rule ⟨a, b⟩ 7 [] [.rule ⟨missing, missing⟩ 8 [] []]) ⟨a, b⟩

private def gb : Term := .app "G" [b]

-- An expression premise may be anchored at another congruent term.
#guard accepts program (.rule ⟨gb, gb⟩ 7 [("x", b)] [rewrite]) ⟨gb, gb⟩

private def ordered : Program := seed ++
  [.rule ⟨[.expr (.app "F" [.var "x"]), .eq (.var "x") b.toExpr],
    [.expr (.app "G" [.var "x"])], "R"⟩]

#guard accepts ordered (.rule ⟨ga, ga⟩ 7 [("x", a)] [fact fa, unionFact a b]) ⟨ga, ga⟩
#guard rejects ordered (.rule ⟨ga, ga⟩ 7 [("x", a)] [unionFact a b, fact fa])

private def unconditional : Program := declarations ++
  [.rule ⟨[], [.expr missing.toExpr], "R"⟩]

#guard accepts unconditional (.rule ⟨missing, missing⟩ 5 [] []) ⟨missing, missing⟩
#guard rejects unconditional (.rule ⟨missing, missing⟩ 6 [] [])

private def nested : Program := declarations ++
  [.rule ⟨[], [.expr (.app "F" [fa.toExpr])], "R"⟩,
   .rule ⟨[.expr (.app "F" [.app "F" [.var "x"]])],
     [.expr (.app "G" [.var "x"])], "R"⟩]

-- One premise for the original nested query, with no flattening in the checker.
#guard accepts nested (.rule ⟨ga, ga⟩ 6 [("x", a)] [fact (.app "F" [fa])]) ⟨ga, ga⟩

private def functions : Program := declarations ++
  [.decl "Table" ⟨0, 1, some (.merge ["old"] ["new"] [] [.var "old"]), none⟩,
   .rule ⟨[], [.expr (.app "Table" [a.toExpr])], "R"⟩]

#guard !sourceOk functions
#guard rejects functions (fact (.app "Table" [a]))
#guard !sourceOk (declarations ++
  [.rule ⟨[.expr (.app "F" [.min (.var "x") (.var "y")])], [], "R"⟩])
-- A bare variable or literal is not a query fact, as in egglog.
#guard !sourceOk (declarations ++ [.rule ⟨[.expr (.var "x")], [], "R"⟩])
#guard !sourceOk (declarations ++ [.rule ⟨[.expr (.lit (.int 3))], [], "R"⟩])
#guard (contextOf (seed ++ [.decl "A" (ctor 0)])).isNone
#guard rejects (declarations ++ [.rule ⟨[], [.expr (.var "unbound")], "R"⟩])
  (.rule ⟨a, a⟩ 5 [] [])

end Egglog.SourceProof.Tests
