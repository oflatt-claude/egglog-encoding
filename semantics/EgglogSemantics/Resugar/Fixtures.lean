import EgglogSemantics.Resugar.Execute
import EgglogSemantics.Congruence.Relational

/-! Proofs the Lean and Rust source checkers must judge alike: lifted proofs for small
programs, and hand-written proofs with known verdicts. -/

namespace Egglog.Resugar.Fixtures

private def ctor (n : Nat) : FnDecl := ⟨n, 1, none, none⟩
private def atom (f : FnName) : Expr := .app f []
private def term (f : FnName) : Term := .app f []

def nestedUnion : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "F" (ctor 1),
   .rule ⟨[], [.expr (.app "F" [atom "A"]), .expr (.app "F" [atom "B"]),
     .union (atom "A") (atom "B")], "seed"⟩, .run "seed"]

def nestedQuery : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "G" (ctor 1), .decl "F" (ctor 2),
   .decl "H" (ctor 1),
   .rule ⟨[], [.expr (.app "F" [.app "G" [atom "B"], .app "G" [atom "B"]]),
     .union (atom "A") (atom "B")], "seed"⟩, .run "seed",
   .rule ⟨[.expr (.app "F" [.app "G" [.var "x"], .app "G" [.var "x"]])],
     [.expr (.app "H" [.var "x"])], "R"⟩, .saturate "R"]

def equalityQuery : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "F" (ctor 1), .decl "G" (ctor 1),
   .rule ⟨[], [.expr (.app "F" [atom "A"]), .expr (.app "G" [atom "B"]),
     .union (.app "F" [atom "A"]) (.app "G" [atom "B"])], "seed"⟩, .run "seed",
   .rule ⟨[.eq (.app "F" [.var "x"]) (.app "G" [.var "y"])],
     [.union (.var "x") (.var "y")], "R"⟩, .saturate "R"]

def ruleChain : Program :=
  [.decl "A" (ctor 0), .decl "F" (ctor 1), .decl "G" (ctor 1),
   .rule ⟨[], [.expr (.app "F" [atom "A"])], "R"⟩,
   .rule ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])], "R"⟩,
   .saturate "R"]

def missingPremise : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "Missing" (ctor 0),
   .rule ⟨[], [.expr (atom "A"), .expr (atom "B")], "seed"⟩, .run "seed",
   .rule ⟨[.expr (atom "Missing")], [.union (atom "A") (atom "B")], "R"⟩,
   .saturate "R"]

def supportCase : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "F" (ctor 1), .decl "G" (ctor 1),
   .rule ⟨[], [.expr (.app "F" [atom "A"])], "seed"⟩, .run "seed",
   .rule ⟨[], [.union (atom "A") (.app "G" [atom "B"])], "R"⟩]

/-- Programs whose every retained row lifts to an accepted source proof. -/
def lifted : List (String × Program) :=
  [("nested-union", nestedUnion), ("nested-query", nestedQuery),
   ("equality-query", equalityQuery), ("rule-chain", ruleChain),
   ("missing-premise", missingPremise), ("support", supportCase)]

structure Fixture where
  name : String
  program : Program
  certificates : List SourceProof.Proof

private def a : Term := term "A"
private def b : Term := term "B"
private def missing : Term := term "Missing"
private def fa : Term := .app "F" [a]
private def fb : Term := .app "F" [b]
private def ga : Term := .app "G" [a]
private def fact (t : Term) : SourceProof.Proof := .rule ⟨t, t⟩ 5 [] []
private def unionFact (x y : Term) : SourceProof.Proof := .rule ⟨x, y⟩ 6 [] []

private def declarations : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "Missing" (ctor 0),
   .decl "F" (ctor 1), .decl "G" (ctor 1)]

private def seed : Program := declarations ++
  [.rule ⟨[], [.expr fa.toExpr], "seed"⟩,
   .rule ⟨[], [.union a.toExpr b.toExpr], "seed"⟩, .run "seed"]

/-- Command 8 builds `(G x)` from `(F x)`. -/
private def create : Program := seed ++
  [.rule ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])], "R"⟩, .saturate "R"]

/-- Command 8 reads `(F x)` and then `(= x (B))`. -/
private def ordered : Program := seed ++
  [.rule ⟨[.expr (.app "F" [.var "x"]), .eq (.var "x") b.toExpr],
    [.expr (.app "G" [.var "x"])], "R"⟩]

/-- Command 7 reads the nested pattern `(F (F x))` as one premise. -/
private def nested : Program := declarations ++
  [.rule ⟨[], [.expr (.app "F" [fa.toExpr])], "seed"⟩, .run "seed",
   .rule ⟨[.expr (.app "F" [.app "F" [.var "x"]])], [.expr (.app "G" [.var "x"])], "R"⟩]

/-- Command 8 fires only on `(Missing)`, which is never built. -/
private def absentPremise : Program := declarations ++
  [.rule ⟨[], [.expr a.toExpr], "seed"⟩,
   .rule ⟨[], [.expr b.toExpr], "seed"⟩, .run "seed",
   .rule ⟨[.expr missing.toExpr], [.union a.toExpr b.toExpr], "R"⟩]

private def one (name : String) (P : Program) (pf : SourceProof.Proof) : Fixture :=
  ⟨name, P, [pf]⟩

/-- Accepted hand-written proofs: ordered premises and a nested premise. -/
def accepted : List Fixture :=
  [one "ordered-premises" ordered (.rule ⟨ga, ga⟩ 8 [("x", a)] [fact fa, unionFact a b]),
   one "nested-premise" nested (.rule ⟨ga, ga⟩ 7 [("x", a)] [fact (.app "F" [fa])])]

/-- Rejected hand-written proofs: invented initial facts, an absent premise, malformed
substitutions, wrong premise order or count, and wrong endpoints and conclusions. -/
def rejected : List Fixture :=
  [one "invented-initial-fact" create (fact missing),
   one "invented-application" create (fact fb),
   one "absent-premise" absentPremise (.rule ⟨a, b⟩ 8 [] [fact missing]),
   one "unbound-variable" create (.rule ⟨ga, ga⟩ 8 [] [fact fa]),
   one "wrong-binding" create (.rule ⟨ga, ga⟩ 8 [("x", b)] [fact fa]),
   one "missing-premise-proof" create (.rule ⟨ga, ga⟩ 8 [("x", a)] []),
   one "premise-order" ordered (.rule ⟨ga, ga⟩ 8 [("x", a)] [unionFact a b, fact fa]),
   one "wrong-conclusion" create (.rule ⟨a, b⟩ 8 [("x", a)] [fact fa]),
   one "transitivity-endpoints" create (.trans ⟨a, b⟩ (fact a) (fact b)),
   one "congruence-child" create (.congr ⟨fa, fb⟩ (fact fa) 0 (unionFact b a)),
   one "symmetry-claim" create (.symm ⟨a, a⟩ (fact fa))]

/-- Every fixture, with the lifted ones first. `none` if a program fails to lift. -/
def all : Option (List Fixture) := do
  let liftedFixtures ← lifted.mapM fun np => do
    let cs ← certificates (Relational.execProgram FDatabase.empty) np.2
    pure (⟨np.1, np.2, cs⟩ : Fixture)
  pure (liftedFixtures ++ accepted ++ rejected)

end Egglog.Resugar.Fixtures
