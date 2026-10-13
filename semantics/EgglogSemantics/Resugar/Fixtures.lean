import EgglogSemantics.Resugar.Lift
import EgglogSemantics.Congruence.Relational

/-! Proofs the Lean and Rust source checkers must judge alike: lifted proofs for small
programs, and hand-written proofs with known verdicts. -/

namespace Egglog.Resugar.Fixtures

private def ctor (n : Nat) : FnDecl := ⟨n, 1, none, none⟩
private def atom (f : FnName) : Expr := .app f []
private def term (f : FnName) : Term := .app f []

def nestedUnion : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "F" (ctor 1),
   .action (.expr (.app "F" [atom "A"])), .action (.expr (.app "F" [atom "B"])),
   .action (.union (atom "A") (atom "B"))]

def nestedQuery : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "G" (ctor 1), .decl "F" (ctor 2),
   .decl "H" (ctor 1),
   .action (.expr (.app "F" [.app "G" [atom "B"], .app "G" [atom "B"]])),
   .action (.union (atom "A") (atom "B")),
   .rule ⟨[.expr (.app "F" [.app "G" [.var "x"], .app "G" [.var "x"]])],
     [.expr (.app "H" [.var "x"])], "R"⟩, .saturate "R"]

def equalityQuery : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "F" (ctor 1), .decl "G" (ctor 1),
   .action (.expr (.app "F" [atom "A"])), .action (.expr (.app "G" [atom "B"])),
   .action (.union (.app "F" [atom "A"]) (.app "G" [atom "B"])),
   .rule ⟨[.eq (.app "F" [.var "x"]) (.app "G" [.var "y"])],
     [.union (.var "x") (.var "y")], "R"⟩, .saturate "R"]

def ruleChain : Program :=
  [.decl "A" (ctor 0), .decl "F" (ctor 1), .decl "G" (ctor 1),
   .rule ⟨[], [.expr (.app "F" [atom "A"])], "R"⟩,
   .rule ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])], "R"⟩,
   .saturate "R"]

def missingPremise : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "Missing" (ctor 0),
   .action (.expr (atom "A")), .action (.expr (atom "B")),
   .rule ⟨[.expr (atom "Missing")], [.union (atom "A") (atom "B")], "R"⟩,
   .saturate "R"]

def supportCase : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "F" (ctor 1), .decl "G" (ctor 1),
   .action (.expr (.app "F" [atom "A"])),
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
private def fiat (t : Term) : SourceProof.Proof := .fiat ⟨t, t⟩

private def declarations : Program :=
  [.decl "A" (ctor 0), .decl "B" (ctor 0), .decl "Missing" (ctor 0),
   .decl "F" (ctor 1), .decl "G" (ctor 1)]

private def globals : Program := declarations ++
  [.action (.expr fa.toExpr), .action (.union a.toExpr b.toExpr)]

/-- Command 7 builds `(G x)` from `(F x)`. -/
private def create : Program := globals ++
  [.rule ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])], "R"⟩, .saturate "R"]

/-- Command 7 reads `(F x)` and then `(= x (B))`. -/
private def ordered : Program := globals ++
  [.rule ⟨[.expr (.app "F" [.var "x"]), .eq (.var "x") b.toExpr],
    [.expr (.app "G" [.var "x"])], "R"⟩]

/-- Command 6 reads the nested pattern `(F (F x))` as one premise. -/
private def nested : Program := declarations ++
  [.action (.expr (.app "F" [fa.toExpr])),
   .rule ⟨[.expr (.app "F" [.app "F" [.var "x"]])], [.expr (.app "G" [.var "x"])], "R"⟩]

/-- Command 7 fires only on `(Missing)`, which is never built. -/
private def absentPremise : Program := declarations ++
  [.action (.expr a.toExpr), .action (.expr b.toExpr),
   .rule ⟨[.expr missing.toExpr], [.union a.toExpr b.toExpr], "R"⟩]

private def one (name : String) (P : Program) (pf : SourceProof.Proof) : Fixture :=
  ⟨name, P, [pf]⟩

/-- Accepted hand-written proofs: ordered premises and a nested premise. -/
def accepted : List Fixture :=
  [one "ordered-premises" ordered (.rule ⟨ga, ga⟩ 7 [("x", a)] [fiat fa, .fiat ⟨a, b⟩]),
   one "nested-premise" nested (.rule ⟨ga, ga⟩ 6 [("x", a)] [fiat (.app "F" [fa])])]

/-- Rejected hand-written proofs: invented globals, an absent premise, malformed
substitutions, wrong premise order or count, and wrong endpoints and conclusions. -/
def rejected : List Fixture :=
  [one "invented-global" create (fiat missing),
   one "invented-application" create (fiat fb),
   one "absent-premise" absentPremise (.rule ⟨a, b⟩ 7 [] [fiat missing]),
   one "unbound-variable" create (.rule ⟨ga, ga⟩ 7 [] [fiat fa]),
   one "wrong-binding" create (.rule ⟨ga, ga⟩ 7 [("x", b)] [fiat fa]),
   one "missing-premise-proof" create (.rule ⟨ga, ga⟩ 7 [("x", a)] []),
   one "premise-order" ordered (.rule ⟨ga, ga⟩ 7 [("x", a)] [.fiat ⟨a, b⟩, fiat fa]),
   one "wrong-conclusion" create (.rule ⟨a, b⟩ 7 [("x", a)] [fiat fa]),
   one "transitivity-endpoints" create (.trans ⟨a, b⟩ (fiat a) (fiat b)),
   one "congruence-child" create (.congr ⟨fa, fb⟩ (fiat fa) 0 (.fiat ⟨b, a⟩)),
   one "symmetry-claim" create (.symm ⟨a, a⟩ (fiat fa))]

/-- Every fixture, with the lifted ones first. `none` if a program fails to lift. -/
def all : Option (List Fixture) := do
  let liftedFixtures ← lifted.mapM fun np => do
    let cs ← certificates (Relational.execProgram FDatabase.empty) np.2
    pure (⟨np.1, np.2, cs⟩ : Fixture)
  pure (liftedFixtures ++ accepted ++ rejected)

end Egglog.Resugar.Fixtures
