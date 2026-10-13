import EgglogSemantics.Resugar.Fixtures
import EgglogSemantics.Tests.Egg
import Lean.Data.Json

/-! Source certificates as JSON, for checking the same certificate with Rust egglog.
A case carries its program as `.egg` source, with every rule named `lean-rule-<index>`
after its command index, and one object per certificate with the Lean verdict. -/

namespace Egglog.Resugar.Export

open Lean (Json toJson)

mutual

/-- `["F", [args…]]` for an application; a literal is a tagged object. -/
def term : Term → Json
  | .lit (.int n) => Json.mkObj [("int", toJson n)]
  | .lit (.bool b) => Json.mkObj [("bool", toJson b)]
  | .app f args => .arr #[toJson f, .arr (terms args).toArray]

def terms : List Term → List Json
  | [] => []
  | t :: ts => term t :: terms ts

end

def ruleName (i : Nat) : String := "lean-rule-" ++ toString i

def reason : SourceProof.Reason → Json
  | .fiat => Json.mkObj [("kind", "fiat")]
  | .symm i => Json.mkObj [("kind", "symm"), ("proof", toJson i)]
  | .trans i j => Json.mkObj [("kind", "trans"), ("left", toJson i), ("right", toJson j)]
  | .congr i k j => Json.mkObj [("kind", "congr"), ("base", toJson i),
      ("index", toJson k), ("child", toJson j)]
  | .rule i σ ps => Json.mkObj [("kind", "rule"), ("rule", ruleName i),
      ("subst", .arr (σ.map fun bnd => .arr #[toJson bnd.1, term bnd.2]).toArray),
      ("premises", toJson ps)]

def node (n : SourceProof.Node) : Json := Json.mkObj
  [("lhs", term n.claim.lhs), ("rhs", term n.claim.rhs), ("reason", reason n.reason)]

def certificate (P : Program) (c : SourceProof.Certificate) : Json := Json.mkObj
  [("nodes", .arr (c.nodes.map node).toArray), ("root", toJson c.root),
   ("accepted", toJson (SourceProof.check P c).isSome)]

/-- The program as `.egg` source with rules named by command index. -/
def program (P : Program) : Option String := do
  if !SourceProof.sourceOk P then none else do
    let C ← SourceProof.contextOf P
    let commands := P.zipIdx.map fun ci => match ci.1 with
      | .rule r =>
        "(rule (" ++ String.intercalate " " (r.query.map (Pattern.toEgg C.sig)) ++ ") (" ++
          String.intercalate " " (r.actions.map (Action.toEgg C.sig)) ++ ") :name \"" ++
          ruleName ci.2 ++ "\"" ++
          (if r.ruleset == "" then "" else " :ruleset " ++ r.ruleset) ++ ")"
      | c => c.toEgg C.sig
    some (String.intercalate "\n" (P.eggHeader :: P.rulesetDecls ++
      commands.filter (· != "")))

def caseJson (name : String) (P : Program) (cs : List SourceProof.Certificate) :
    Option Json := do
  let source ← program P
  some (Json.mkObj [("case", name), ("program", source),
    ("certificates", .arr (cs.map (certificate P)).toArray)])

/-- The curated fixtures, which both checkers must judge alike. -/
def fixtures : Option (List Json) := do
  let fs ← Fixtures.all
  fs.mapM fun f => caseJson f.name f.program f.certificates

end Egglog.Resugar.Export
