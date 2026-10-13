import EgglogSemantics.Resugar.Builder

namespace Egglog.Resugar

open SourceProof (Context Proof)

def replaceChildren (P : Program) (C : Context) (children : List Proof)
    (parent : Proof) : Option Proof :=
  children.zipIdx.foldlM (fun acc child => congr P C acc child.2 child.1) parent

mutual

/-- The compiler's left-to-right postorder, repeated on the original expression. The
unconsumed premise proofs are threaded through in that order. -/
def queryExpr (P : Program) (C : Context) (σ : Env) (allPremises : List Proof) :
    Expr → List Proof → Option (Proof × List Proof)
  | .app f args, remaining => do
    let (children, rest) ← queryArgs P C σ allPremises args remaining
    let parent :: rest := rest | none
    if parent.claim.rhs != .app f (children.map (·.claim.lhs)) then none else do
      let result ← replaceChildren P C children parent
      some (result, rest)
  | e, remaining => do
    let t ← e.eval C.sig σ
    let p ← witness P C t allPremises
    some (p, remaining)

def queryArgs (P : Program) (C : Context) (σ : Env) (allPremises : List Proof) :
    List Expr → List Proof → Option (List Proof × List Proof)
  | [], remaining => some ([], remaining)
  | e :: es, remaining => do
    let (p, next) ← queryExpr P C σ allPremises e remaining
    let (ps, last) ← queryArgs P C σ allPremises es next
    some (p :: ps, last)

end

def queryPattern (P : Program) (C : Context) (σ : Env) (allPremises : List Proof)
    (p : Pattern) (remaining : List Proof) : Option (Proof × List Proof) := do
  match p with
  | .expr e => queryExpr P C σ allPremises e remaining
  | .eq lhs rhs =>
    let (a, next) ← queryExpr P C σ allPremises lhs remaining
    let (z, last) ← queryExpr P C σ allPremises rhs next
    let equality :: rest := last | none
    if equality.claim != (⟨a.claim.lhs, z.claim.lhs⟩ : SourceProof.Claim) then none else do
      let rev ← symm P C a
      let left ← trans P C rev equality
      let result ← trans P C left z
      some (result, rest)

def queryPatterns (P : Program) (C : Context) (σ : Env) (allPremises : List Proof) :
    Query → List Proof → Option (List Proof × List Proof)
  | [], remaining => some ([], remaining)
  | p :: ps, remaining => do
    let (a, next) ← queryPattern P C σ allPremises p remaining
    let (as, last) ← queryPatterns P C σ allPremises ps next
    some (a :: as, last)

/-- One source premise proof per original query conjunct, consuming every lifted premise. -/
def query (P : Program) (C : Context) (σ : Env) (q : Query) (premises : List Proof) :
    Option (List Proof) := do
  let (ps, remaining) ← queryPatterns P C σ premises q premises
  if remaining.isEmpty then some ps else none

end Egglog.Resugar
