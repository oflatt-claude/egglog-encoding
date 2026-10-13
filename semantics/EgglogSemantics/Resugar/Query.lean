import EgglogSemantics.Resugar.Builder

namespace Egglog.Resugar

open SourceProof (Context)

structure QueryState where
  builder : Builder
  remaining : List Nat

def replaceChildren (P : Program) (C : Context) (children : List Nat)
    (parent : Nat) (b : Builder) : Option (Nat × Builder) :=
  children.zipIdx.foldlM (fun state child =>
    state.2.congr P C state.1 child.2 child.1) (parent, b)

mutual

/-- The compiler's left-to-right postorder, repeated on the original expression. -/
def queryExpr (P : Program) (C : Context) (σ : Env) (allPremises : List Nat) :
    Expr → QueryState → Option (Nat × QueryState)
  | .app f args, state => do
    let (children, next) ← queryArgs P C σ allPremises args state
    let parent :: rest := next.remaining | none
    let claim ← next.builder.claims[parent]?
    let ids ← children.mapM fun i => (next.builder.claims[i]?).map SourceProof.Claim.lhs
    if claim.rhs != .app f ids then none else do
      let (result, b) ← replaceChildren P C children parent next.builder
      some (result, ⟨b, rest⟩)
  | e, state => do
    let t ← e.eval C.sig σ
    let (i, b) ← witness P C state.builder t allPremises
    some (i, { state with builder := b })

def queryArgs (P : Program) (C : Context) (σ : Env) (allPremises : List Nat) :
    List Expr → QueryState → Option (List Nat × QueryState)
  | [], state => some ([], state)
  | e :: es, state => do
    let (i, next) ← queryExpr P C σ allPremises e state
    let (is, last) ← queryArgs P C σ allPremises es next
    some (i :: is, last)

end

def queryPattern (P : Program) (C : Context) (σ : Env) (allPremises : List Nat)
    (p : Pattern) (state : QueryState) : Option (Nat × QueryState) := do
  match p with
  | .expr e => queryExpr P C σ allPremises e state
  | .eq lhs rhs =>
    let (i, next) ← queryExpr P C σ allPremises lhs state
    let (j, last) ← queryExpr P C σ allPremises rhs next
    let equality :: rest := last.remaining | none
    let a ← last.builder.claims[i]?
    let z ← last.builder.claims[j]?
    let eq ← last.builder.claims[equality]?
    if eq != (⟨a.lhs, z.lhs⟩ : SourceProof.Claim) then none else do
      let (rev, b) ← last.builder.symm P C i
      let (left, b) ← b.trans P C rev equality
      let (result, b) ← b.trans P C left j
      some (result, ⟨b, rest⟩)

def queryPatterns (P : Program) (C : Context) (σ : Env) (allPremises : List Nat) :
    Query → QueryState → Option (List Nat × QueryState)
  | [], state => some ([], state)
  | p :: ps, state => do
    let (i, next) ← queryPattern P C σ allPremises p state
    let (is, last) ← queryPatterns P C σ allPremises ps next
    some (i :: is, last)

def query (P : Program) (C : Context) (σ : Env) (q : Query) (premises : List Nat)
    (b : Builder) : Option (List Nat × Builder) := do
  let (ps, state) ← queryPatterns P C σ premises q ⟨b, premises⟩
  if state.remaining.isEmpty then some (ps, state.builder) else none

end Egglog.Resugar
