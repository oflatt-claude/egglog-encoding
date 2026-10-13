import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Spec.Scope

namespace Egglog.SourceProof

def exprOk (e : Expr) : Bool := e.fns.all fun f => (Prim.ofName f).isNone

/-- A query fact is an application, as in egglog; an equality compares value expressions. -/
def patternOk : Pattern → Bool
  | .expr (.app f args) => exprOk (.app f args)
  | .expr _ => false
  | .eq a b => exprOk a && exprOk b

def actionOk : Action → Bool
  | .expr e => exprOk e
  | .union a b => exprOk a && exprOk b

def ruleOk (r : Rule) : Bool := r.query.all patternOk && r.actions.all actionOk

def sourceOk (P : Program) : Bool := P.all fun c => match c with
  | .decl _ d => d.merge.isNone
  | .rule r => ruleOk r
  | .action a => actionOk a
  | _ => true

def premiseMatches (sig : Signature) (σ : Env) (p : Pattern) (c : Claim) : Bool :=
  match p with
  | .expr e => e.evalAtom sig σ == some c.rhs &&
      ((e.entry sig).isNone || c.lhs == c.rhs)
  | .eq a b => a.eval sig σ == some c.lhs && b.eval sig σ == some c.rhs

def premisesMatch (sig : Signature) (σ : Env) : Query → List Claim → Bool
  | [], [] => true
  | p :: ps, c :: cs => premiseMatches sig σ p c && premisesMatch sig σ ps cs
  | _, _ => false

def supportedValue (premises : List Claim) (t : Term) : Bool :=
  premises.any fun c => decide (t ∈ c.lhs.subtermList ∨ t ∈ c.rhs.subtermList)

def ruleFacts (C : Context) (r : Rule) (σ : Env)
    (premises : List Claim) : Option (List Claim) := do
  if decide ((Env.dom σ).Perm r.query.vars) &&
      σ.all (fun b => valueOk C.sig b.2 && supportedValue premises b.2) &&
      premisesMatch C.sig σ r.query premises then
    actionsFacts C.sig σ r.actions
  else none

def checkReason (P : Program) (C : Context) (prior : List Claim) (n : Node) : Bool :=
  (match n.reason with
  | .fiat => some (decide (n.claim ∈ C.globals))
  | .symm i => do
      let p ← prior[i]?
      some (n.claim == (⟨p.rhs, p.lhs⟩ : Claim))
  | .trans i j => do
      let p ← prior[i]?
      let q ← prior[j]?
      some (p.rhs == q.lhs && n.claim == (⟨p.lhs, q.rhs⟩ : Claim))
  | .congr i k j => do
      let p ← prior[i]?
      let q ← prior[j]?
      let .app f args := p.rhs | none
      let t ← args[k]?
      some (t == q.lhs && valueOk C.sig q.lhs && valueOk C.sig q.rhs &&
        n.claim == (⟨p.lhs, .app f (args.set k q.rhs)⟩ : Claim))
  | .rule i σ ps => do
      let .rule r ← P[i]? | none
      let premises ← ps.mapM fun j => prior[j]?
      let fs ← ruleFacts C r σ premises
      some (decide (n.claim ∈ fs))).getD false

def checkNode (P : Program) (C : Context) (prior : List Claim) (n : Node) : Bool :=
  atomOk C.sig n.claim.lhs && atomOk C.sig n.claim.rhs &&
    checkReason P C prior n

def checkNodes (P : Program) (C : Context) : List Claim → List Node → Option (List Claim)
  | prior, [] => some prior
  | prior, n :: ns =>
      if checkNode P C prior n then checkNodes P C (prior ++ [n.claim]) ns else none

/-- Validate every node before returning the selected claim. -/
def check (P : Program) (cert : Certificate) : Option Claim := do
  if !sourceOk P then none else do
    let C ← contextOf P
    let claims ← checkNodes P C [] cert.nodes
    claims[cert.root]?

end Egglog.SourceProof
