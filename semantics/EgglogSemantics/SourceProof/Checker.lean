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

/-- The root node, against the claims its subproofs state. -/
def checkNode (P : Program) (C : Context) (pf : Proof) : Bool :=
  atomOk C.sig pf.claim.lhs && atomOk C.sig pf.claim.rhs &&
  match pf with
  | .fiat c => decide (c ∈ C.globals)
  | .symm c p => c == ⟨p.claim.rhs, p.claim.lhs⟩
  | .trans c p q => p.claim.rhs == q.claim.lhs && c == ⟨p.claim.lhs, q.claim.rhs⟩
  | .congr c p k q =>
      match p.claim.rhs with
      | .app f args =>
          args[k]? == some q.claim.lhs && valueOk C.sig q.claim.lhs &&
            valueOk C.sig q.claim.rhs &&
            c == ⟨p.claim.lhs, .app f (args.set k q.claim.rhs)⟩
      | .lit _ => false
  | .rule c i σ ps => (do
      let .rule r ← P[i]? | none
      let fs ← ruleFacts C r σ (ps.map Proof.claim)
      some (decide (c ∈ fs))).getD false

mutual

/-- Every node is valid. -/
def valid (P : Program) (C : Context) : Proof → Bool
  | .fiat c => checkNode P C (.fiat c)
  | .symm c p => valid P C p && checkNode P C (.symm c p)
  | .trans c p q => valid P C p && valid P C q && checkNode P C (.trans c p q)
  | .congr c p k q => valid P C p && valid P C q && checkNode P C (.congr c p k q)
  | .rule c i σ ps => allValid P C ps && checkNode P C (.rule c i σ ps)

def allValid (P : Program) (C : Context) : List Proof → Bool
  | [] => true
  | p :: ps => valid P C p && allValid P C ps

end

/-- The claim of a proof whose every node is valid. -/
def check (P : Program) (pf : Proof) : Option Claim := do
  if !sourceOk P then none else do
    let C ← contextOf P
    if valid P C pf then some pf.claim else none

end Egglog.SourceProof
