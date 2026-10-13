import EgglogSemantics.Provenance.Format
import EgglogSemantics.Spec.Scope

namespace Egglog.Provenance

def actionFacts (sig : Signature) (σ : Env) : Action → Option (List Term)
  | .expr e => do
      let t ← e.evalAtom sig σ
      if SourceProof.atomOk sig t then some t.subtermList else none
  | .union _ _ => none

def actionsFacts (sig : Signature) (σ : Env) : List Action → Option (List Term)
  | [] => some []
  | a :: as => do
      let fs ← actionFacts sig σ a
      let rest ← actionsFacts sig σ as
      some (fs ++ rest)

def unionFree (P : Program) : Bool := P.all fun c => match c with
  | .action a => match a with | .expr _ => true | .union _ _ => false
  | .rule r => r.actions.all fun a => match a with | .expr _ => true | .union _ _ => false
  | .decl _ d => match d.merge with
    | some (.merge body _) => body.all fun a => match a with
      | .expr _ => true | .union _ _ => false
    | _ => true
  | _ => true

def premiseMatches (sig : Signature) (σ : Env) (p : Pattern) (fact : Term) : Bool :=
  match p with
  | .expr e => e.evalAtom sig σ == some fact
  | .eq a b => a.eval sig σ == some fact && b.eval sig σ == some fact

def premisesMatch (sig : Signature) (σ : Env) : Query → List Term → Bool
  | [], [] => true
  | p :: ps, t :: ts => premiseMatches sig σ p t && premisesMatch sig σ ps ts
  | _, _ => false

def ruleFacts (sig : Signature) (r : Rule) (σ : Env)
    (premises : List Term) : Option (List Term) := do
  if decide ((Env.dom σ).Perm r.query.vars) &&
      σ.all (fun b => SourceProof.valueOk sig b.2 &&
        premises.any (fun p => decide (b.2 ∈ p.subtermList))) &&
      premisesMatch sig σ r.query premises then
    actionsFacts sig σ r.actions
  else none

structure MergeFacts where
  body : List Term
  result : Term

def conflicts (d : FnDecl) (body : List Action) (old new : List Term) : Bool :=
  match d.unchangedWidth body with
  | none => true
  | some k => old.take k != new.take k

/-- Both inputs must be actual entries at the same structural key. -/
def mergeFacts (sig : Signature) (f : FnName) (old new : Term) : Option MergeFacts := do
  let d ← sig f
  let some (.merge body res) := d.merge | none
  let .app ofn oc := old | none
  let .app nfn nc := new | none
  if ofn == f && nfn == f && oc.length == d.entryWidth && nc.length == d.entryWidth &&
      oc.take d.arity == nc.take d.arity then do
    let os := oc.drop d.arity
    let ns := nc.drop d.arity
    if conflicts d body os ns then do
      let σ := mergeEnv os ns
      let facts ← actionsFacts sig σ body
      let vs ← Expr.evalList sig res σ
      if vs.length == d.outArity && SourceProof.valuesOk sig vs then
        some ⟨facts, .app f (oc.take d.arity ++ vs)⟩
      else none
    else none
  else none

def checkReason (P : Program) (sig : Signature) (prior : List Term) (n : Node) : Bool :=
  (match n.reason with
  | .global i => do
      let .action a ← P[i]? | none
      let facts ← actionFacts sig [] a
      some (decide (n.fact ∈ facts))
  | .rule i σ ps => do
      let .rule r ← P[i]? | none
      let premises ← ps.mapM fun j => prior[j]?
      let facts ← ruleFacts sig r σ premises
      some (decide (n.fact ∈ facts))
  | .merge f i j => do
      let old ← prior[i]?
      let new ← prior[j]?
      let facts ← mergeFacts sig f old new
      some (decide (n.fact ∈ facts.body ∨ n.fact ∈ facts.result.subtermList))
  | .subterm i => do
      let parent ← prior[i]?
      some (decide (n.fact ∈ parent.subtermList))).getD false

def checkNode (P : Program) (C : SourceProof.Context) (prior : List Term) (n : Node) : Bool :=
  SourceProof.atomOk C.sig n.fact && checkReason P C.sig prior n &&
    match n.reason with
    | .global _ => decide ((⟨n.fact, n.fact⟩ : SourceProof.Claim) ∈ C.globals)
    | _ => true

def checkNodes (P : Program) (C : SourceProof.Context) : List Term → List Node → Option (List Term)
  | prior, [] => some prior
  | prior, n :: ns =>
      if checkNode P C prior n then
        checkNodes P C (prior ++ [n.fact]) ns
      else none

def check (P : Program) (cert : Certificate) : Option Term := do
  if !unionFree P then none else do
    let C ← SourceProof.contextOf P
    let facts ← checkNodes P C [] cert.nodes
    facts[cert.root]?

end Egglog.Provenance
