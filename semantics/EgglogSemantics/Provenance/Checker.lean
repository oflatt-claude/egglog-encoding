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
    | some (.merge _ _ body _) => body.all fun a => match a with
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
  let some (.merge oldVars newVars body res) := d.merge | none
  let .app ofn oc := old | none
  let .app nfn nc := new | none
  if ofn == f && nfn == f && oc.length == d.entryWidth && nc.length == d.entryWidth &&
      oc.take d.arity == nc.take d.arity then do
    let os := oc.drop d.arity
    let ns := nc.drop d.arity
    if conflicts d body os ns then do
      let σ := mergeEnv oldVars newVars os ns
      let facts ← actionsFacts sig σ body
      let vs ← Expr.evalList sig res σ
      if vs.length == d.outArity && SourceProof.valuesOk sig vs then
        some ⟨facts, .app f (oc.take d.arity ++ vs)⟩
      else none
    else none
  else none

/-- The root node's justification, against the facts its subproofs state. -/
def checkReason (P : Program) (sig : Signature) : Proof → Bool
  | .global t i => (do
      let .action a ← P[i]? | none
      let facts ← actionFacts sig [] a
      some (decide (t ∈ facts))).getD false
  | .rule t i σ ps => (do
      let .rule r ← P[i]? | none
      let facts ← ruleFacts sig r σ (ps.map Proof.fact)
      some (decide (t ∈ facts))).getD false
  | .merge t f old new => (do
      let facts ← mergeFacts sig f old.fact new.fact
      some (decide (t ∈ facts.body ∨ t ∈ facts.result.subtermList))).getD false
  | .subterm t parent => decide (t ∈ parent.fact.subtermList)

def checkNode (P : Program) (C : SourceProof.Context) (pf : Proof) : Bool :=
  SourceProof.atomOk C.sig pf.fact && checkReason P C.sig pf &&
    match pf with
    | .global t _ => decide ((⟨t, t⟩ : SourceProof.Claim) ∈ C.globals)
    | _ => true

mutual

/-- Every node is valid. -/
def valid (P : Program) (C : SourceProof.Context) : Proof → Bool
  | .global t i => checkNode P C (.global t i)
  | .rule t i σ ps => allValid P C ps && checkNode P C (.rule t i σ ps)
  | .merge t f p q => valid P C p && valid P C q && checkNode P C (.merge t f p q)
  | .subterm t p => valid P C p && checkNode P C (.subterm t p)

def allValid (P : Program) (C : SourceProof.Context) : List Proof → Bool
  | [] => true
  | p :: ps => valid P C p && allValid P C ps

end

/-- Check a proof about the compiled relational program, which has no `union`. This is an
intermediate step: source proofs are checked by `SourceProof.check` against the original
program, unions included. -/
def check (P : Program) (pf : Proof) : Option Term := do
  if !unionFree P then none else do
    let C ← SourceProof.contextOf P
    if valid P C pf then some pf.fact else none

end Egglog.Provenance
