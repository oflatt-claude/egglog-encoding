import EgglogSemantics.Resugar.Query
import EgglogSemantics.Provenance.Extract
import EgglogSemantics.Resugar.Claim

namespace Egglog.Resugar

open SourceProof (Claim Context Proof)

def sourceSubst (vars : List Var) (σ : Env) : Option Env :=
  vars.mapM fun v => (Env.lookup v σ).map (v, ·)

def rebuild (P : Program) (C : Context) (kind : Congruence.RebuildOrigin)
    (ps : List Proof) : Option Proof := do
  let [p, q] := ps | none
  match kind with
  | .compress => trans P C p q
  | .eclass _ => do
    let rev ← symm P C q
    trans P C rev p
  | .child _ k => congr P C p k q

def merge (P : Program) (C : Context) (f : FnName) (old new : Proof)
    (c : Claim) : Option Proof :=
  finish P C old c <|> finish P C new c <|> do
    let p ← match Congruence.tableRole P f with
      | some .unionFind => do
        let rev ← symm P C old
        trans P C rev new
      | some (.view _) => do
        let rev ← symm P C new
        trans P C old rev
      | none => none
    finish P C p c

/-- The proof `k` builds must establish the source claim of the relational fact. -/
def expect (P : Program) (C : Context) (fact : Term) (k : Claim → Option Proof) :
    Option Proof := do
  let c ← factClaim P C fact
  let p ← k c
  if p.claim == c then some p else none

mutual

/-- Lift relational provenance to a source proof of the same fact's claim. -/
def liftProof (P : Program) (C : Context) (compiled : List Congruence.Command) :
    Provenance.Proof → Option Proof
  | .subterm t parent => expect P C t fun c => do
      let p ← liftProof P C compiled parent
      finish P C p c
  | .merge t f old new => expect P C t fun c => do
      let p ← liftProof P C compiled old
      let q ← liftProof P C compiled new
      merge P C f p q c
  | .rule t command σ premises => expect P C t fun c => do
      let tagged ← compiled[command]?
      let origin ← tagged.ruleOrigin
      let ps ← liftAll P C compiled premises
      match origin with
      | .source index => do
        let .rule r ← P[index]? | none
        let σ' ← sourceSubst r.query.vars σ
        let sourcePremises ← query P C σ' r.query ps
        node P C (.rule c index σ' sourcePremises)
      | .rebuild kind => do
        let p ← rebuild P C kind ps
        finish P C p c

def liftAll (P : Program) (C : Context) (compiled : List Congruence.Command) :
    List Provenance.Proof → Option (List Proof)
  | [] => some []
  | p :: ps => do
    let q ← liftProof P C compiled p
    let qs ← liftAll P C compiled ps
    some (q :: qs)

end

/-- Check the relational proof against the compiled program, lift it, and check the
original source claim. -/
def lift (P : Program) (pf : Provenance.Proof) : Option Proof := do
  if !SourceProof.sourceOk P then none else do
    let C ← SourceProof.contextOf P
    let compiled := Congruence.compile P
    let fact ← Provenance.check (compiled.map Congruence.Command.command) pf
    let wanted ← factClaim P C fact
    let result ← liftProof P C compiled pf
    if SourceProof.check P result == some wanted then some result else none

def extractRow (P : Program) (r : Entry) : Option Proof := do
  let intermediate ← Provenance.extractRow (Congruence.encode P) r
  lift P intermediate

end Egglog.Resugar
