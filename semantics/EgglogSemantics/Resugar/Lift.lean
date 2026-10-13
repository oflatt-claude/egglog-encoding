import EgglogSemantics.Resugar.Query
import EgglogSemantics.Provenance.Extract
import EgglogSemantics.Congruence.Encode

namespace Egglog.Resugar

open SourceProof (Claim Context Certificate)

/-- A view relates its id to its constructor application; UF records an equality. -/
def factClaim (P : Program) (C : Context) (t : Term) : Option Claim := do
  if SourceProof.valueOk C.sig t then some ⟨t, t⟩ else do
    let .app f cols := t | none
    match Congruence.tableRole P f with
    | some .unionFind =>
      let [a, b] := cols | none
      some ⟨a, b⟩
    | some (.view ctor) => do
      let d ← C.sig ctor
      if cols.length != d.arity + 1 then none else do
        let id ← cols[d.arity]?
        some ⟨id, .app ctor (cols.take d.arity)⟩
    | none => none

def sourceSubst (vars : List Var) (σ : Env) : Option Env :=
  vars.mapM fun v => (Env.lookup v σ).map (v, ·)

def rebuild (P : Program) (C : Context) (kind : Congruence.RebuildOrigin)
    (ps : List Nat) (b : Builder) : Option (Nat × Builder) := do
  let [i, j] := ps | none
  match kind with
  | .compress => b.trans P C i j
  | .eclass _ => do
    let (rev, b) ← b.symm P C j
    b.trans P C rev i
  | .child _ k => b.congr P C i k j

def merge (P : Program) (C : Context) (f : FnName) (old new : Nat)
    (c : Claim) (b : Builder) : Option (Nat × Builder) :=
  b.finish P C old c <|> b.finish P C new c <|> do
    let (i, b) ← match Congruence.tableRole P f with
      | some .unionFind => do
        let (rev, b) ← b.symm P C old
        b.trans P C rev new
      | some (.view _) => do
        let (rev, b) ← b.symm P C new
        b.trans P C old rev
      | none => none
    b.finish P C i c

def liftNode (P : Program) (C : Context) (compiled : List Congruence.Command)
    (prior : List Nat) (b : Builder) (n : Provenance.Node) : Option (Nat × Builder) := do
  let c ← factClaim P C n.fact
  match n.reason with
  | .global _ => b.add P C c .fiat
  | .subterm parent => do
    let i ← prior[parent]?
    b.finish P C i c
  | .merge f old new => do
    let i ← prior[old]?
    let j ← prior[new]?
    merge P C f i j c b
  | .rule command σ premises => do
    let tagged ← compiled[command]?
    let origin ← tagged.ruleOrigin
    let ps ← premises.mapM fun i => prior[i]?
    match origin with
    | .source index => do
      let .rule r ← P[index]? | none
      let σ' ← sourceSubst r.query.vars σ
      let (sourcePremises, b) ← query P C σ' r.query ps b
      b.add P C c (.rule index σ' sourcePremises)
    | .rebuild kind => do
      let (i, b) ← rebuild P C kind ps b
      b.finish P C i c

/-- Check the relational certificate, lift its DAG, and check the original source claim. -/
def lift (P : Program) (cert : Provenance.Certificate) : Option Certificate := do
  if !SourceProof.sourceOk P then none else do
    let C ← SourceProof.contextOf P
    let compiled := Congruence.compile P
    let fact ← Provenance.check (compiled.map Congruence.Command.command) cert
    let wanted ← factClaim P C fact
    let (ids, b) ← cert.nodes.foldlM (fun (state : List Nat × Builder) n => do
      let (i, next) ← liftNode P C compiled state.1 state.2 n
      let expected ← factClaim P C n.fact
      if next.claims[i]? != some expected then none else
        some (state.1 ++ [i], next)) ([], {})
    let root ← ids[cert.root]?
    let result : Certificate := ⟨b.nodes, root⟩
    if SourceProof.check P result == some wanted then some result else none

def extractRow (P : Program) (r : Row) (fuel : Nat := 1024) : Option Certificate := do
  let intermediate ← Provenance.extractRow (Congruence.encode P) r fuel
  lift P intermediate

/-- Run the instrumented compilation of `P` with `exec` and lift every retained row. -/
def certificates (exec : Program → Option FDatabase) (P : Program) :
    Option (List Certificate) := do
  let target := Congruence.encode P
  let C ← SourceProof.contextOf target
  let annotated ← Provenance.encode target
  let d ← exec annotated
  (Provenance.retainedRows C.sig d.terms).mapM (extractRow P ·)

end Egglog.Resugar
