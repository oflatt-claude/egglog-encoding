import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Impl.Interp

namespace Egglog.Provenance

inductive ProofKind where
  | global (command : Nat)
  | rule (command action : Nat)
  | body (function : FnName) (action : Nat)
  | result (function : FnName)
  | subterm

def proofKinds (P : Program) : List (FnName × ProofKind) :=
  (subtermName, .subterm) :: P.zipIdx.flatMap fun ci => match ci.1 with
    | .decl f d => match d.merge with
      | some (.merge body _) => (resultName f, .result f) ::
          body.zipIdx.map fun aj => (bodyName f aj.2, .body f aj.2)
      | _ => []
    | .action _ => [(globalName ci.2, .global ci.2)]
    | .rule r => r.actions.zipIdx.map fun aj => (ruleName ci.2 aj.2, .rule ci.2 aj.2)
    | _ => []

structure Builder where
  nodes : List Node := []
  cache : List (Term × Nat) := []

def Builder.facts (b : Builder) : List Term := b.nodes.map Node.fact

def Builder.add (P : Program) (sig : Signature) (b : Builder) (pf : Term)
    (fact : Term) (reason : Reason) : Option (Nat × Builder) := do
  let node : Node := ⟨fact, reason⟩
  if !SourceProof.atomOk sig fact || !checkReason P sig b.facts node then none else
    some (b.nodes.length, ⟨b.nodes ++ [node], (pf, b.nodes.length) :: b.cache⟩)

def actionRoot (sig : Signature) (σ : Env) : Action → Option Term
  | .expr e => e.evalAtom sig σ
  | .union _ _ => none

def mergeBodyRoot (sig : Signature) (f : FnName) (j : Nat)
    (old new : Term) : Option Term := do
  let d ← sig f
  let some (.merge body _) := d.merge | none
  let .app _ oc := old | none
  let .app _ nc := new | none
  let a ← body[j]?
  actionRoot sig (mergeEnv (oc.drop d.arity) (nc.drop d.arity)) a

/-- Decode proof constructors against the uninstrumented program, sharing repeated nodes. -/
def decode (P : Program) (sig : Signature) (kinds : List (FnName × ProofKind)) :
    Nat → Term → Builder → Option (Nat × Builder)
  | 0, _, _ => none
  | fuel + 1, pf, b => do
    if let some hit := b.cache.find? (fun kv => kv.1 == pf) then some (hit.2, b) else do
      let .app f args := pf | none
      let (_, kind) ← kinds.find? (fun kv => kv.1 == f)
      match kind with
      | .global i =>
        if !args.isEmpty then none else do
          let .action a ← P[i]? | none
          let fact ← actionRoot sig [] a
          b.add P sig pf fact (.global i)
      | .rule i j => do
        let .rule r ← P[i]? | none
        if args.length != r.query.vars.length + r.query.length then none else do
          let σ := r.query.vars.zip (args.take r.query.vars.length)
          let (ps, b') ← (args.drop r.query.vars.length).foldlM
            (fun (state : List Nat × Builder) p => do
              let (id, next) ← decode P sig kinds fuel p state.2
              some (state.1 ++ [id], next)) ([], b)
          let a ← r.actions[j]?
          let fact ← actionRoot sig σ a
          b'.add P sig pf fact (.rule i σ ps)
      | .body fn _ | .result fn => do
        let [op, np] := args | none
        let (oi, b') ← decode P sig kinds fuel op b
        let (ni, b'') ← decode P sig kinds fuel np b'
        let old ← b''.facts[oi]?
        let new ← b''.facts[ni]?
        let fs ← mergeFacts sig fn old new
        let fact ← match kind with
          | .body _ j => mergeBodyRoot sig fn j old new
          | _ => some fs.result
        b''.add P sig pf fact (.merge fn oi ni)
      | .subterm => do
        let [fact, parent] := args | none
        let (i, b') ← decode P sig kinds fuel parent b
        b'.add P sig pf fact (.subterm i)

def extract (P : Program) (pf : Term) (fuel : Nat := 1024) : Option Certificate := do
  let C ← SourceProof.contextOf P
  if !programOk P C.sig then none else do
    let (root, b) ← decode P C.sig (proofKinds P) fuel pf {}
    let cert : Certificate := ⟨b.nodes, root⟩
    if (check P cert).isSome then some cert else none

/-- The selected proof must establish exactly the row's original data columns. -/
def extractRow (P : Program) (r : Row) (fuel : Nat := 1024) : Option Certificate := do
  let C ← SourceProof.contextOf P
  let d ← C.sig r.fn
  if d.merge.isNone || r.args.length != d.arity || r.out.length != d.outArity + 1 then
    none
  else do
    let pf ← r.out[d.outArity]?
    let cert ← extract P pf fuel
    if check P cert == some (.app r.fn (r.args ++ r.out.take d.outArity)) then
      some cert
    else none

def eraseRow (sig : Signature) (r : Row) : Option Row := do
  let d ← sig r.fn
  if d.merge.isSome then some { r with out := r.out.take d.outArity }
  else some r

def eraseFact (sig : Signature) (t : Term) : Option Term := do
  if SourceProof.valueOk sig t then some t else do
    let .app f cols := t | none
    let d ← sig f
    if d.merge.isSome && cols.length == d.entryWidth + 1 then
      some (.app f (cols.take d.entryWidth))
    else none

def retainedRows (sig : Signature) (terms : List Term) : List Row :=
  terms.filterMap fun t => do
    let .app f cols := t | none
    let d ← sig f
    if d.merge.isSome && cols.length == d.entryWidth + 1 then
      some ⟨f, cols.take d.arity, cols.drop d.arity⟩
    else none

end Egglog.Provenance
