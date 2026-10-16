import EgglogSemantics.Provenance.Encode

namespace Egglog.Provenance

inductive ProofKind where
  | rule (command action : Nat)
  | body (function : FnName) (action : Nat)
  | result (function : FnName)
  | subterm

def proofKinds (P : Program) : List (FnName × ProofKind) :=
  (subtermName, .subterm) :: P.zipIdx.flatMap fun ci => match ci.1 with
    | .decl f d => match d.merge with
      | some (.merge _ _ body _) => (resultName f, .result f) ::
          body.zipIdx.map fun aj => (bodyName f aj.2, .body f aj.2)
      | _ => []
    | .rule r => r.actions.zipIdx.map fun aj => (ruleName ci.2 aj.2, .rule ci.2 aj.2)
    | _ => []

/-- Validate a node as it is decoded. -/
def node (P : Program) (sig : Signature) (pf : Proof) : Option Proof :=
  if SourceProof.atomOk sig pf.fact && checkReason P sig pf then some pf else none

def actionRoot (sig : Signature) (σ : Env) : Action → Option Term
  | .expr e => e.evalAtom sig σ
  | .union _ _ => none

def mergeBodyRoot (sig : Signature) (f : FnName) (j : Nat)
    (old new : Term) : Option Term := do
  let d ← sig f
  let some (.merge oldVars newVars body _) := d.merge | none
  let .app _ oc := old | none
  let .app _ nc := new | none
  let a ← body[j]?
  actionRoot sig (mergeEnv oldVars newVars (oc.drop d.arity) (nc.drop d.arity)) a

private theorem sizeOf_tail_le (ts : List Term) : sizeOf ts.tail ≤ sizeOf ts := by
  cases ts with
  | nil => simp
  | cons t ts => simp only [List.tail_cons, List.cons.sizeOf_spec]; omega

private theorem sizeOf_drop_le (n : Nat) (ts : List Term) : sizeOf (ts.drop n) ≤ sizeOf ts := by
  induction ts generalizing n with
  | nil => simp
  | cons t ts ih =>
    cases n with
    | zero => simp
    | succ n =>
      have := ih n
      simp only [List.drop_succ_cons, List.cons.sizeOf_spec]
      omega

mutual

/-- Decode a proof constructor against the uninstrumented program. -/
def decode (P : Program) (sig : Signature) (kinds : List (FnName × ProofKind)) :
    Term → Option Proof
  | .lit _ => none
  | .app f args => do
    let (_, kind) ← kinds.find? (fun kv => kv.1 == f)
    match kind with
    | .rule i j => do
      let .rule r ← P[i]? | none
      let n := r.query.vars.length
      if args.length != n + r.query.length then none else do
        let σ := r.query.vars.zip (args.take n)
        let ps ← decodeAll P sig kinds (args.drop n)
        let a ← r.actions[j]?
        let fact ← actionRoot sig σ a
        node P sig (.rule fact i σ ps)
    | .body fn j => do
      let [old, new] ← decodeAll P sig kinds args | none
      let fact ← mergeBodyRoot sig fn j old.fact new.fact
      node P sig (.merge fact fn old new)
    | .result fn => do
      let [old, new] ← decodeAll P sig kinds args | none
      let fs ← mergeFacts sig fn old.fact new.fact
      node P sig (.merge fs.result fn old new)
    | .subterm => do
      let fact ← args[0]?
      let [p] ← decodeAll P sig kinds args.tail | none
      node P sig (.subterm fact p)
termination_by t => sizeOf t
decreasing_by all_goals
  simp_wf
  all_goals first
    | omega
    | exact Nat.lt_of_le_of_lt (sizeOf_drop_le _ _) (by omega)
    | exact Nat.lt_of_le_of_lt (sizeOf_tail_le _) (by omega)

def decodeAll (P : Program) (sig : Signature) (kinds : List (FnName × ProofKind)) :
    List Term → Option (List Proof)
  | [] => some []
  | t :: ts => do
    let p ← decode P sig kinds t
    let ps ← decodeAll P sig kinds ts
    some (p :: ps)
termination_by ts => sizeOf ts
decreasing_by all_goals (simp_wf; omega)

end

def extract (P : Program) (pf : Term) : Option Proof := do
  let C ← SourceProof.contextOf P
  if !programOk P C.sig then none else do
    let p ← decode P C.sig (proofKinds P) pf
    if (check P p).isSome then some p else none

/-- The selected proof must establish exactly the row's original data columns. -/
def extractRow (P : Program) (r : Entry) : Option Proof := do
  let C ← SourceProof.contextOf P
  let d ← C.sig r.name
  if d.merge.isNone || r.key.length != d.arity || r.value.length != d.outArity + 1 then
    none
  else do
    let pf ← r.value[d.outArity]?
    let p ← extract P pf
    if check P p == some (.app r.name (r.key ++ r.value.take d.outArity)) then
      some p
    else none

def eraseRow (sig : Signature) (r : Entry) : Option Entry := do
  let d ← sig r.name
  if d.merge.isSome then some { r with value := r.value.take d.outArity }
  else some r

def eraseFact (sig : Signature) (t : Term) : Option Term := do
  if SourceProof.valueOk sig t then some t else do
    let .app f cols := t | none
    let d ← sig f
    if d.merge.isSome && cols.length == d.entryWidth + 1 then
      some (.app f (cols.take d.entryWidth))
    else none

def retainedRows (sig : Signature) (terms : List Term) : List Entry :=
  terms.filterMap fun t => do
    let .app f cols := t | none
    let d ← sig f
    if d.merge.isSome && cols.length == d.entryWidth + 1 then
      some ⟨f, cols.take d.arity, cols.drop d.arity⟩
    else none

end Egglog.Provenance
