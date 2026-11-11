import EgglogSemantics.Provenance.Encode

/-! Reconstruct proofs from a firing log. A firing with justified equality premises and
satisfied disequalities proves the terms its build actions produce, including subterms.
`proofs` returns checked proofs for every data row, or fails if any is unavailable. -/

namespace Egglog.Provenance

/-- Decode logged rule indices and substitutions in reverse input order, skipping invalid
indices and argument counts. For the interpreter's newest-first term list, this is the
order in which firings were recorded. -/
def firings (P : Program) (terms : List Term) : List (Nat × Env) :=
  terms.reverse.filterMap fun t => match t with
    | .app f args => do
        let i ← fireIndex f
        let r ← P.rules[i]?
        if args.length == r.query.vars.length then some (i, r.query.vars.zip args) else none
    | .lit _ => none

/-- Proofs by the term they prove. -/
abbrev Facts := List (Term × Proof)

/-- The proofs of a query's premises under `σ`, one per equality pattern: of a row's
instance, or of the common value of an equality. A disequality has no proof and only has to
hold. -/
def premiseProofs (facts : Facts) (σ : Env) : Query → Option (List Proof)
  | [] => some []
  | .expr e :: ps => do
      let p ← facts.lookup (← e.eval σ)
      some (p :: (← premiseProofs facts σ ps))
  | .eq a b :: ps => do
      let x ← a.eval σ
      let y ← b.eval σ
      if x != y then none else
      let p ← facts.lookup x
      some (p :: (← premiseProofs facts σ ps))
  | .ne a b :: ps => do
      let x ← a.eval σ
      let y ← b.eval σ
      if x == y then none else premiseProofs facts σ ps

/-- The terms a firing proves once its premises have proofs: every subterm of every row it
writes, by a rule node stating that term's reflexivity. -/
def justify (P : Program) (facts : Facts) (i : Nat) (σ : Env) : Option Facts := do
  let r ← P.rules[i]?
  let ps ← premiseProofs facts σ r.query
  some <| r.actions.flatMap fun a => match a with
    | .expr e => match e.eval σ with
      | some t => t.subtermList.map fun s => (s, .rule ⟨s, s⟩ i σ ps)
      | none => []
    | _ => []

/-- Justify the first available pending firing at each step and append its facts.
Stop when fuel is exhausted or no pending firing can be justified. -/
def reconstruct (P : Program) : Nat → Facts → List (Nat × Env) → Facts
  | 0, facts, _ => facts
  | n + 1, facts, pending =>
    match pending.findSome? fun f => (justify P facts f.1 f.2).map (f, ·) with
    | none => facts
    | some (f, new) => reconstruct P n (facts ++ new) (pending.erase f)

/-- The rows of the program among the held terms. -/
def dataRows (P : Program) (terms : List Term) : List Term :=
  let heads := rowHeads P
  terms.filter fun t => match t with
    | .app f _ => heads.contains f
    | .lit _ => false

/-- A row of the firing log: an application of a name with the log prefix. -/
def isLog : Term → Bool
  | .app f _ => firePrefix.isPrefixOf f
  | .lit _ => false

/-- The held terms without the log. -/
def eraseLog (terms : List Term) : List Term := terms.filter fun t => !isLog t

/-- Remove equations whose left endpoint is a log row, retaining subsumed rows.
For an instrumented execution satisfying `ExtlogTheorems.provenance_pass_correct`, the
result has the original program's final meaning. -/
def _root_.Egglog.Database.eraseLog (d : Database) : Database :=
  ⟨{q ∈ d.eqs | isLog q.1 = false}, d.subsumed⟩

/-- Every row with its checked proof from the log, or `none` where no proof checks. -/
def rowProofs (P : Program) (terms : List Term) : List (Term × Option Proof) :=
  let fs := firings P terms
  let facts := reconstruct P fs.length [] fs
  (dataRows P terms).map fun t =>
    (t, (facts.lookup t).bind fun pf => if check P pf == some t then some pf else none)

/-- A checked proof for every data row, using rule nodes justified by logged firings
(the paper's `L ⊢ π : c`). Return `none` if `programOk` fails or any row lacks a checked
proof. -/
@[blueprint "def:log-proofs"
  (statement := /--
  \begin{mathpar}
  \ir{Fire}{\mathtt{fire}_i(\sigma(x_1),\ldots,\sigma(x_n))\in L\\
    L\vdash\pi_j:c_j\ (\forall j)\\
    P'\vdash\kw{rule}_i(c,\sigma;\pi_1,\ldots,\pi_m):c}
    {L\vdash\kw{rule}_i(c,\sigma;\pi_1,\ldots,\pi_m):c}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def proofs (P : Program) (terms : List Term) : Option (List (Term × Proof)) := do
  if !programOk P then none else
    (rowProofs P terms).mapM fun tp => tp.2.map (tp.1, ·)

end Egglog.Provenance
