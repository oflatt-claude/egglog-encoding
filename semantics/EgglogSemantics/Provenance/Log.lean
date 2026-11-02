import EgglogSemantics.Provenance.Encode

/-! The firing log and the proofs read off it. A logged firing is justified once every
premise has a proof; it then proves every row it wrote and every subterm of one, by a rule
node stating that term's reflexivity. Justifying firings until none is left that can be
finds a proof for every row that has one. -/

namespace Egglog.Provenance

/-- The firings the held terms record, a rule index and its substitution each, in the order
they were written: the interpreter keeps its newest term first. Justifying them in this
order credits every term to the firing that built it, since a maintenance row only mentions
terms that exist already. -/
def firings (P : Program) (terms : List Term) : List (Nat × Env) :=
  terms.reverse.filterMap fun t => match t with
    | .app f args => do
        let i ← fireIndex f
        let r ← P.rules[i]?
        if args.length == r.query.vars.length then some (i, r.query.vars.zip args) else none
    | .lit _ => none

/-- Proofs by the term they prove. -/
abbrev Facts := List (Term × Proof)

/-- The proof of a premise under `σ`: of a row's instance, of the common value of an
equality, or of the left side of a disequality. -/
def premiseProof (facts : Facts) (σ : Env) : Pattern → Option Proof
  | .expr e => do facts.lookup (← e.eval σ)
  | .eq a b => do
      let x ← a.eval σ
      let y ← b.eval σ
      if x == y then facts.lookup x else none
  | .ne a b => do
      let x ← a.eval σ
      let y ← b.eval σ
      if x == y then none else facts.lookup x

/-- The terms a firing proves once its premises have proofs: every subterm of every row it
writes, by a rule node stating that term's reflexivity. -/
def justify (P : Program) (facts : Facts) (i : Nat) (σ : Env) : Option Facts := do
  let r ← P.rules[i]?
  let ps ← r.query.mapM (premiseProof facts σ)
  some <| r.actions.flatMap fun a => match a with
    | .expr e => match e.eval σ with
      | some t => t.subtermList.map fun s => (s, .rule ⟨s, s⟩ i σ ps)
      | none => []
    | _ => []

/-- Justify the pending firings one at a time until none can be. -/
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

/-- The held terms without the log. -/
def eraseLog (terms : List Term) : List Term :=
  terms.filter fun t => match t with
    | .app f _ => (fireIndex f).isNone
    | .lit _ => true

/-- Every row with its checked proof from the log, or `none` where no proof checks. -/
def rowProofs (P : Program) (terms : List Term) : List (Term × Option Proof) :=
  let fs := firings P terms
  let facts := reconstruct P fs.length [] fs
  (dataRows P terms).map fun t =>
    (t, (facts.lookup t).bind fun pf => if check P pf == some t then some pf else none)

/-- A checked proof of every row, read off the log `L` of the instrumented run. The proofs
are the derivations of the checker's rule case whose firings are logged, `L ⊢ π : c`;
`reconstruct` finds one per row by justifying firings in order. -/
@[blueprint "def:log-proofs"
  (statement := /--
  \begin{mathpar}
  \ir{Fire}{\mathtt{fire}_i(\sigma(x_1),\ldots,\sigma(x_n))\in L\\
    r_i=(p_1\land\cdots\land p_m\Rightarrow H)\\
    L\vdash\pi_j:c_j\quad c_j\in\operatorname{premises}_\sigma(p_j)\ (\forall j)\\
    c\in\operatorname{facts}_\sigma(H)}
    {L\vdash\kw{rule}_i(c,\sigma;\pi_1,\ldots,\pi_m):c}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def proofs (P : Program) (terms : List Term) : Option (List (Term × Proof)) := do
  if !programOk P then none else
    (rowProofs P terms).mapM fun tp => tp.2.map (tp.1, ·)

end Egglog.Provenance
