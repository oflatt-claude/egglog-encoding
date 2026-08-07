import EgglogSemantics.Impl.Interp
import EgglogSemantics.Spec.Merge

/-!
# An executable interpreter for the M9 semantics

`Impl/Interp.lean` runs the constructor-only fragment. This runs `Spec/Merge.lean`, so
that `:merge` programs can be differentially tested against egglog — which is the only
check that M9's design matches the real system rather than matching itself.

Three things differ from `Impl/Interp.lean`, all forced by the spec being *relational*.

**The refinement weakens to reachability.** `exec_toDatabase` says the constructor
interpreter computes exactly the spec's answer. Here the spec admits several, so the
statement is `ProgramStep d.toMDatabase p (execM p).toMDatabase` — the interpreter's
result is one the spec reaches. `Proofs/Merge.lean` states it.

**The merge phase is one pass, not a fixpoint.** `mergeRound` fires every collision it
can see once. It is structurally terminating, so no fuel and no accessibility argument,
and it is *sound* precisely because `RunStep` is `MergeClosure` without `MergeSaturated`
— any number of steps is reachable, including few. `mergeSaturate` (the real thing,
with a termination witness) is what a simulation theorem would need; the difftest does
not, for the reason under `rowCount`.

**A lookup has to pick.** `Expr.MEval`'s `lookup` reads any recorded output; `execExpr`
takes the first. `MERGE.md`, "Why the reader over-approximates", is why the spec does
not pin this and why an interpreter must.

The congruence closure is *unchanged*. `MCong.fd` fires only at `.union` functions, and
a `.union` function's rows are exactly the constructor rows `Impl/Closure.lean` already
sees through `terms`; a `:merge` function's rows contribute nothing to `MCong`. So
`closureF` needs no `fd` disjunct as long as every declared function is `.merge` or
`.noMerge`, which is `Proofs/Merge.lean`'s `closureF_ok`.
-/

namespace Egglog
/-! ### Finite M9 databases -/
/-- The executable counterpart of `MDatabase`. `List`s, for `FDatabase`'s reason:
`Finset.toList` is noncomputable, so nothing that must enumerate can be compiled. -/
structure FMDatabase where
  sig : Signature
  terms : List Term
  rows : List Row
  eqs : List (Term × Term)
  env : Env
  rules : List MRule

namespace FMDatabase
/-- The spec database an `FMDatabase` denotes. -/
def toMDatabase (d : FMDatabase) : MDatabase where
  sig := d.sig
  terms := {t | t ∈ d.terms}
  rows := {r | r ∈ d.rows}
  eqs := {p | p ∈ d.eqs}
  env := d.env
  rules := {r | r ∈ d.rules}

/-- The initial database. -/
def empty : FMDatabase where
  sig := fun _ => none
  terms := []
  rows := []
  eqs := []
  env := []
  rules := []

/-- The constructor rows of `t`, computed: one per application among its subterms. -/
def ctorRowsL (t : Term) : List Row :=
  t.subtermList.filterMap fun s =>
    match s with
    | .app f as => some ⟨f, as, [.app f as]⟩
    | .lit _ => none

/-- Build `t`: insert it, its subterms, and their constructor rows. Deduplicated, for
`FDatabase.addTerm`'s reason — a round's union copies every operand. -/
def build (t : Term) (d : FMDatabase) : FMDatabase :=
  { d with terms := (t.subtermList ++ d.terms).dedup,
           rows := (ctorRowsL t ++ d.rows).dedup }

/-- `build` over a list. -/
def buildAll (ts : List Term) (d : FMDatabase) : FMDatabase :=
  ts.foldl (fun e t => e.build t) d

/-- `(set (f as…) vs)`: build the operands, then assert the row. -/
def addRow (f : FnName) (as vs : List Term) (d : FMDatabase) : FMDatabase :=
  let d := (d.buildAll as).buildAll vs
  { d with rows := (⟨f, as, vs⟩ :: d.rows).dedup }

/-- Assert `a = b`, building both. -/
def addEq (a b : Term) (d : FMDatabase) : FMDatabase :=
  let d := (d.build a).build b
  { d with eqs := ((a, b) :: d.eqs).dedup }

/-- Union two databases, taking sig, env and rules from the left. -/
def union (d₁ d₂ : FMDatabase) : FMDatabase :=
  { d₁ with terms := (d₁.terms ++ d₂.terms).dedup,
            rows := (d₁.rows ++ d₂.rows).dedup,
            eqs := (d₁.eqs ++ d₂.eqs).dedup }

/-- `terms` as a `Finset`. -/
def termsF (d : FMDatabase) : Finset Term := d.terms.toFinset

/-- The congruence closure of `d`, computed. Unchanged from `Impl/Interp.lean`: see the
module docstring for why `rows` need not enter it. -/
def closureF (d : FMDatabase) : Finset (Term × Term) :=
  closureTotal d.termsF d.eqs.toFinset

/-- Whether two key tuples are congruent. -/
def congrKeys (cl : Finset (Term × Term)) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ cl)

/-- `MDatabase.Out`, computed: every output recorded at a key congruent to `as`. -/
def outs (d : FMDatabase) (f : FnName) (as : List Term) : List (List Term) :=
  let cl := d.closureF
  d.rows.filterMap fun r =>
    if r.fn = f && congrKeys cl as r.args then some r.out else none

end FMDatabase
/-! ### Evaluation

`Expr.MEval`, computed. The `lookup` case takes the *first* recorded output, which is
the interpreter's pick; the spec allows any. -/
mutual

/-- `Expr.MEval`, computed. -/
def FMDatabase.execExpr (d : FMDatabase) (σ : Env) : Expr → Option Term
  | .lit l => some (.lit l)
  | .var v => Env.lookup v σ
  | .app f args =>
    (FMDatabase.execExprList d σ args).bind fun ts =>
      match Prim.ofName f with
      | some p => p.apply ts
      | none =>
        match d.sig.mergeOf f with
        | .union => some (.app f ts)
        | _ => match d.outs f ts with
               | [v] :: _ => some v
               | _ => none

/-- `execExpr` over an argument list. -/
def FMDatabase.execExprList (d : FMDatabase) (σ : Env) : List Expr → Option (List Term)
  | [] => some []
  | e :: es => (d.execExpr σ e).bind fun t => (d.execExprList σ es).map (t :: ·)

end

/-! ### Actions -/
/-- `MDatabase.RowActionStep`, computed. -/
def FMDatabase.execRowAction (d : FMDatabase) : RowAction → Option FMDatabase
  | .expr e => (d.execExpr d.env e).map fun t => d.build t
  | .letBind v e => (d.execExpr d.env e).map fun t =>
      { d.build t with env := (v, t) :: d.env }
  | .union e₁ e₂ => (d.execExpr d.env e₁).bind fun t₁ =>
      (d.execExpr d.env e₂).map fun t₂ => d.addEq t₁ t₂
  | .set f args out => (d.execExprList d.env args).bind fun ts =>
      (d.execExpr d.env out).map fun v => d.addRow f ts [v]

/-- `MDatabase.RowActionsStep`, computed. -/
def FMDatabase.execRowActions (d : FMDatabase) : List RowAction → Option FMDatabase
  | [] => some d
  | a :: as => (d.execRowAction a).bind fun d' => d'.execRowActions as

/-! ### The merge phase -/
/-- One `:merge` firing on a named pair of rows, if it applies. -/
def FMDatabase.mergeOne (d : FMDatabase) (r₁ r₂ : Row) : Option FMDatabase :=
  if r₁.fn = r₂.fn && congrKeys d.closureF r₁.args r₂.args then
    match d.sig.mergeOf r₁.fn with
    | .merge body res =>
      (FMDatabase.execRowActions { d with env := mergeEnv r₁.out r₂.out } body).bind
        fun e => (e.execExprList e.env res).map fun vs =>
          { e.addRow r₁.fn r₁.args vs with env := d.env, rules := d.rules }
    | _ => none
  else none

/-- One pass of the merge phase: every ordered pair of rows, fired once, left to right.

**Not** saturation. Structurally terminating, so it needs neither fuel nor a termination
witness, and sound because `RunStep` is `MergeClosure` with no `MergeSaturated`
requirement — a prefix of the closure is still a reachable state. `mergeSaturate` below
is the real thing and is not what the interpreter runs. -/
def FMDatabase.mergeRound (d : FMDatabase) : FMDatabase :=
  d.rows.foldl (fun acc r₁ =>
    acc.rows.foldl (fun acc' r₂ =>
      match acc'.mergeOne r₁ r₂ with
      | some acc'' => acc''
      | none => acc') acc) d

/-! ### Running -/
/-- The substitutions satisfying a query, over an `FMDatabase`.

Reuses `Impl/Interp.lean`'s enumerator by projecting onto an `FDatabase`. That is exact
while patterns mention no `:merge` function — the projection drops `rows`, and `MCong`
reads a row only at a `.union` function. The difftest's fragment stays inside that;
`MERGE.md` records it. -/
def FMDatabase.toF (d : FMDatabase) : FDatabase where
  sig := d.sig
  terms := d.terms
  eqs := d.eqs
  env := d.env
  rules := []

/-- One firing of `r` on `σ`, unioned into `acc`. -/
def FMDatabase.fireInto (d : FMDatabase) (r : MRule) (acc : FMDatabase) (σ : Env) :
    FMDatabase :=
  match (FMDatabase.execRowActions { d with env := d.env ++ σ } r.actions) with
  | some d' => acc.union { d' with env := d.env, rules := d.rules }
  | none => acc

/-- Every firing of `r`, unioned into `acc`. -/
def FMDatabase.fireRule (d : FMDatabase) (acc : FMDatabase) (r : MRule) : FMDatabase :=
  (matchQuery d.toF r.query).foldl (FMDatabase.fireInto d r) acc

/-- One round: fire every rule off the pre-state, then one merge pass. -/
def FMDatabase.execRunRules (d : FMDatabase) : FMDatabase :=
  (d.rules.foldl (FMDatabase.fireRule d) d).mergeRound

/-- Whether a merge pass changed anything. Compares the decidable fields; `sig` is a
function and `env`/`rules` a merge cannot touch. -/
def FMDatabase.settled (d : FMDatabase) : Bool :=
  let e := d.mergeRound
  e.terms == d.terms && e.rows == d.rows && e.eqs == d.eqs

/-- Merge saturation, for the record. Takes a **termination witness**, not fuel: being
undefined for a signature whose merges diverge is what egglog does too, where fuel would
return a half-merged database and present it as an answer. Not used by `execCmd`, which
runs one pass — see `mergeRound`. -/
def FMDatabase.MergeRel (x y : FMDatabase) : Prop :=
  y.mergeRound = x ∧ ¬ y.settled = true

def FMDatabase.mergeSaturate (d : FMDatabase) (h : Acc FMDatabase.MergeRel d) :
    FMDatabase :=
  Acc.rec (motive := fun _ _ => FMDatabase)
    (fun x _ ih => if he : x.settled = true then x else ih x.mergeRound ⟨rfl, he⟩) h

/-- `CmdStep`, computed. -/
def FMDatabase.execCmd (d : FMDatabase) : MCmd → Option FMDatabase
  | .action a => d.execRowAction a
  | .rule r => some { d with rules := r :: d.rules }
  | .run => some d.execRunRules
  | .decl f dc => some { d with sig := Function.update d.sig f (some dc) }

/-- `ProgramStep`, computed. -/
def FMDatabase.execProgram (d : FMDatabase) : MProgram → Option FMDatabase
  | [] => some d
  | c :: cs => (d.execCmd c).bind fun d' => d'.execProgram cs

/-- Run an M9 program from the initial database. -/
def execM (p : MProgram) : Option FMDatabase := FMDatabase.empty.execProgram p

/-! ### Row counts

`(print-size)` reports one row per distinct *canonical key tuple*, so this counts
congruence classes of keys — not rows and not values.

That is what makes the difftest work without the interpreter saturating merges. A merge
step writes its combined row at a key that is already present, so it adds no key class;
a merge with an empty action block adds no row anywhere else either. The count is
therefore invariant under the merge phase, which `Proofs/Merge.lean`'s
`mergeOne_rowCount` states. It is also why keeping every superseded output — the
over-approximation the whole design rests on — does not inflate the number: three
recorded values at one key are still one row. -/
/-- The key tuples of `d`'s `f`-rows. -/
def FMDatabase.keyLists (d : FMDatabase) (f : FnName) : List (List Term) :=
  d.rows.filterMap fun r => if r.fn = f then some r.args else none

/-- The number of rows egglog's table for `f` would hold: one per congruence class of
key tuples. Each key is mapped to its whole class and the distinct classes counted, so
no representative has to be chosen. -/
def FMDatabase.rowCount (d : FMDatabase) (f : FnName) : Nat :=
  let cl := d.closureF
  let keys := (d.keyLists f).toFinset
  (keys.image fun as => keys.filter fun bs => congrKeys cl as bs).card

end Egglog
