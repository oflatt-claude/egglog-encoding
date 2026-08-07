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
statement is `ProgramStep d.toDatabase p (exec p).toDatabase` — the interpreter's
result is one the spec reaches. `Proofs/Merge.lean` states it.

**The merge phase is not run at all by `exec`.** `mergeRound` fires every collision it
can see once and is structurally terminating; `mergeSaturate` takes a termination
witness rather than fuel. Neither is called by `Impl/Interp.lean`'s `execRunRules`,
which is *sound* precisely because `RunStep` is `MergeClosure` with no `MergeSaturated`
requirement — zero steps is a reachable state. The difftest does not need them either,
for the reason under `rowCount`.

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
namespace FDatabase
/-- Whether two key tuples are congruent. -/
def congrKeys (cl : Finset (Term × Term)) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ cl)

/-- `Database.Out`, computed: every output recorded at a key congruent to `as`. -/
def outs (d : FDatabase) (f : FnName) (as : List Term) : List (List Term) :=
  let cl := d.closureF
  d.rows.filterMap fun r =>
    if r.fn = f && congrKeys cl as r.args then some r.out else none

end FDatabase
/-! ### Evaluation

`Expr.MEval`, computed. The `lookup` case takes the *first* recorded output, which is
the interpreter's pick; the spec allows any. -/
mutual

/-- `Expr.MEval`, computed. -/
def FDatabase.execExpr (d : FDatabase) (σ : Env) : Expr → Option Term
  | .lit l => some (.lit l)
  | .var v => Env.lookup v σ
  | .app f args =>
    (FDatabase.execExprList d σ args).bind fun ts =>
      match Prim.ofName f with
      | some p => p.apply ts
      | none =>
        match d.sig.mergeOf f with
        | .union => some (.app f ts)
        | _ => match d.outs f ts with
               | [v] :: _ => some v
               | _ => none

/-- `execExpr` over an argument list. -/
def FDatabase.execExprList (d : FDatabase) (σ : Env) : List Expr → Option (List Term)
  | [] => some []
  | e :: es => (d.execExpr σ e).bind fun t => (d.execExprList σ es).map (t :: ·)

end

/-! ### Actions -/
/-- `MDatabase.ActionStep`, computed. -/
def FDatabase.execAction (d : FDatabase) : Action → Option FDatabase
  | .expr e => (d.execExpr d.env e).map fun t => d.addTerm t
  | .letBind v e => (d.execExpr d.env e).map fun t =>
      { d.addTerm t with env := (v, t) :: d.env }
  | .union e₁ e₂ => (d.execExpr d.env e₁).bind fun t₁ =>
      (d.execExpr d.env e₂).map fun t₂ => d.addEq t₁ t₂
  | .set f args out => (d.execExprList d.env args).bind fun ts =>
      (d.execExpr d.env out).map fun v => d.addRow f ts [v]

/-- `MDatabase.ActionsStep`, computed. -/
def FDatabase.execActions (d : FDatabase) : List Action → Option FDatabase
  | [] => some d
  | a :: as => (d.execAction a).bind fun d' => d'.execActions as

/-! ### The merge phase -/
/-- One `:merge` firing on a named pair of rows, if it applies. -/
def FDatabase.mergeOne (d : FDatabase) (r₁ r₂ : Row) : Option FDatabase :=
  if r₁.fn = r₂.fn && congrKeys d.closureF r₁.args r₂.args then
    match d.sig.mergeOf r₁.fn with
    | .merge body res =>
      (FDatabase.execActions { d with env := mergeEnv r₁.out r₂.out } body).bind
        fun e => (e.execExprList e.env res).map fun vs =>
          { e.addRow r₁.fn r₁.args vs with env := d.env, rules := d.rules }
    | _ => none
  else none

/-- One pass of the merge phase: every ordered pair of rows, fired once, left to right.

**Not** saturation. Structurally terminating, so it needs neither fuel nor a termination
witness, and sound because `RunStep` is `MergeClosure` with no `MergeSaturated`
requirement — a prefix of the closure is still a reachable state. -/
def FDatabase.mergeRound (d : FDatabase) : FDatabase :=
  d.rows.foldl (fun acc r₁ =>
    acc.rows.foldl (fun acc' r₂ =>
      match acc'.mergeOne r₁ r₂ with
      | some acc'' => acc''
      | none => acc') acc) d

/-! ### Running -/
/-- Whether a merge pass changed anything. Compares the decidable fields; `sig` is a
function and `env`/`rules` a merge cannot touch. -/
def FDatabase.settled (d : FDatabase) : Bool :=
  let e := d.mergeRound
  e.terms == d.terms && e.rows == d.rows && e.eqs == d.eqs

/-- Merge saturation, for the record. Takes a **termination witness**, not fuel: being
undefined for a signature whose merges diverge is what egglog does too, where fuel would
return a half-merged database and present it as an answer. Not used by `execCmd`, which
runs one pass — see `mergeRound`. -/
def FDatabase.MergeRel (x y : FDatabase) : Prop :=
  y.mergeRound = x ∧ ¬ y.settled = true

def FDatabase.mergeSaturate (d : FDatabase) (h : Acc FDatabase.MergeRel d) :
    FDatabase :=
  Acc.rec (motive := fun _ _ => FDatabase)
    (fun x _ ih => if he : x.settled = true then x else ih x.mergeRound ⟨rfl, he⟩) h

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
def FDatabase.keyLists (d : FDatabase) (f : FnName) : List (List Term) :=
  d.rows.filterMap fun r => if r.fn = f then some r.args else none

/-- The number of rows egglog's table for `f` would hold: one per congruence class of
key tuples. Each key is mapped to its whole class and the distinct classes counted, so
no representative has to be chosen.

Generalizes `Impl/Interp.lean`'s `rowCount`, which reads applications out of `terms`.
The two agree on a constructor, since `addTerm` writes one row per application; this one
additionally counts a `:merge` function's table. -/
def FDatabase.keyRowCount (d : FDatabase) (f : FnName) : Nat :=
  let cl := d.closureF
  let keys := (d.keyLists f).toFinset
  (keys.image fun as => keys.filter fun bs => congrKeys cl as bs).card

end Egglog
