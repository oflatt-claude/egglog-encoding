import EgglogSemantics.Spec.Merge
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Proofs.Congruence

/-!
# What M9 has to prove

Most theorems here are *stated* and unproved. Stating them is what pins the design
down; `MERGE.md` says which one buys what.

The load-bearing one is `mcong_toM_iff`: on the image of `Database.toM`, and for an
all-constructors signature, the generalized relation is exactly M2's `Cong`. That is
what makes replacing `Database` by `MDatabase` a refactor rather than a rewrite —
without it every M2–M8 theorem would have to be reproved rather than transported.
-/

namespace Egglog
/-! ### Signatures -/
/-- With `mergeOf` defaulting an undeclared name to `.union`, `AllConstructors` says
exactly that every function is a constructor. This is why "everything up to M8" is
literally the all-constructors case and not merely analogous to it. -/
theorem Signature.mergeOf_eq_union {sig : Signature} (h : sig.AllConstructors)
    (f : FnName) : sig.mergeOf f = MergeSpec.union := by
  unfold Signature.mergeOf
  cases hf : sig f with
  | none => rfl
  | some d => exact h f d hf

/-! ### Structure of the row set under the embedding

`Database.toM` is a structure literal, so its projections reduce; the `simp` lemmas are
for `rw`, which needs them syntactically. -/
@[simp] theorem Database.toM_sig {db : Database} : db.toM.sig = db.sig := rfl
@[simp] theorem Database.toM_terms {db : Database} : db.toM.terms = db.terms := rfl
@[simp] theorem Database.toM_eqs {db : Database} : db.toM.eqs = db.eqs := rfl

/-- The rows the embedding produces are exactly the applications the database holds. -/
theorem Database.toM_row_iff {db : Database} {f : FnName} {as vs : List Term} :
    Row.mk f as vs ∈ db.toM.rows ↔ vs = [.app f as] ∧ Term.app f as ∈ db.terms :=
  Iff.rfl

/-! ### The generalized relation is the old one

Two directions, two hypotheses. `MCong → Cong` holds for any signature, because a row
of the embedding is a constructor row whatever the signature says. `Cong → MCong`
needs `AllConstructors`, which is what licenses `fd`. -/
mutual

/-- Every generalized derivation over the embedding is an M2 derivation.

`fd` is the only interesting case: its two rows come from `Database.toM`, so their
outputs are `.app f as` and `.app f bs` and both applications are in `db.terms` — the
two premises `Cong.congr` wants. -/
theorem MCong.toCong {db : Database} {a b : Term} (h : MCong db.toM a b) :
    Cong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (MCong.toCong h)
  | .trans h₁ h₂ => exact .trans (MCong.toCong h₁) (MCong.toCong h₂)
  | .fd ha hb _ hl hxy =>
    obtain ⟨rfl, hma⟩ := Database.toM_row_iff.mp ha
    obtain ⟨rfl, hmb⟩ := Database.toM_row_iff.mp hb
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact .congr hma hmb (MCongList.toCongList hl)

theorem MCongList.toCongList {db : Database} {as bs : List Term}
    (h : MCongList db.toM as bs) : CongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (MCong.toCong hab) (MCongList.toCongList hl)

end

mutual

/-- Every M2 derivation is a generalized derivation over the embedding.

`congr` is the only interesting case: its two membership premises are exactly what
`Database.toM` needs to produce the two rows `fd` wants, and `Signature.mergeOf_eq_union`
is what lets `fd` fire. -/
theorem Cong.toMCong {db : Database} (hsig : db.sig.AllConstructors) {a b : Term}
    (h : Cong db a b) : MCong db.toM a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (Cong.toMCong hsig h)
  | .trans h₁ h₂ => exact .trans (Cong.toMCong hsig h₁) (Cong.toMCong hsig h₂)
  | .congr (f := f) (as := as) (bs := bs) hma hmb hl =>
    exact .fd (a := [Term.app f as]) (b := [Term.app f bs]) ⟨rfl, hma⟩ ⟨rfl, hmb⟩
      (Signature.mergeOf_eq_union hsig f) (CongList.toMCongList hsig hl) (by simp)

theorem CongList.toMCongList {db : Database} (hsig : db.sig.AllConstructors)
    {as bs : List Term} (h : CongList db as bs) : MCongList db.toM as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (Cong.toMCong hsig hab) (CongList.toMCongList hsig hl)

end

/-- **The compatibility theorem.** On all-constructor signatures the functional
dependency *is* congruence.

This is what `PLAN.md` M9 asks for, and the reason `MCong` has no `congr` constructor:
congruence is not lost, it is `fd` read at constructor rows. -/
theorem mcong_toM_iff {db : Database} (hsig : db.sig.AllConstructors) {a b : Term} :
    MCong db.toM a b ↔ Cong db a b :=
  ⟨MCong.toCong, Cong.toMCong hsig⟩

/-- Congruence, recovered as a derived rule rather than a constructor. Holds in any
`MDatabase` whose functions are constructors, not only in the image of `toM`. -/
theorem MCong.congr {db : MDatabase} {f : FnName} {as bs : List Term}
    (ha : Row.mk f as [.app f as] ∈ db.rows) (hb : Row.mk f bs [.app f bs] ∈ db.rows)
    (hsig : db.sig.mergeOf f = MergeSpec.union) (hl : MCongList db as bs) :
    MCong db (.app f as) (.app f bs) :=
  .fd ha hb hsig hl (by simp)

/-- The rest of M9 collapses too: with no `.merge` function there is no collision to
resolve, so a round is `MRunRules` and nothing else. Companion to `mcong_toM_iff` on
the *step* side — together they say M9 restricted to constructors is M0–M8 unchanged. -/
theorem MergeStep.saturated_of_allConstructors {db : MDatabase}
    (hsig : db.sig.AllConstructors) : MergeSaturated db := by
  intro db' h
  cases h with
  | collide _ _ _ hm _ _ =>
    rw [Signature.mergeOf_eq_union hsig] at hm
    exact absurd hm (by simp)

/-- The least-congruence principle, which is how every negative fact about the closure
gets proved and the shape the M11 checker-soundness argument takes. `Cong.le` with the
`congr` hypothesis replaced by an `fd` one. -/
theorem MCong.le {db : MDatabase} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hfd : ∀ f as bs (a b : List Term) x y, Row.mk f as a ∈ db.rows →
      Row.mk f bs b ∈ db.rows → db.sig.mergeOf f = MergeSpec.union →
      List.Forall₂ R as bs → (x, y) ∈ a.zip b → R x y)
    {a b : Term} (h : MCong db a b) : R a b := by
  sorry

/-! ### Monotonicity

Constraint (3). That a merge *adds* the combined row instead of replacing the two it
combined is exactly what these need. -/
mutual

/-- Adding terms, rows and equalities only adds derivations. `Cong.mono`, with the
`fd` case in place of `congr`. -/
theorem MCong.mono {d₁ d₂ : MDatabase} (h : d₁.Contained d₂) {a b : Term}
    (hc : MCong d₁ a b) : MCong d₂ a b := by
  sorry

theorem MCongList.mono {d₁ d₂ : MDatabase} (h : d₁.Contained d₂) {as bs : List Term}
    (hc : MCongList d₁ as bs) : MCongList d₂ as bs := by
  sorry

end

/-- `Out` is monotone, because both of its conjuncts are. A rule body reading a table
never *loses* a match — the property an overwriting merge would destroy, and the one
seminaive evaluation rests on. -/
theorem MDatabase.Out.mono {d₁ d₂ : MDatabase} (h : d₁.Contained d₂) {f : FnName}
    {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  sorry

/-- A `set` only adds. -/
theorem MDatabase.contained_addRow {db : MDatabase} {f : FnName} {as vs : List Term} :
    db.Contained (db.addRow f as vs) := by
  sorry

/-- Row actions only add, exactly as `evalAction_contained` does for `Action`. -/
theorem MDatabase.RowActionStep.contained {db d : MDatabase} {a : RowAction}
    (h : MDatabase.RowActionStep db a d) : db.Contained d := by
  sorry

theorem MDatabase.RowActionsStep.contained {db d : MDatabase} {as : List RowAction}
    (h : MDatabase.RowActionsStep db as d) : db.Contained d := by
  sorry

/-- **A merge never shrinks the database.**

Constraint (3), discharged by the representation rather than by an argument: the step
adds the combined row beside the two it merged, so there is nothing to overwrite. This
is what lets `MCong.mono`, `Out.mono` and every `WF`-preservation lemma survive into
M9 unchanged. -/
theorem MergeStep.contained {d₁ d₂ : MDatabase} (h : MergeStep d₁ d₂) :
    d₁.Contained d₂ := by
  sorry

theorem MergeClosure.contained {d₁ d₂ : MDatabase} (h : MergeClosure d₁ d₂) :
    d₁.Contained d₂ := by
  sorry

/-- **A vacuous self-collision is the identity step.**

`MergeStep` has no `a ≠ b` guard, so `MCongList`'s reflexivity makes every row collide
with itself. This is what keeps `MergeSaturated` reachable anyway: when the body adds
nothing and returns the output it was given — `ordering-min p p = p`, the union-find's
case — the step re-derives a row already present and `db' = db`. A merge that is *not*
idempotent has no such fixpoint and correctly never saturates, which is the intended
reading rather than a defect (`MERGE.md`, "No guard on the collision"). -/
theorem MergeStep.self_id {db d : MDatabase} {f : FnName} {as a : List Term}
    {body : List RowAction} {res : List Expr} (hw : db.WF) (hrow : Row.mk f as a ∈ db.rows)
    (hsig : db.sig.mergeOf f = MergeSpec.merge body res)
    (hbody : MDatabase.RowActionsStep { db with env := mergeEnv a a } body d)
    (hfix : d.terms = db.terms ∧ d.rows = db.rows ∧ d.eqs = db.eqs)
    (hres : Expr.MEvalList d d.env res a) :
    ({ d.addRow f as a with env := db.env, rules := db.rules } : MDatabase) = db := by
  sorry

/-! ### The observable value

Constraint (3)'s second half. `PLAN.md` proposes a merge-fold and asks for it to be
well defined; `Current` is that value defined as a maximum instead, which needs only
antisymmetry. It is not what `Expr.MEval` reads. -/
/-- The observable value is unique. This is "the fold is well defined", with a fold's
commutativity and associativity obligations replaced by antisymmetry of the order —
see `MERGE.md`, "Why a maximum and not a fold". -/
theorem MDatabase.current_unique {db : MDatabase} {le : List Term → List Term → Prop}
    (hanti : ∀ x y, le x y → le y x → x = y) {f : FnName} {as v w : List Term}
    (hv : db.Current le f as v) (hw : db.Current le f as w) : v = w :=
  hanti _ _ (hw.2 v hv.1) (hv.2 w hw.1)

/-- `Term.blt` is a strict linear order. Needed for `ordering-min`/`ordering-max` to be
a deterministic choice, and for "keep the smaller side" to descend. -/
theorem Term.blt_linear : (∀ s t : Term, Term.blt s t = true → Term.blt t s = false) ∧
    (∀ s t : Term, s ≠ t → Term.blt s t = true ∨ Term.blt t s = true) ∧
    (∀ s t u : Term, Term.blt s t = true → Term.blt t u = true → Term.blt s u = true) := by
  sorry

/-- **A `.union` function's outputs are all congruent.**

The functional dependency, stated as what it buys: however many rows a `.union`
function accumulates at one key class, they are one e-class. For `@UF_<Sort>` this is
"every parent a term ever had is equal to it"; for `@<C>View` it is congruence. -/
theorem MDatabase.Out.union_cong {db : MDatabase} {f : FnName} {as v w : List Term}
    {x y : Term} (hsig : db.sig.mergeOf f = MergeSpec.union) (hv : db.Out f as v)
    (hw : db.Out f as w) (hxy : (x, y) ∈ v.zip w) : MCong db x y := by
  sorry

/-! ### Invariants over the step relation

The shape every M11 safety theorem takes, and the reason termination and confluence are
*not* in the spec: an invariant holds at every reachable state, so a run that diverges
satisfies it throughout and a run that merges in a different order satisfies it too.
"Every proof row the encoding writes is checker-valid" is one of these. -/
/-- Reachable states satisfy any invariant preserved by one command. -/
theorem invariant_of_step {I : MDatabase → Prop}
    (hstep : ∀ db c db', I db → CmdStep db c db' → I db')
    {db db' : MDatabase} {p : MProgram} (hinit : I db) (h : ProgramStep db p db') :
    I db' := by
  induction h with
  | nil => exact hinit
  | cons hc _ ih => exact ih (hstep _ _ _ hinit hc)

/-- **Every command only adds.**

The formal content of "never delete a term row or a proof row", which the encoding
depends on and which the invariant argument needs: anything the checker reads is
positive in the state, so once true it stays true. `.rule` and `.decl` touch only
fields `Contained` ignores. -/
theorem CmdStep.contained {db db' : MDatabase} {c : MCmd} (h : CmdStep db c db') :
    db.Contained db' := by
  sorry

theorem ProgramStep.contained {db db' : MDatabase} {p : MProgram}
    (h : ProgramStep db p db') : db.Contained db' := by
  sorry

/-! ### Determinism

Demoted. Confluence is not needed by any safety theorem — see `invariant_of_step`. It
buys one thing only: strengthening M10's refinement from "the interpreter's result is
spec-reachable" to an equality. -/
/-- A merge that is a `le`-join is locally confluent: two collisions available at once
can be fired in either order and rejoined. **Not known to hold as stated** — a merge
body that writes to a *third* table can plausibly break the diamond even when the value
combiner is a join, since the third table's own merge sees a different pair depending on
the order. `MERGE.md` open question 2. -/
theorem MergeStep.diamond_of_join {db d₁ d₂ : MDatabase}
    {le : List Term → List Term → Prop}
    (hjoin : ∀ f as v w, db.Current le f as v → db.Out f as w → le w v)
    (h₁ : MergeStep db d₁) (h₂ : MergeStep db d₂) :
    ∃ d, MergeClosure d₁ d ∧ MergeClosure d₂ d := by
  sorry

/-- With a confluent merge the *saturated* states of a round coincide, so an
interpreter that runs merges to a fixpoint computes the one answer `RunStep` allows
that egglog also allows. `RunStep` itself stays a relation. -/
theorem RunStep.unique_of_confluent {db d₁ d₂ : MDatabase}
    (hconf : ∀ e e₁ e₂, MergeStep e e₁ → MergeStep e e₂ →
      ∃ e', MergeClosure e₁ e' ∧ MergeClosure e₂ e')
    (hs₁ : MergeSaturated d₁) (hs₂ : MergeSaturated d₂)
    (h₁ : RunStep db d₁) (h₂ : RunStep db d₂) : d₁ = d₂ := by
  sorry

/-! ### The interpreter

`Impl/Merge.lean` runs the M9 semantics. The refinement is weaker than M10's on purpose:
the spec admits several results, so the interpreter's is one of them rather than *the*
one. -/
/-- **The M9 refinement: reachability, not equality.**

`exec_toDatabase` says the constructor interpreter computes exactly `run p`. Here the
spec is a relation, so the statement is that the interpreter lands on a state the spec
reaches. Nothing stronger is available, and nothing stronger is wanted — pinning a
single result would mean pinning the merge order, which is the thing `MERGE.md` argues
the semantics should decline to pin. -/
theorem execM_reachable {p : MProgram} {d : FMDatabase} (h : execM p = some d) :
    ProgramStep FMDatabase.empty.toMDatabase p d.toMDatabase := by
  sorry

/-- The interpreter's merge phase is a *prefix* of the merge closure — one pass, not a
fixpoint. This is what makes `execM_reachable` provable without a termination argument,
and it is only sound because `RunStep` dropped `MergeSaturated`. -/
theorem mergeRound_closure {d : FMDatabase} :
    MergeClosure d.toMDatabase d.mergeRound.toMDatabase := by
  sorry

/-- **The congruence closure needs no `fd` disjunct.**

`MCong.fd` fires only at a `.union` function, and in a database the interpreter builds a
`.union` function's rows are exactly the constructor rows of its terms — the two
hypotheses. So `MCong` coincides with `Cong` on the row-free projection, and
`Impl/Closure.lean`'s `closure` decides it unchanged. This is what licenses
`FMDatabase.closureF` reusing `closureTotal`. -/
theorem FMDatabase.closureF_ok {d : FMDatabase}
    (hrow : ∀ r ∈ d.rows, d.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ d.terms)
    (hterm : ∀ f as, Term.app f as ∈ d.terms → d.sig.mergeOf f = MergeSpec.union →
      Row.mk f as [.app f as] ∈ d.rows)
    {a b : Term} : MCong d.toMDatabase a b ↔ Cong d.toF.toDatabase a b := by
  sorry

/-- **Row counts do not observe the merge phase.**

`rowCount` counts congruence classes of *keys*. A merge step writes its combined row at a
key already present, and a merge with an empty action block writes nothing else, so a
merge pass leaves every count alone.

This is what lets the differential test compare row counts while the interpreter runs
only one merge pass instead of saturating — and it is also why keeping every superseded
output, the over-approximation the design rests on, does not inflate the number: three
recorded values at one key are still one row. Both halves of `PLAN.md`'s row-count oracle
survive into M9 because of it. -/
theorem FMDatabase.mergeRound_rowCount {d : FMDatabase} (f : FnName)
    (hpure : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res → body = []) :
    d.mergeRound.rowCount f = d.rowCount f := by
  sorry

/-! ### Well-formedness -/
theorem MDatabase.WF.addRow {db : MDatabase} (hw : db.WF) {f : FnName}
    {as vs : List Term} : (db.addRow f as vs).WF := by
  sorry

theorem MergeStep.wf {d₁ d₂ : MDatabase} (hw : d₁.WF) (h : MergeStep d₁ d₂) :
    d₂.WF := by
  sorry

end Egglog
