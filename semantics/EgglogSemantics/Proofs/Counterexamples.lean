import EgglogSemantics.Proofs.Merge

/-!
# Machine-checked falsity witnesses for `Proofs/Merge.lean`'s refinement chain

Three defects, each with a concrete compiling counterexample. Nothing here is admitted,
nothing uses `native_decide`, and no `Classical.choice` enters beyond what `Mathlib`
already pulls in.

Every witness keeps its `:merge` function **nullary**. That is not cosmetic: a nullary
key makes `congrKeys cl [] []` reduce to `true` through `List.all []` without ever
forcing `cl`, and `cl` is `closureF`, whose well-founded recursion the kernel cannot
unfold. With nullary keys the whole interpreter — `execExpr`, `execAction`, `mergeRound`,
`mergeSaturateF 64` — reduces by `rfl`.
-/

namespace Egglog
namespace Falsity

/-! ## Shared vocabulary -/

/-- `(function f () i64 :merge 7)`: a nullary `:merge` function with an empty merge body
whose merged value is the constant `7`. -/
def fDecl : FnDecl := { arity := 0, outArity := 1, merge := .merge [] [.lit (.int 7)] }

/-- The signature `Cmd.decl` installs for `fDecl`. -/
def sigF : Signature := Function.update (fun _ => none) "f" (some fDecl)

/-- The three-field `FDatabase.Inv` as the refinement chain originally stated it.

The live `FDatabase.Inv` is being strengthened concurrently; every claim below is proved
against *both*, so that neither version's shape can quietly rescue the counterexample. -/
structure Inv3 (d : FDatabase) : Prop where
  wf : d.WF
  ctorTerms : d.toDatabase.CtorTerms
  rowsComplete : d.toDatabase.RowsComplete

/-! ## Claim 1 — `Cmd.decl` destroys `FDatabase.Inv`

`Database.CtorTerms` is stated relative to `db.sig`, and `execCmdM (.decl f dc)` rewrites
`sig`. So a database already holding `g()` — a constructor, because `g` is undeclared —
stops satisfying `CtorTerms` the moment `g` is declared `:merge`. -/

/-- A database holding the constructor term `g()`, under the empty signature. -/
def dG : FDatabase where
  sig := fun _ => none
  terms := [.app "g" []]
  rows := [⟨"g", [], [.app "g" []]⟩]
  eqs := []
  env := []
  rules := []

/-- `dG` after `(function g () i64 :merge 7)`. -/
def dG' : FDatabase := { dG with sig := Function.update dG.sig "g" (some fDecl) }

theorem dG_terms (t : Term) : t ∈ dG.toDatabase.terms ↔ t = .app "g" [] := by
  simp [FDatabase.toDatabase, dG]

theorem dG_rows (r : Row) : r ∈ dG.toDatabase.rows ↔ r = ⟨"g", [], [.app "g" []]⟩ := by
  simp [FDatabase.toDatabase, dG]

theorem dG_wf : dG.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht s hs
    rw [dG_terms] at ht
    subst ht
    rw [Term.mem_subterms] at hs
    cases hs with
    | refl => rw [dG_terms]
    | arg hmem _ => simp at hmem
  · intro p hp; simp [FDatabase.toDatabase, dG] at hp
  · intro b hb; simp [FDatabase.toDatabase, dG] at hb

/-- Every name is undeclared in `dG`, hence a constructor. -/
theorem dG_ctorTerms : dG.toDatabase.CtorTerms := fun _ _ _ => rfl

theorem dG_rowsComplete : dG.toDatabase.RowsComplete := by
  rintro r ⟨hout, hmem⟩
  rw [dG_terms] at hmem
  obtain ⟨fn, args, out⟩ := r
  simp only [Term.app.injEq] at hmem hout
  obtain ⟨rfl, rfl⟩ := hmem
  rw [dG_rows]
  simp_all

theorem dG_inv3 : Inv3 dG := ⟨dG_wf, dG_ctorTerms, dG_rowsComplete⟩

theorem dG_inv : dG.Inv := by
  refine ⟨dG_wf, dG_ctorTerms, dG_rowsComplete, ?_, ?_⟩
  · -- rowsWF
    intro r hr
    rw [dG_rows] at hr
    subst hr
    refine ⟨by simp, ?_⟩
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    rw [dG_terms]
  · -- ctorRows
    intro r hr _
    rw [dG_rows] at hr
    subst hr
    exact ⟨rfl, by rw [dG_terms]⟩

/-- `mergeOf` at `g` really has changed. -/
theorem dG'_mergeOf : dG'.toDatabase.sig.mergeOf "g" = MergeSpec.merge [] [.lit (.int 7)] :=
  rfl

/-- **Claim 1, CONFIRMED.** `Cmd.decl` takes a database satisfying `FDatabase.Inv` to one
that does not.

Precisely what this does and does not show. It shows there is **no** `FDatabase.Inv.decl`
preservation lemma to be had, so `execProgramM_contained`'s induction — which carries `Inv`
and must re-establish it after every command — cannot get past a `.decl`. It does **not**
by itself refute `execCmdM_contained` at the `.decl` case: that case's conclusion is a
containment, and `CmdStep.decl` reaches exactly the interpreter's state. The defect is in
the invariant, and the fix has to be either a hypothesis excluding a re-declaration of a
name already used as a constructor, or a formulation of `CtorTerms` that a signature update
cannot invalidate. -/
theorem claim1 : ∃ (d : FDatabase) (f : FnName) (dc : FnDecl) (d' : FDatabase),
    d.Inv ∧ d.execCmdM (.decl f dc) = some d' ∧ ¬ d'.Inv :=
  ⟨dG, "g", fDecl, dG', dG_inv, rfl, fun h => by
    have hmem : Term.app "g" [] ∈ dG'.toDatabase.terms := by
      show Term.app "g" [] ∈ dG.toDatabase.terms
      rw [dG_terms]
    have := h.ctorTerms "g" [] hmem
    rw [dG'_mergeOf] at this
    exact MergeSpec.noConfusion this⟩

/-- Claim 1 against the *original* three-field invariant, so that the witness does not
depend on which version of `FDatabase.Inv` is in force: the field it breaks, `ctorTerms`,
is in both. -/
theorem claim1' : ∃ (d : FDatabase) (f : FnName) (dc : FnDecl) (d' : FDatabase),
    Inv3 d ∧ d.execCmdM (.decl f dc) = some d' ∧ ¬ Inv3 d' :=
  ⟨dG, "g", fDecl, dG', dG_inv3, rfl,
    fun h => by
      have hmem : Term.app "g" [] ∈ dG'.toDatabase.terms := by
        show Term.app "g" [] ∈ dG.toDatabase.terms
        rw [dG_terms]
      have := h.ctorTerms "g" [] hmem
      rw [dG'_mergeOf] at this
      exact MergeSpec.noConfusion this⟩

/-! ## Claim 2 — `execCmdM_contained` is false at `.action`

`execCmdM (.action a) = (d.execAction a).bind (mergeSaturateF mergeFuel)` runs a merge
phase; `CmdStep.action` does not. The merge phase *writes a new row*, and no `ActionStep`
successor holds it, so the implementation state is not `Contained` in any of them.

The deletion of the two merged rows is the safe direction (`Contained` asks the
implementation to be *smaller*). The killer is the row the merge **adds**. -/

/-- After `(function f () i64 :merge 7)` and `(set (f) 1)`. -/
def d1 : FDatabase where
  sig := sigF
  terms := [.lit (.int 1)]
  rows := [⟨"f", [], [.lit (.int 1)]⟩]
  eqs := []
  env := []
  rules := []

/-- The top-level action `(set (f) 2)`. -/
def act2 : Action := .set "f" [] [.lit (.int 2)]

/-- What `execCmdM (.action act2)` computes: the two colliding rows are gone and the
merged row `f() ↦ 7` — a row no `ActionStep` successor holds — is in their place. -/
def d2 : FDatabase where
  sig := sigF
  terms := [.lit (.int 7), .lit (.int 2), .lit (.int 1)]
  rows := [⟨"f", [], [.lit (.int 7)]⟩]
  eqs := []
  env := []
  rules := []

theorem d1_terms (t : Term) : t ∈ d1.toDatabase.terms ↔ t = .lit (.int 1) := by
  simp [FDatabase.toDatabase, d1]

theorem d1_rows (r : Row) : r ∈ d1.toDatabase.rows ↔ r = ⟨"f", [], [.lit (.int 1)]⟩ := by
  simp [FDatabase.toDatabase, d1]

theorem d1_wf : d1.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht s hs
    rw [d1_terms] at ht
    subst ht
    rw [Term.mem_subterms] at hs
    cases hs
    rw [d1_terms]
  · intro p hp; simp [FDatabase.toDatabase, d1] at hp
  · intro b hb; simp [FDatabase.toDatabase, d1] at hb

/-- `d1` holds no application at all, so `CtorTerms` is vacuous — the invariant is not
being smuggled past a `:merge` head here. -/
theorem d1_ctorTerms : d1.toDatabase.CtorTerms := by
  intro f as h
  rw [d1_terms] at h
  exact absurd h (by simp)

theorem d1_rowsComplete : d1.toDatabase.RowsComplete := by
  rintro r ⟨hout, hmem⟩
  rw [d1_terms] at hmem
  exact absurd hmem (by simp)

theorem d1_inv3 : Inv3 d1 := ⟨d1_wf, d1_ctorTerms, d1_rowsComplete⟩

theorem d1_inv : d1.Inv := by
  refine ⟨d1_wf, d1_ctorTerms, d1_rowsComplete, ?_, ?_⟩
  · intro r hr
    rw [d1_rows] at hr
    subst hr
    refine ⟨by simp, ?_⟩
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    rw [d1_terms]
  · intro r hr hf
    rw [d1_rows] at hr
    subst hr
    exact absurd hf (by intro h; exact MergeSpec.noConfusion h)

/-- The action is legal: `Action.SetLegal` is the only well-formedness condition the model
imposes on a `set`, and `f` is not a constructor. So the counterexample is not an artifact
of an ill-formed program. -/
theorem act2_legal : act2.SetLegal d1.sig := by
  intro h
  exact MergeSpec.noConfusion (show MergeSpec.merge [] [Expr.lit (Lit.int 7)] = _ from h)

/-- The whole command, merge phase included, reduces. -/
theorem d1_step : d1.execCmdM (.action act2) = some d2 := rfl

/-- A literal has no constructor rows, so an `addTerm` of one adds nothing to `rows`. -/
theorem ctorRows_lit {l : Lit} : (Term.lit l).ctorRows = ∅ := by
  ext r
  simp only [Term.ctorRows, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ hm
  rw [Term.mem_subterms] at hm
  cases hm

/-- The merged row `f() ↦ 7`. -/
def rowMerged : Row := ⟨"f", [], [.lit (.int 7)]⟩

theorem rowMerged_mem : rowMerged ∈ d2.toDatabase.rows := by
  simp [FDatabase.toDatabase, d2, rowMerged]

/-- Every `ActionStep` successor of `d1` under `(set (f) 2)` has exactly the two asserted
rows and nothing else. -/
theorem actionStep_rows {db : Database}
    (h : Database.ActionStep d1.toDatabase act2 db) :
    db.rows = insert (Row.mk "f" [] [.lit (.int 2)]) d1.toDatabase.rows := by
  cases h with
  | set hargs hout =>
    rename_i ts vs
    cases hargs
    cases hout with
    | cons he hrest =>
      cases hrest
      cases he
      show (Database.addRow "f" [] [Term.lit (Lit.int 2)] d1.toDatabase).rows = _
      simp only [Database.addRow, Database.addTerms, List.foldl, Database.addTerm,
        ctorRows_lit, Set.union_empty]

/-- The heart of Claim 2: no `CmdStep` successor of `d1` contains the interpreter's answer,
because the merge phase wrote `f() ↦ 7` and the specification's `.action` rule has no merge
phase to write it. -/
theorem d1_not_contained :
    ¬ ∃ db, CmdStep d1.toDatabase (.action act2) db ∧ d2.toDatabase.Contained db := by
  rintro ⟨db, hstep, hc⟩
  cases hstep with
  | action hact =>
    have hrows := actionStep_rows hact
    have : rowMerged ∈ db.rows := hc.rows rowMerged_mem
    rw [hrows] at this
    simp only [Set.mem_insert_iff, FDatabase.toDatabase, Set.mem_setOf_eq, d1,
      List.mem_singleton, rowMerged] at this
    rcases this with h | h <;> exact absurd h (by decide)

/-- **Claim 2, CONFIRMED.** `FDatabase.execCmdM_contained` is false. -/
theorem claim2 : ∃ (d d' : FDatabase) (a : Action), d.Inv ∧ d.execCmdM (.action a) = some d' ∧
    ¬ ∃ db, CmdStep d.toDatabase (.action a) db ∧ d'.toDatabase.Contained db :=
  ⟨d1, d2, act2, d1_inv, d1_step, d1_not_contained⟩

/-- Claim 2 against the original three-field invariant. -/
theorem claim2' : ∃ (d d' : FDatabase) (a : Action), Inv3 d ∧ d.execCmdM (.action a) = some d' ∧
    ¬ ∃ db, CmdStep d.toDatabase (.action a) db ∧ d'.toDatabase.Contained db :=
  ⟨d1, d2, act2, d1_inv3, d1_step, d1_not_contained⟩

/-- `FDatabase.execCmdM_contained`'s statement, verbatim, negated. -/
theorem claim2_execCmdM : ¬ ∀ {d d' : FDatabase} {c : Cmd}, d.Inv → d.execCmdM c = some d' →
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Contained db :=
  fun h => d1_not_contained (h d1_inv d1_step)

/-! ### The same counterexample kills `execM_contained` outright

`d1` is not hand-built: it is what the interpreter reaches from `FDatabase.empty` on the
three-command program below. Since every `MEval` in that program is on a literal, the
specification's `ProgramStep` successor is unique, and it holds neither `f() ↦ 7` nor the
term `7`. -/

/-- `(function f () i64 :merge 7) (set (f) 1) (set (f) 2)`. -/
def prog : Program :=
  [.decl "f" fDecl, .action (.set "f" [] [.lit (.int 1)]), .action act2]

theorem prog_exec : execM prog = some d2 := rfl

theorem programStep_rows {db : Database} (h : ProgramStep FDatabase.empty.toDatabase prog db) :
    db.rows = insert (Row.mk "f" [] [.lit (.int 2)])
      (insert (Row.mk "f" [] [.lit (.int 1)]) (∅ : Set Row)) := by
  cases h with
  | cons hc hrest =>
    cases hc with
    | decl =>
      cases hrest with
      | cons hc1 hrest1 =>
        cases hc1 with
        | action ha1 =>
          cases ha1 with
          | set hargs hout =>
            cases hargs
            cases hout with
            | cons he hr =>
              cases hr
              cases he
              cases hrest1 with
              | cons hc2 hrest2 =>
                cases hc2 with
                | action ha2 =>
                  cases ha2 with
                  | set hargs2 hout2 =>
                    cases hargs2
                    cases hout2 with
                    | cons he2 hr2 =>
                      cases hr2
                      cases he2
                      cases hrest2
                      simp only [Database.addRow, Database.addTerms, List.foldl,
                        Database.addTerm, ctorRows_lit, Set.union_empty,
                        FDatabase.toDatabase_empty, Database.empty]

/-- **`execM_contained` is false.** The implementation's answer to a three-command program
is contained in no state the specification reaches. -/
theorem claim2_execM : ¬ ∀ {p : Program} {d : FDatabase}, execM p = some d →
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ d.toDatabase.Contained db := by
  intro h
  obtain ⟨db, hstep, hc⟩ := h prog_exec
  have hmem : rowMerged ∈ db.rows := hc.rows rowMerged_mem
  rw [programStep_rows hstep] at hmem
  simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false, rowMerged] at hmem
  rcases hmem with h | h <;> exact absurd h (by decide)

/-- `FDatabase.execProgramM_contained`'s statement, verbatim, negated. It implies
`execM_contained` through the proved `FDatabase.Inv.empty`, so refuting the latter refutes
the former. -/
theorem claim2_execProgramM :
    ¬ ∀ {d d' : FDatabase} {p : Program}, d.Inv → d.execProgramM p = some d' →
      ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Contained db := by
  intro h
  exact claim2_execM fun hp => h FDatabase.Inv.empty hp

/-! ## Claim 3 — `execExpr`'s lookup branch fails where `MEval` succeeds

`Impl/Merge.lean`'s lookup branch is

    match d.outs f ts with | [v] :: _ => some v | _ => none

which demands that the *first* congruent row be single-column. `Expr.MEval.lookup` only
needs *some* congruent row recording `[v]`. Since `addRow` prepends, a freshly written
multi-column row shadows a single-column one at the same key.

**Scope, stated honestly.** This is an *incompleteness*, not unsoundness: `execExpr`
returning `none` cannot make `execExpr_MEval` false, and it makes `execM` `none`, at which
point every `*_contained` theorem is vacuous. What it does break is the docstring in
`Impl/Merge.lean` — "`Expr.MEval`'s `lookup` reads any recorded output; `execExpr` takes
the first" — which describes a *choice among* the spec's answers, and a `STUCK` differential
result where egglog answers.

Reaching the state needs one function whose rows differ in value-column count at one key.
Nothing in the model forbids it: `FnDecl.outArity` is declared but never read outside
`Tests/Egg.lean`'s renderer, and `Action.SetLegal` — the only well-formedness condition on
a `set` — constrains only the function's merge kind (`Spec/Scope.lean:148`). Both actions
below are `SetLegal`. egglog fixes a function's value-column count at declaration, which is
what `outArity` records, so the mixed-width state is presumably not reachable from a
well-typed egglog program: this reads as a gap in the model's own hygiene rather than a
divergence from egglog. It is still a real bug in `execExpr`, whose contract as written is
"take the first recorded output". -/

/-- `(function h () i64 :merge 9)`. -/
def hDecl : FnDecl := { arity := 0, outArity := 1, merge := .merge [] [.lit (.int 9)] }

def sigH : Signature := Function.update (fun _ => none) "h" (some hDecl)

/-- A database recording the single-column row `h() ↦ 3`. -/
def d3 : FDatabase where
  sig := sigH
  terms := [.lit (.int 3)]
  rows := [⟨"h", [], [.lit (.int 3)]⟩]
  eqs := []
  env := []
  rules := []

/-- `(set (h) (values 1 2))` — a two-column write at the same key. -/
def actTuple : Action := .set "h" [] [.lit (.int 1), .lit (.int 2)]

theorem actTuple_legal : actTuple.SetLegal d3.sig := by
  intro h
  exact MergeSpec.noConfusion (show MergeSpec.merge [] [Expr.lit (Lit.int 9)] = _ from h)

/-- The state after the two-column write: the wide row is now first. -/
def d4 : FDatabase := d3.addRow "h" [] [.lit (.int 1), .lit (.int 2)]

theorem d4_outs : d4.outs "h" [] = [[.lit (.int 1), .lit (.int 2)], [.lit (.int 3)]] := rfl

/-- The interpreter gets stuck. -/
theorem d4_execExpr : d4.execExpr [] (.app "h" []) = none := rfl

/-- The specification does not: the shadowed single-column row is still a legal read. -/
theorem d4_meval : Expr.MEval d4.toDatabase [] (.app "h" []) (.lit (.int 3)) := by
  refine Expr.MEval.lookup rfl ?_ .nil ⟨[], .nil, ?_⟩
  · intro hh
    exact MergeSpec.noConfusion (show MergeSpec.merge [] [Expr.lit (Lit.int 9)] = _ from hh)
  · show Row.mk "h" [] [Term.lit (Lit.int 3)] ∈ d4.rows
    decide

/-- **Claim 3, CONFIRMED.** `execExpr` returns `none` on an application the specification
evaluates. -/
theorem claim3 : ∃ (d : FDatabase) (e : Expr) (t : Term),
    d.execExpr d.env e = none ∧ Expr.MEval d.toDatabase d.env e t :=
  ⟨d4, .app "h" [], .lit (.int 3), d4_execExpr, d4_meval⟩

/-- The shadowing is dynamic, not a hand-built state: one `set` inside an action list is
enough to make the *next* action of the same list get stuck. -/
theorem claim3_actions :
    d3.execActions [actTuple, .expr (.app "h" [])] = none := rfl

/-- …while the specification runs the same action list to completion. -/
theorem claim3_actions_spec :
    Database.ActionsStep d3.toDatabase [actTuple, .expr (.app "h" [])]
      ((d3.toDatabase.addRow "h" [] [.lit (.int 1), .lit (.int 2)]).addTerm
        (.lit (.int 3))) := by
  refine .cons (.set .nil (.cons .lit (.cons .lit .nil))) (.cons ?_ .nil)
  · have : (d3.toDatabase.addRow "h" [] [.lit (.int 1), .lit (.int 2)]) = d4.toDatabase := by
      rw [d4, FDatabase.toDatabase_addRow]
    rw [this]
    exact .expr d4_meval

/-! ## Axiom audit -/


/-! ### The counterexample -/

def cexSig : Signature := fun n =>
  if n = "f" then some ⟨0, 1, .merge [.set "F" [] []] [.var "old"]⟩ else none

def cexD : FDatabase where
  sig := cexSig
  terms := [.lit (.int 1), .lit (.int 2)]
  rows := [⟨"f", [], [.lit (.int 1)]⟩, ⟨"f", [], [.lit (.int 2)]⟩]
  eqs := []
  env := []
  rules := []

theorem cexD_terms {t : Term} (h : t ∈ cexD.toDatabase.terms) :
    t = .lit (.int 1) ∨ t = .lit (.int 2) := by
  simpa [cexD, FDatabase.toDatabase] using h

theorem cexD_rows {r : Row} (h : r ∈ cexD.toDatabase.rows) :
    r = ⟨"f", [], [.lit (.int 1)]⟩ ∨ r = ⟨"f", [], [.lit (.int 2)]⟩ := by
  simpa [cexD, FDatabase.toDatabase] using h

theorem cexD_mem_terms (l : Lit) (h : l = .int 1 ∨ l = .int 2) :
    Term.lit l ∈ cexD.toDatabase.terms := by
  rcases h with rfl | rfl <;> simp [cexD, FDatabase.toDatabase]

theorem cexD_inv : cexD.Inv where
  wf := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht s hs
      rcases cexD_terms ht with rfl | rfl <;>
        · rw [Term.subterms_lit] at hs
          rcases hs with rfl
          exact ht
    · intro p hp; simp [cexD, FDatabase.toDatabase] at hp
    · intro b hb; simp [cexD, FDatabase.toDatabase] at hb
  ctorTerms := by
    intro f as hm
    rcases cexD_terms hm with h | h <;> simp at h
  rowsComplete := by
    rintro r ⟨-, hm⟩
    rcases cexD_terms hm with h | h <;> simp at h
  rowsWF := by
    intro r hr
    rcases cexD_rows hr with rfl | rfl
    · refine ⟨by simp, fun v hv => ?_⟩
      rw [List.mem_singleton] at hv
      exact hv ▸ cexD_mem_terms _ (Or.inl rfl)
    · refine ⟨by simp, fun v hv => ?_⟩
      rw [List.mem_singleton] at hv
      exact hv ▸ cexD_mem_terms _ (Or.inr rfl)
  ctorRows := by
    intro r hr hu
    rcases cexD_rows hr with rfl | rfl <;>
      · rw [show cexD.sig = cexSig from rfl] at hu
        simp [cexSig, Signature.mergeOf] at hu

theorem cexD_mergeRound_badRow : (⟨"F", [], []⟩ : Row) ∈ cexD.mergeRound.toDatabase.rows :=
  show (⟨"F", [], []⟩ : Row) ∈ cexD.mergeRound.rows by decide

theorem mergeRound_inv_false : ∃ d : FDatabase, d.Inv ∧ ¬ d.mergeRound.Inv := by
  refine ⟨cexD, cexD_inv, fun h => ?_⟩
  have hsig : cexD.mergeRound.sig = cexD.sig := FDatabase.mergeRound_confined.2.2.1
  have hu : cexD.mergeRound.sig.mergeOf "F" = MergeSpec.union := by
    rw [hsig]; rfl
  exact absurd (h.ctorRows ⟨"F", [], []⟩ cexD_mergeRound_badRow hu).1 (by simp)

/-! ## The two matching statements

`FDatabase.patternHoldsM_MValidSubst` and `FDatabase.matchQueryM_MValidQuerySubst` are
false without the hypotheses they now carry, for two **independent** reasons: the first
needs `ValidEnv`, and the second's `σ` *is* a valid env at both its patterns. Both
witnesses live in a one-term database — `FDatabase.empty` plus the literal `0` — whose
`Inv` comes from `Inv.empty` and `Inv.addTerm` over `Term.ctorTerm_lit`. -/

/-- The only term of the counterexample database. -/
def t0 : Term := .lit (.int 0)

/-- `FDatabase.empty` holding just `t0`. -/
def dEx : FDatabase := FDatabase.empty.addTerm t0

theorem dEx_inv : dEx.Inv := FDatabase.Inv.empty.addTerm Term.ctorTerm_lit

theorem t0_mem : t0 ∈ dEx.terms := by
  simp [dEx, FDatabase.addTerm, t0, List.mem_dedup]

/-- `t0` is its own witness: reflexivity in the extended database. -/
theorem t0_cong : (t0, t0) ∈ (dEx.addTerm t0).closureF :=
  (FDatabase.mem_closureF_addTerm dEx_inv.wf).mpr (Cong.refl (Or.inl t0_mem))

/-- The pattern `0` matches under a substitution binding `x`, which the pattern does not
mention: `patternHoldsM` reads `σ` only through `d.env ++ σ`. -/
theorem holds_lit : dEx.patternHoldsM (.expr (.lit (.int 0))) [("x", t0)] = true := by
  simp only [FDatabase.patternHoldsM, FDatabase.execExpr, decide_eq_true_eq]
  exact ⟨t0, t0_mem, t0_cong⟩

/-- **`FDatabase.patternHoldsM_MValidSubst` is false without `ValidEnv`.**
`MValidSubst.expr` carries `ValidEnv (e.freeVars db.env) db σ`, which pins `Env.dom σ` to
a permutation of the pattern's free variables; `(Expr.lit _).freeVars` is `[]` and `σ`
binds `x`. -/
theorem patternHoldsM_MValidSubst_false :
    ¬ ∀ (d : FDatabase), d.Inv → ∀ (p : Pattern) (σ : Env),
        d.patternHoldsM p σ = true → MValidSubst d.toDatabase p σ := by
  intro H
  have hbad := H dEx dEx_inv (.expr (.lit (.int 0))) [("x", t0)] holds_lit
  cases hbad with
  | expr hv _ _ _ => simpa [Env.dom, Expr.freeVars] using hv.1

/-- Two patterns sharing the variable `x`. `Query.freeVars qEx dEx.env = ["x"]`: the
`∪` in `Query.freeVars` deduplicates, so the enumerator assigns `x` once. -/
def qEx : Query := [Pattern.expr (.var "x"), Pattern.expr (.var "x")]

theorem holds_var : dEx.patternHoldsM (.expr (.var "x")) [("x", t0)] = true := by
  show decide (∃ w ∈ dEx.terms, (w, t0) ∈ (dEx.addTerm t0).closureF) = true
  rw [decide_eq_true_eq]
  exact ⟨t0, t0_mem, t0_cong⟩

theorem mem_matchQueryM_ex : [("x", t0)] ∈ dEx.matchQueryM qEx := by
  rw [FDatabase.matchQueryM, List.mem_filter]
  constructor
  · refine mem_assignments.mpr ⟨rfl, ?_⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact t0_mem
  · show (dEx.patternHoldsM (.expr (.var "x")) (Env.canon ["x"] [("x", t0)]) &&
      (dEx.patternHoldsM (.expr (.var "x")) (Env.canon ["x"] [("x", t0)]) && true)) = true
    rw [show Env.canon ["x"] [("x", t0)] = [("x", t0)] from rfl, holds_var]
    rfl

/-- `Env.UnionAll` is concatenation: `Union2` fixes `σr = σ₁ ++ σ₂` and the fold ends at
`UnionAll [σ] σ`, so lengths add. This is what the enumerator cannot satisfy. -/
theorem unionAll_sum_length {σs : List Env} {σ : Env} (h : Env.UnionAll σs σ) :
    (σs.map List.length).sum = σ.length := by
  induction h with
  | nil => simp
  | single σ => simp
  | step hu _ ih =>
    obtain ⟨-, rfl⟩ := hu
    simp only [List.map_cons, List.sum_cons, List.length_append] at ih ⊢
    omega

/-- **`FDatabase.matchQueryM_MValidQuerySubst` is false without `Env.Agree`.**
`[("x", t0)]` is enumerated for `qEx`, and `ValidEnv` holds for it at *both* patterns — so
this is not the `ValidEnv` defect again. `MValidQuerySubst` needs one substitution per
pattern, each of length `1`, concatenated to give `σ`; that would make `σ` have length
`2`. -/
theorem matchQueryM_MValidQuerySubst_false :
    ¬ ∀ (d : FDatabase), d.Inv → ∀ (q : Query) (σ : Env),
        σ ∈ d.matchQueryM q → MValidQuerySubst d.toDatabase q σ := by
  intro H
  obtain ⟨σs, hall, hu⟩ := H dEx dEx_inv qEx [("x", t0)] mem_matchQueryM_ex
  have hlen : ∀ ρ, MValidSubst dEx.toDatabase (.expr (.var "x")) ρ → ρ.length = 1 := by
    intro ρ hρ
    cases hρ with
    | expr hv _ _ _ =>
      have := hv.1.length_eq
      simpa [Env.dom, Expr.freeVars, show dEx.env = [] from rfl, Env.lookup] using this
  cases hall with
  | cons h1 hrest =>
    cases hrest with
    | cons h2 hnil =>
      cases hnil with
      | nil =>
        have := unionAll_sum_length hu
        simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
          hlen _ h1, hlen _ h2] at this
        simp at this

end Falsity
end Egglog
