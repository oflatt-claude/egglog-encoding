import EgglogSemantics.Impl.Check
import EgglogSemantics.Proofs.Merge

/-!
# Machine-checked falsity witnesses for `Proofs/Merge.lean`'s refinement chain

Two defects, each with a concrete compiling counterexample, plus three refutations of
statements that were tried without the hypotheses they now carry. Nothing here is
admitted, nothing uses `native_decide`, and no `Classical.choice` enters beyond what
`Mathlib` already pulls in.

Two further witnesses used to live here — that `Program.SetLegal` could not be dropped
from `exec_programStep`, and that `CmdStep.mono_recorded` needed a hypothesis at `.decl`.
Both turned on the specification reading congruence through `rows` and `sig`. `Cong` reads
neither, so both are gone; the two sections below record what they said and what is left
open.

**Declaration is required** (`Signature.IsCtor`), so every witness that builds a term
declares its constructors. That is not bookkeeping: three of them turned on a name being
undeclared and therefore a constructor, and each had to be rewritten to say what it now
says. `staleProgram` is the one whose *conclusion* changed — see the last section.

There was a third defect — `execCmdM_contained` was false at `.action`, because the
interpreter runs a merge phase after a top-level action and `CmdStep.action` had none.
That was a defect in the *specification*: egglog compiles a bare action into a one-rule
run and every rule-set run ends in `merge_all`. `CmdStep.action` now carries a
`MergeClosure` phase, so the witness no longer witnesses anything and has been removed
along with its data; `FDatabase.execCmdM_contained` is proved.

Every witness keeps its `:merge` function **nullary**. That is not cosmetic: a nullary
key makes `congrKeys cl [] []` reduce to `true` through `List.all []` without ever
forcing `cl`, and `cl` is `closureF`, whose well-founded recursion the kernel cannot
unfold. With nullary keys the whole interpreter — `Expr.eval`, `execAction`, `mergeRound`,
`mergeSaturateF 64` — reduces by `rfl`.
-/

namespace Egglog
namespace Falsity

/-! ## Shared vocabulary -/

/-- `(function f () i64 :merge 7)`: a nullary `:merge` function with an empty merge body
whose merged value is the constant `7`. -/
def fDecl : FnDecl :=
  { arity := 0, outArity := 1, merge := some (.merge [] [.lit (.int 7)]) }

/-- `(datatype S (c))`, at `n` argument columns. Declaration is required, so every witness
below that *builds* a term has to declare its constructor first — where these once relied
on an undeclared name being one. -/
def ctorDecl (n : Nat) : FnDecl := { arity := n, outArity := 1, merge := none }

/-- The three-field `FDatabase.Inv` as the refinement chain originally stated it.

The live `FDatabase.Inv` is being strengthened concurrently; every claim below is proved
against *both*, so that neither version's shape can quietly rescue the counterexample. -/
structure Inv3 (d : FDatabase) : Prop where
  wf : d.WF
  ctorTerms : d.toDatabase.CtorTerms
  rowsComplete : d.toDatabase.RowsComplete

/-! ## Claim 1 — `Cmd.decl` destroys `FDatabase.Inv`

`Database.CtorTerms` is stated relative to `db.sig`, and `execCmdM (.decl f dc)` rewrites
`sig`. So a database already holding `g()` — a constructor, because that is how it was
declared — stops satisfying `CtorTerms` the moment `g` is *re*declared `:merge`. -/

/-- A database holding the constructor term `g()`, with `g` declared a constructor. `dG'`
below redeclares it `:merge`, which is what `FDatabase.Unused` forbids. -/
def dG : FDatabase where
  sig := Function.update (fun _ => none) "g" (some (ctorDecl 0))
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

/-- The only application `dG` holds is `g`'s, and `g` is declared a constructor. -/
theorem dG_ctorTerms : dG.toDatabase.CtorTerms := by
  intro f as hm
  rw [dG_terms] at hm
  simp only [Term.app.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  exact ⟨ctorDecl 0, rfl, rfl⟩

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
theorem dG'_mergeOf :
    dG'.toDatabase.sig.mergeOf "g" = some (MergeSpec.merge [] [.lit (.int 7)]) := rfl

/-- **Claim 1, CONFIRMED.** `Cmd.decl` takes a database satisfying `FDatabase.Inv` to one
that does not.

Precisely what this does and does not show. It shows there is no **unconditional**
`FDatabase.Inv.decl` preservation lemma, so `execProgramM_contained`'s induction — which
carries `Inv` and must re-establish it after every command — cannot get past a `.decl`
for free. It does **not** by itself refute `execCmdM_contained` at the `.decl` case: that
case's conclusion is a containment, and `CmdStep.decl` reaches exactly the interpreter's
state.

This is what forces `FDatabase.Unused` — the hypothesis `FDatabase.Inv.decl` and hence
`FDatabase.ProgramLegal` carry: a declaration names something the state does not yet
mention. `g` here is *declared and used*, and then redeclared `:merge`, which is the one
shape that hypothesis excludes and the one shape egglog's own "declare before use"
excludes too. -/
theorem claim1 : ∃ (d : FDatabase) (f : FnName) (dc : FnDecl) (d' : FDatabase),
    d.Inv ∧ d.execCmdM (.decl f dc) = some d' ∧ ¬ d'.Inv :=
  ⟨dG, "g", fDecl, dG', dG_inv, rfl, fun h => by
    have hmem : Term.app "g" [] ∈ dG'.toDatabase.terms := by
      show Term.app "g" [] ∈ dG.toDatabase.terms
      rw [dG_terms]
    exact Signature.not_isCtor dG'_mergeOf (h.ctorTerms "g" [] hmem)⟩

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
      exact Signature.not_isCtor dG'_mergeOf (h.ctorTerms "g" [] hmem)⟩

/-! ## `SetLegal` does not bound a row's width; `arityOk` does

**What used to be here.** `claim3` witnessed a defect in `Impl/Merge.lean`'s lookup branch,

    match d.outs f ts with | [v] :: _ => some v | _ => none

which demanded that the *first* congruent row be single-column where the old `MEval.lookup`
needed only *some* congruent row recording `[v]`, so a freshly written two-column row
shadowed a single-column one at the same key. There is no lookup branch and no
a `lookup` rule any more — reading is a query atom (`Spec/Scope.lean`, "Reading in an
action") — so the defect does not exist rather than being merely unreachable, and
`claim3`, `claim3_actions` and `claim3_actions_spec` have gone with it.

**What survives is the hygiene gap that made it reachable.** `Action.SetLegal` constrains
only a function's merge kind, so it admits a `set` whose value list is the wrong width for
the declaration; `FnDecl.outArity` is what records the width, and `Impl/Check.lean`'s
arity check is what reads it. The witness below is that pair, and it is why the check is
not redundant with `SetLegal`. -/

/-- `(function h () i64 :merge 9)`. -/
def hDecl : FnDecl :=
  { arity := 0, outArity := 1, merge := some (.merge [] [.lit (.int 9)]) }

def sigH : Signature := Function.update (fun _ => none) "h" (some hDecl)

/-- `(set (h) (values 1 2))` — a two-column write to a one-column function. -/
def actTuple : Action := .set "h" [] [.lit (.int 1), .lit (.int 2)]

/-- `SetLegal`, the only condition a `set` carried before the arity check, holds of it. -/
theorem actTuple_legal : actTuple.SetLegal sigH := by
  show Signature.mergeOf sigH "h" ≠ none
  rw [show sigH.mergeOf "h" = some (.merge [] [.lit (.int 9)]) from rfl]
  simp

/-- The two-column write egglog's typechecker rejects: "Arity mismatch, expected 1 args". -/
theorem actTuple_not_arityOk : actTuple.arityOk sigH = false := rfl

/-- …and the whole program with it, so no state the model accepts holds rows of two widths
at one key. -/
theorem claim3Program_not_arityOk :
    Program.arityOk [.decl "h" hDecl, .action actTuple,
      .action (.expr (.app "h" []))] (fun _ => none) = false := rfl

/-! ## Axiom audit -/


/-! ### The counterexample -/

def cexSig : Signature := fun n =>
  if n = "f" then some ⟨0, 1, some (.merge [.set "F" [] []] [.var "old"])⟩ else none

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
  have hu : cexD.mergeRound.sig.mergeOf "F" = none := by
    rw [hsig]; rfl
  exact absurd (h.ctorRows ⟨"F", [], []⟩ cexD_mergeRound_badRow hu).1 (by simp)

/-! ## The two matching statements

`FDatabase.patternHolds_validSubst` and `FDatabase.matchQuery_validQuerySubst` are
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
mention: `patternHolds` reads `σ` only through `d.env ++ σ`. -/
theorem holds_lit : patternHolds dEx (.expr (.lit (.int 0))) [("x", t0)] = true := by
  simp only [patternHolds, Expr.eval, decide_eq_true_eq]
  exact ⟨t0, t0_mem, t0_cong⟩

/-- **`FDatabase.patternHolds_validSubst` is false without `ValidEnv`.**
`ValidSubst` carries `ValidEnv (p.freeVars db.env) db σ`, which pins `Env.dom σ` to
a permutation of the pattern's free variables; `(Expr.lit _).freeVars` is `[]` and `σ`
binds `x`. -/
theorem patternHolds_validSubst_false :
    ¬ ∀ (d : FDatabase), d.Inv → ∀ (p : Pattern) (σ : Env),
        patternHolds d p σ = true → ValidSubst d.toDatabase p σ := by
  intro H
  have hbad := H dEx dEx_inv (.expr (.lit (.int 0))) [("x", t0)] holds_lit
  simpa [Env.dom, Pattern.freeVars, Expr.freeVars] using hbad.1.1

/-- Two patterns sharing the variable `x`. `Query.freeVars qEx dEx.env = ["x"]`: the
`∪` in `Query.freeVars` deduplicates, so the enumerator assigns `x` once. -/
def qEx : Query := [Pattern.expr (.var "x"), Pattern.expr (.var "x")]

theorem holds_var : patternHolds dEx (.expr (.var "x")) [("x", t0)] = true := by
  show decide (∃ w ∈ dEx.terms, (w, t0) ∈ (dEx.addTerm t0).closureF) = true
  rw [decide_eq_true_eq]
  exact ⟨t0, t0_mem, t0_cong⟩

theorem mem_matchQuery_ex : [("x", t0)] ∈ matchQuery dEx qEx := by
  rw [matchQuery, List.mem_filter]
  constructor
  · refine mem_assignments.mpr ⟨rfl, ?_⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact t0_mem
  · show (patternHolds dEx (.expr (.var "x")) (Env.canon ["x"] [("x", t0)]) &&
      (patternHolds dEx (.expr (.var "x")) (Env.canon ["x"] [("x", t0)]) && true)) = true
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

/-- **`FDatabase.matchQuery_validQuerySubst` is false without `Env.Agree`.**
`[("x", t0)]` is enumerated for `qEx`, and `ValidEnv` holds for it at *both* patterns — so
this is not the `ValidEnv` defect again. `ValidQuerySubst` needs one substitution per
pattern, each of length `1`, concatenated to give `σ`; that would make `σ` have length
`2`. -/
theorem matchQuery_validQuerySubst_false :
    ¬ ∀ (d : FDatabase), d.Inv → ∀ (q : Query) (σ : Env),
        σ ∈ matchQuery d q → ValidQuerySubst d.toDatabase q σ := by
  intro H
  obtain ⟨σs, hall, hu⟩ := H dEx dEx_inv qEx [("x", t0)] mem_matchQuery_ex
  have hlen : ∀ ρ, ValidSubst dEx.toDatabase (.expr (.var "x")) ρ → ρ.length = 1 := by
    intro ρ hρ
    have := hρ.1.1.length_eq
    simpa [Env.dom, Pattern.freeVars, Expr.freeVars, show dEx.env = [] from rfl, Env.lookup]
      using this
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

/-! ## Where `execM_reachable`'s `SetLegal` witness went

There used to be a witness here — `(datatype S (f) (g)) (set (f) 0) (set (f) 1)
(rule ((= 0 1)) ((g))) (run)` — that `Program.SetLegal` could not be dropped from
`execM_reachable` and `exec_programStep`. It worked because the specification read
congruence as a relation that consulted `rows`: the two `set`s left two rows of the
constructor `f` at one key, the functional dependency derived `0 = 1`, and the
interpreter's `closureF`, which computes `Cong`, did not.

`Spec/` no longer has that relation. `Cong` reads `terms` and `eqs` and nothing else, so
`(set (f) 0)` and `(set (f) 1)` leave a stray row that *neither* side's congruence sees
and the query `((= 0 1))` matches in neither. The program is still one egglog's front end
rejects, and `Action.SetLegal` still rejects it; what is gone is the proof that the
hypothesis is *necessary*.

`exec_programStep` and `execM_reachable` still carry it, because
`Database.CtorState.rows` is what the induction re-establishes at each command and
`Action.SetLegal` is what preserves it. Whether the hypothesis could now be dropped
outright is open, and is not settled here.

What the same program *does* still witness is below: `Proofs/Congruence.lean`'s `Cong.fd`
has a hypothesis, and a `set` on a constructor is a state a program reaches where that
hypothesis is false and the functional dependency fails. -/

theorem forall₂_eq_list {as bs : List Term} (h : List.Forall₂ (· = ·) as bs) : as = bs := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [hab, ih]

/-- `(datatype S (c) (d) (f)) (set (f) (c)) (set (f) (d))`. Declares only constructors,
and its two `set`s are the one thing `Program.SetLegal` forbids. -/
def setCtorProgram : Program :=
  [ .decl "c" (ctorDecl 0), .decl "d" (ctorDecl 0), .decl "f" (ctorDecl 0),
    .action (.set "f" [] [.app "c" []]), .action (.set "f" [] [.app "d" []]) ]

def cTerm : Term := .app "c" []
def dTerm : Term := .app "d" []

def setCtorSig₁ : Database :=
  { Database.empty with sig := Function.update Database.empty.sig "c" (some (ctorDecl 0)) }
def setCtorSig₂ : Database :=
  { setCtorSig₁ with sig := Function.update setCtorSig₁.sig "d" (some (ctorDecl 0)) }
def setCtorSig : Database :=
  { setCtorSig₂ with sig := Function.update setCtorSig₂.sig "f" (some (ctorDecl 0)) }

/-- After `(set (f) (c))`. -/
def setCtorDb₁ : Database := setCtorSig.addRow "f" [] [cTerm]

/-- After `(set (f) (d))`: two rows of the constructor `f` at the same (empty) key,
recording two different terms. -/
def setCtorDb : Database := setCtorDb₁.addRow "f" [] [dTerm]

theorem setCtor_eval₁ :
    evalAction setCtorSig (.set "f" [] [.app "c" []]) = some setCtorDb₁ := rfl

theorem setCtor_eval₂ :
    evalAction setCtorDb₁ (.set "f" [] [.app "d" []]) = some setCtorDb := rfl

/-- **The state is reachable.** No merge phase does anything — every declaration is a
constructor — so each action is its own step. -/
theorem setCtor_programStep : ProgramStep Database.empty setCtorProgram setCtorDb :=
  .cons .decl (.cons .decl (.cons .decl
    (.cons (.action setCtor_eval₁ .refl) (.cons (.action setCtor_eval₂ .refl) .nil))))

theorem setCtor_row_c : Row.mk "f" [] [cTerm] ∈ setCtorDb.rows := by
  simp [setCtorDb, setCtorDb₁, Database.addRow, Database.addTerms, Database.addTerm]

theorem setCtor_row_d : Row.mk "f" [] [dTerm] ∈ setCtorDb.rows := by
  simp [setCtorDb, Database.addRow]

theorem setCtor_isCtor : setCtorDb.sig.IsCtor "f" := ⟨ctorDecl 0, rfl, rfl⟩

theorem setCtor_eqs : setCtorDb.eqs = ∅ := rfl

/-- **`Cong.fd`'s hypothesis is false there.** `f` is a declared constructor and its row
records `(c)`, which is not `.app "f" []`. -/
theorem setCtor_not_ctorShaped :
    ¬ ∀ r ∈ setCtorDb.rows, setCtorDb.sig.IsCtor r.fn →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ setCtorDb.terms := by
  intro h
  have := (h ⟨"f", [], [cTerm]⟩ setCtor_row_c setCtor_isCtor).1
  simp [cTerm] at this

/-- **…and the functional dependency genuinely fails.** The two rows are both present,
their keys are equal, and `f` is a declared constructor; `Cong` still does not relate the
outputs, because `eqs` is empty and the two terms head different names.

This is the whole of the difference a row-reading congruence would have made, and it is
confined to programs `Action.SetLegal` rejects. -/
theorem setCtor_not_cong : ¬ Cong setCtorDb cTerm dTerm := by
  intro h
  have heq : cTerm = dTerm :=
    Cong.le (R := (· = ·)) (fun a b hm => absurd (setCtor_eqs ▸ hm) (by simp))
      (fun _ _ => rfl) (fun _ _ h => h.symm) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
      (fun _ _ _ _ _ hl => by rw [forall₂_eq_list hl]) h
  simp [cTerm, dTerm] at heq

theorem setCtorProgram_ctorDecls : setCtorProgram.CtorDecls := by
  intro c hc
  simp only [setCtorProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> trivial

/-- The one check that rejects it. -/
theorem setCtorProgram_not_setLegal :
    ¬ setCtorProgram.SetLegal Database.empty.sig := by
  rintro ⟨-, -, -, hs, -⟩
  exact hs (by decide)


/-! ## `CmdStep.mono_recorded` at `.decl`

Both witnesses that used to bound this case are gone, for different reasons. -/

/-! ### The `.decl` case no longer needs a hypothesis

The witness that used to sit here declared `f` a constructor, gave it two rows at one key
whose outputs the functional dependency equated, and then *re*declared `f` `:no-merge` —
which took the derivation away without removing a term, a row or an equality, so
`Database.Recorded` was destroyed by a command that added nothing.

`Cong` reads neither `sig` nor `rows`, so no declaration can destroy a derivation and the
witness cannot be rebuilt. `CmdStep.mono_recorded` and `ProgramStep.mono_recorded` have
correspondingly lost their `Cmd.DeclFresh` hypothesis, and `Cong.mono_update` is the
`.decl` case in one line.

`FDatabase.ProgramLegal` still carries `Cmd.DeclUnused`, for an unrelated reason that
`claim1` above still witnesses: a declaration destroys `FDatabase.Inv`. -/

/-! ### …and the program that used to block the other candidate no longer runs

`staleProgram`'s rule head names `f`, which nothing declares. Under the old reading that
made `f` a constructor, `Expr.eval` built `(f)`, `addTerm` wrote its constructor row, and
every specification run of the program therefore held a row of an undeclared name — which
is what made "the witness holds no row of `f`" unavailable as a hypothesis for
`CmdStep.mono_recorded`.

Declaration is required now, so `Expr.eval` has no rule for `(f)`: the head gets stuck at
every state the program reaches, the rule contributes nothing, and no row of `f` is ever
written. The program is correspondingly not `Program.Evaluable`, which is the static check
that rejects it. Both facts are below; the row is gone, so there is nothing left to
exhibit. -/

/-- `(function M () i64 :merge new)`. -/
def staleDecl : FnDecl := ⟨0, 1, some (.merge [] [.var "new"])⟩

/-- `(rule ((= 0 (M))) ((f)))`. Its head names `f`, which nothing has declared; only a
`set` is constrained by `Action.SetLegal`, so the rule is still legal, and it is
`Program.Evaluable` that rejects it. -/
def staleRule : Rule := ⟨[.values [.lit (.int 0)] "M" []], [.expr (.app "f" [])]⟩

def staleProgram : Program :=
  [ .decl "M" staleDecl,
    .action (.set "M" [] [.lit (.int 0)]),
    .action (.set "M" [] [.lit (.int 1)]),
    .rule staleRule,
    .run ]

def staleSig : Signature := Function.update (fun _ => none) "M" (some staleDecl)

theorem staleSig_mergeOf :
    Signature.mergeOf staleSig "M" = some (.merge [] [.var "new"]) := rfl

/-- The program passes the head condition the refinement chain carries. -/
theorem staleProgram_setLegal : Program.SetLegal staleProgram (fun _ => none) := by
  refine ⟨trivial, ?_, ?_, ⟨fun _ _ => trivial, trivial, trivial⟩, trivial, trivial⟩ <;>
    · show Signature.mergeOf staleSig "M" ≠ none
      rw [staleSig_mergeOf]
      simp

/-- …and the merge-body condition it carries. -/
theorem staleProgram_mergesLegal : Signature.MergesLegal staleSig := by
  intro g body res hg
  by_cases hgM : g = "M"
  · subst hgM
    rw [staleSig_mergeOf] at hg
    cases Option.some.inj hg
    trivial
  · rw [Signature.mergeOf, staleSig, Function.update_of_ne hgM] at hg
    exact absurd hg (by simp)

/-- **The static check rejects it.** `Program.Evaluable` asks that every applied name be a
declared constructor, and `staleRule`'s head applies `f`. -/
theorem staleProgram_not_evaluable : ¬ Program.Evaluable staleProgram (fun _ => none) := by
  rintro ⟨-, -, -, hrule, -, -⟩
  exact Signature.not_isCtor_of_none (show staleSig "f" = none from rfl)
    (hrule.2.1 "f" (by simp)).2

/-- **And the row is no longer reachable.** At every state `staleProgram` reaches, `f` is
still undeclared, so the rule's head does not evaluate under any environment: the firing
that used to write `(f)`'s constructor row cannot happen.

The old witness — `undeclared_row_reachable` — exhibited that row and concluded that
`CmdStep.mono_recorded`'s `.decl` case could not assume the specification witness to be
free of `f`. This is what replaces it. -/
theorem staleProgram_head_stuck {C : Database}
    (h : ProgramStep FDatabase.empty.toDatabase staleProgram C) :
    C.sig "f" = none ∧ ∀ σ : Env, Expr.eval C.sig (.app "f" []) σ = none := by
  rw [staleProgram] at h
  obtain ⟨C1, h1, h⟩ := h.cons_inv
  obtain ⟨C2, h2, h⟩ := h.cons_inv
  obtain ⟨C3, h3, h⟩ := h.cons_inv
  obtain ⟨C4, h4, h⟩ := h.cons_inv
  obtain ⟨C5, h5, h⟩ := h.cons_inv
  have hf : C5.sig "f" = none := by
    rw [h5.sig, h4.sig, h3.sig, h2.sig, h1.sig]
    rfl
  obtain rfl := h.nil_inv
  exact ⟨hf, fun σ =>
    Expr.eval_app_undeclared (show Prim.ofName "f" = none from rfl) hf⟩

end Falsity
end Egglog
