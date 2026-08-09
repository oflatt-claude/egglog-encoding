import EgglogSemantics.Impl.Check
import EgglogSemantics.Proofs.Merge

/-!
# Machine-checked falsity witnesses for `Proofs/Merge.lean`'s refinement chain

Two defects, each with a concrete compiling counterexample, plus three refutations of
statements that were tried without the hypotheses they now carry, plus one witness that a
hypothesis a *proved* theorem carries cannot be dropped —
`execM_reachable_needs_setLegal`. Nothing here is admitted, nothing uses `native_decide`,
and no `Classical.choice` enters beyond what `Mathlib` already pulls in.

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
mention. `g` here is *undeclared but used*, which is the one shape that hypothesis
excludes and the one shape egglog's own "declare before use" excludes too. -/
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
theorem actTuple_legal : actTuple.SetLegal sigH :=
  Signature.not_isCtor (show sigH.mergeOf "h" = some (.merge [] [.lit (.int 9)]) from rfl)

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
        simp [cexSig, Signature.IsCtor, Signature.mergeOf] at hu

theorem cexD_mergeRound_badRow : (⟨"F", [], []⟩ : Row) ∈ cexD.mergeRound.toDatabase.rows :=
  show (⟨"F", [], []⟩ : Row) ∈ cexD.mergeRound.rows by decide

theorem mergeRound_inv_false : ∃ d : FDatabase, d.Inv ∧ ¬ d.mergeRound.Inv := by
  refine ⟨cexD, cexD_inv, fun h => ?_⟩
  have hsig : cexD.mergeRound.sig = cexD.sig := FDatabase.mergeRound_confined.2.2.1
  have hu : cexD.mergeRound.sig.IsCtor "F" := by
    rw [hsig]; rfl
  exact absurd (h.ctorRows ⟨"F", [], []⟩ cexD_mergeRound_badRow hu).1 (by simp)

/-! ## The two matching statements

`FDatabase.patternHolds_MValidSubst` and `FDatabase.matchQuery_MValidQuerySubst` are
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

/-- **`FDatabase.patternHolds_MValidSubst` is false without `ValidEnv`.**
`MValidSubst.expr` carries `ValidEnv (e.freeVars db.env) db σ`, which pins `Env.dom σ` to
a permutation of the pattern's free variables; `(Expr.lit _).freeVars` is `[]` and `σ`
binds `x`. -/
theorem patternHolds_MValidSubst_false :
    ¬ ∀ (d : FDatabase), d.Inv → ∀ (p : Pattern) (σ : Env),
        patternHolds d p σ = true → MValidSubst d.toDatabase p σ := by
  intro H
  have hbad := H dEx dEx_inv (.expr (.lit (.int 0))) [("x", t0)] holds_lit
  cases hbad with
  | expr hv _ _ _ => simpa [Env.dom, Expr.freeVars] using hv.1

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

/-- **`FDatabase.matchQuery_MValidQuerySubst` is false without `Env.Agree`.**
`[("x", t0)]` is enumerated for `qEx`, and `ValidEnv` holds for it at *both* patterns — so
this is not the `ValidEnv` defect again. `MValidQuerySubst` needs one substitution per
pattern, each of length `1`, concatenated to give `σ`; that would make `σ` have length
`2`. -/
theorem matchQuery_MValidQuerySubst_false :
    ¬ ∀ (d : FDatabase), d.Inv → ∀ (q : Query) (σ : Env),
        σ ∈ matchQuery d q → MValidQuerySubst d.toDatabase q σ := by
  intro H
  obtain ⟨σs, hall, hu⟩ := H dEx dEx_inv qEx [("x", t0)] mem_matchQuery_ex
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

/-! ## `execM_reachable`'s `SetLegal` hypothesis cannot be dropped

`Proofs/Merge.lean`'s `execM_reachable` carries three hypotheses. Two are forced by the
counterexamples in its own docstring; this section is the third, which is the one that
would look droppable — no primitive is named, nothing is declared, and the program is four
commands long.

**The mechanism.** `(set (f) 0)` and `(set (f) 1)` leave two rows of `f` at the same
(empty) key with different outputs. `f` is undeclared, so `Signature.mergeOf` calls it a
constructor, and `MCong.fd` — which *is* the functional dependency — derives `0 = 1` from
the pair. `Cong` has no such rule: it relates only what `eqs` asserts and what congruence
of applications gives, and neither applies to two literals. So the query `((= 0 1))`
matches in the specification and not in the interpreter, the relational round adds the
head's term where the functional round adds nothing, and the two rounds differ.

`Database.CtorRows` is exactly the condition that excludes this, `Action.SetLegal` is how
the semantics enforces it statically (`Database.not_ctorRows_addRow` is the same failure at
its smallest), and `Proofs/Step.lean`'s `Database.CtorState` is where the two meet.

Unlike the rest of this file the witness declares no function at all, so there is no
`:merge` body and nothing here needs the nullary-key trick: `run` reduces by `rfl`
because every action is a `set` with an empty key and a literal value. -/

/-- `(rule ((= 0 1)) ((g)))`. Its head builds a term the interpreter's round cannot. -/
def badRule : Rule := ⟨[.eq (.lit (.int 0)) (.lit (.int 1))], [.expr (.app "g" [])]⟩

/-- `(set (f) 0) (set (f) 1) (rule ((= 0 1)) ((g))) (run)`.

Declares nothing, so `Program.CtorDecls` holds, and its two `set`s are the one thing
`Program.SetLegal` forbids. -/
def badProgram : Program :=
  [.action (.set "f" [] [.lit (.int 0)]), .action (.set "f" [] [.lit (.int 1)]),
    .rule badRule, .run]

/-- The state `badProgram`'s first three commands run to. -/
def badDb : Database :=
  { (Database.empty.addRow "f" [] [.lit (.int 0)]).addRow "f" [] [.lit (.int 1)] with
    rules := insert badRule ∅ }

theorem badDb_sig : badDb.sig.AllConstructors := by
  intro f
  simp [Signature.IsCtor, Signature.mergeOf, badDb, Database.empty]

theorem badDb_eqs : badDb.eqs = ∅ := by simp [badDb, Database.empty]

theorem badDb_terms : badDb.terms = {Term.lit (.int 0), Term.lit (.int 1)} := by
  simp [badDb, Database.addRow, Database.addTerms, Database.addTerm, Database.empty]
  ext t
  simp [Set.mem_insert_iff]
  tauto

theorem badDb_row0 : Row.mk "f" [] [Term.lit (.int 0)] ∈ badDb.rows := by
  simp [badDb, Database.addRow, Database.addTerms, Database.addTerm, Database.empty]

theorem badDb_row1 : Row.mk "f" [] [Term.lit (.int 1)] ∈ badDb.rows := by
  simp [badDb, Database.addRow, Database.addTerms, Database.addTerm, Database.empty]

theorem badDb_mem_rules {r : Rule} : r ∈ badDb.rules ↔ r = badRule := by simp [badDb]

theorem forall₂_eq_list {as bs : List Term} (h : List.Forall₂ (· = ·) as bs) : as = bs := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [hab, ih]

/-- The functional dependency fires on the two rows the `set`s wrote: `f` is undeclared,
so `mergeOf` calls it a constructor, and the keys are equal. -/
theorem badDb_mcong :
    MCong ((badDb.addTerm (.lit (.int 0))).addTerm (.lit (.int 1)))
      (.lit (.int 0)) (.lit (.int 1)) :=
  .fd (f := "f") (as := []) (bs := []) (a := [.lit (.int 0)]) (b := [.lit (.int 1)])
    (Or.inl (Or.inl badDb_row0)) (Or.inl (Or.inl badDb_row1))
    (by simp [Signature.IsCtor, Signature.mergeOf, badDb, Database.empty]) .nil (by simp)

/-- `Cong` does not fire: `eqs` is empty and no application is involved, so `Cong.le` at
equality closes it. -/
theorem badDb_not_cong :
    ¬ Cong ((badDb.addTerm (.lit (.int 0))).addTerm (.lit (.int 1)))
      (.lit (.int 0)) (.lit (.int 1)) := by
  intro h
  have heq : (Term.lit (.int 0)) = Term.lit (.int 1) :=
    Cong.le (R := (· = ·)) (fun a b hm => by simp [badDb_eqs] at hm) (fun _ _ => rfl)
      (fun _ _ h => h.symm) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
      (fun _ _ _ _ _ hl => by rw [forall₂_eq_list hl]) h
  simp at heq

theorem badDb_mvalid : MValidSubst badDb (.eq (.lit (.int 0)) (.lit (.int 1))) [] :=
  .eq (w := .lit (.int 0)) (t₁ := .lit (.int 0)) (t₂ := .lit (.int 1))
    ⟨by simp, by simp⟩ (by simp [badDb_terms]) rfl rfl
    (.refl (by simp [badDb_terms])) badDb_mcong

/-- No substitution matches on the interpreter's side: both operands are literals, so the
final premise is `CongOn badDb 0 1` whatever `σ` is. -/
theorem badDb_not_valid (σ : Env) :
    ¬ ValidSubst badDb (.eq (.lit (.int 0)) (.lit (.int 1))) σ := by
  intro h
  cases h with
  | @eq e₁ e₂ σ w t₁ t₂ hve hw hev₁ hev₂ hcw hct =>
    simp only [Expr.eval_lit, Option.some.injEq] at hev₁ hev₂
    subst hev₁
    subst hev₂
    exact badDb_not_cong hct

theorem badDb_mvalidQuery : MValidQuerySubst badDb badRule.query [] :=
  ⟨[[]], .cons badDb_mvalid .nil, .single []⟩

theorem badDb_not_validQuery (σ : Env) : ¬ ValidQuerySubst badDb badRule.query σ := by
  rintro ⟨σs, hall, hu⟩
  cases hall with
  | cons hp hrest =>
    cases hrest with
    | nil => cases hu with | single => exact badDb_not_valid _ hp

theorem badDb_ruleResults : ruleResults badDb badRule = ∅ := by
  ext d
  simp only [ruleResults, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨σ, hq, -⟩
  exact badDb_not_validQuery σ hq

/-- The functional round adds nothing: the only rule's query has no match. -/
theorem badDb_runRules_terms : (runRules badDb).terms = badDb.terms := by
  have hS : {d | ∃ r ∈ badDb.rules, d ∈ ruleResults badDb r} = ∅ := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨r, hr, hd⟩
    rw [badDb_mem_rules] at hr
    subst hr
    rw [badDb_ruleResults] at hd
    exact hd
  rw [runRules, hS]
  simp

/-- The relational round does add something: `MCong` matches the query, so the head runs
and `g` appears. -/
theorem badDb_runRules_mem : Term.app "g" [] ∈ (RunRules badDb).terms := by
  have hstep : evalLocalActions badDb badRule.actions ([] : Env) =
      some { ({ badDb with env := badDb.env ++ ([] : Env) }).addTerm (Term.app "g" []) with
        env := badDb.env, rules := badDb.rules } := by
    have hact : evalAction { badDb with env := badDb.env ++ ([] : Env) }
        (.expr (.app "g" []))
        = some (({ badDb with env := badDb.env ++ ([] : Env) }).addTerm (.app "g" [])) := by
      rw [evalAction, Expr.eval_app_ctor (by simp [Prim.ofName])
        (by simp [Signature.IsCtor, Signature.mergeOf, badDb, Database.empty])]
      rfl
    rw [evalLocalActions, show badRule.actions = [Action.expr (.app "g" [])] from rfl,
      evalActions_cons, hact]
    rfl
  set d : Database := { ({ badDb with env := badDb.env ++ ([] : Env) }).addTerm
    (Term.app "g" []) with env := badDb.env, rules := badDb.rules } with hdef
  have hmemS : d ∈ {d | ∃ r ∈ badDb.rules, d ∈ RuleResults badDb r} :=
    ⟨badRule, badDb_mem_rules.mpr rfl, [], badDb_mvalidQuery, hstep⟩
  have hmemd : Term.app "g" [] ∈ d.terms := Database.mem_addTerm _ _
  exact Or.inr (Set.mem_biUnion hmemS hmemd)

theorem badDb_runRules_ne : RunRules badDb ≠ runRules badDb := by
  intro h
  have hmem : Term.app "g" [] ∈ badDb.terms := by
    rw [← badDb_runRules_terms, ← h]; exact badDb_runRules_mem
  rw [badDb_terms] at hmem
  simp at hmem

theorem badProgram_run : run badProgram = some (runRules badDb) := rfl

theorem badProgram_ctorDecls : badProgram.CtorDecls := by
  intro c hc
  simp only [badProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> trivial

/-- **The state `badProgram` runs to is not one the relation reaches.**

The first three commands are forced — `CmdStep.stepCmd_eq` reads each of them back as
`stepCmd`, using that `MergeClosure` is the identity on a constructor signature — and at
the fourth `RunStep.eq_runRules` pins the result to `RunRules badDb`, which
`badDb_runRules_ne` says is not `runRules badDb`. -/
theorem badProgram_not_programStep :
    ¬ ProgramStep Database.empty badProgram (runRules badDb) := by
  intro h
  simp only [badProgram] at h
  obtain ⟨d₁, h₀, k₁⟩ := h.cons_inv
  obtain ⟨d₂, h₁, k₂⟩ := k₁.cons_inv
  obtain ⟨d₃, h₂, k₃⟩ := k₂.cons_inv
  obtain ⟨d₄, h₃, k₄⟩ := k₃.cons_inv
  have hempty : Database.empty.sig.AllConstructors := Database.CtorState.empty.sig
  have e₀ : d₁ = Database.empty.addRow "f" [] [Term.lit (.int 0)] :=
    (Option.some.inj (h₀.stepCmd_eq hempty (by simp))).symm
  subst e₀
  have e₁ : d₂ = (Database.empty.addRow "f" [] [Term.lit (.int 0)]).addRow "f" []
      [Term.lit (.int 1)] :=
    (Option.some.inj (h₁.stepCmd_eq hempty (by simp))).symm
  subst e₁
  have e₂ : d₃ = badDb :=
    (Option.some.inj (h₂.stepCmd_eq hempty (by simp))).symm
  subst e₂
  have e₃ := k₄.nil_inv
  subst e₃
  cases h₃ with
  | run hrun => exact badDb_runRules_ne (RunStep.eq_runRules badDb_sig hrun).symm

/-- **`execM_reachable`'s `Program.SetLegal` hypothesis is necessary.** There is a program
satisfying the other one — it declares only constructors — whose `exec` state no
`ProgramStep` reaches.

`exec_toDatabase` carries `badProgram_run` across to the interpreter, so this refutes the
theorem in the shape it is stated, not merely the `run` half of it. -/
theorem execM_reachable_needs_setLegal :
    ∃ (p : Program) (d : FDatabase), p.CtorDecls ∧ exec p = some d ∧
      ¬ ProgramStep FDatabase.empty.toDatabase p d.toDatabase := by
  have hmap : (exec badProgram).map FDatabase.toDatabase = some (runRules badDb) := by
    rw [exec_toDatabase]; exact badProgram_run
  obtain ⟨d, hd, hdd⟩ := Option.map_eq_some_iff.mp hmap
  refine ⟨badProgram, d, badProgram_ctorDecls, hd, ?_⟩
  rw [FDatabase.toDatabase_empty, hdd]
  exact badProgram_not_programStep

/-! ## `CmdStep.mono_recorded` at `.decl`

The two witnesses that bound the one open case of `CmdStep.mono_recorded`.

`Database.Recorded` reads a key up to `MCong`, and `MCong.fd` fires only at a
constructor, so declaring `f` `:merge` can take a derivation away. The first witness says
the `.decl` case therefore needs a hypothesis. The second says the obvious one — the
specification witness holds no row of `f` — is not available: a rule head may name a
function no command has declared, and the specification's stale reads fire such a rule
where the interpreter does not, so the witness holds a row of `f` while
`Cmd.DeclUnused`, which is checked at the *interpreter's* state, still passes. -/

/-! ### The `.decl` case needs a hypothesis -/

def d0 : Term := .lit (.int 0)
def d1 : Term := .lit (.int 1)
def d2 : Term := .lit (.int 2)

def declTerms : Set Term := {d0, d1, d2}

/-- The implementation side: one row of `g`, keyed at `d0`. -/
def declA : Database := ⟨fun _ => none, declTerms, {⟨"g", [d0], [d2]⟩}, ∅, [], ∅⟩

/-- The specification side: the same row keyed at `d1` instead — a rebuild's re-keying —
plus the two rows of `f` that make `d0` and `d1` congruent. -/
def declC : Database :=
  ⟨fun _ => none, declTerms, {⟨"f", [], [d0]⟩, ⟨"f", [], [d1]⟩, ⟨"g", [d1], [d2]⟩}, ∅, [], ∅⟩

/-- `(function f () i64 :no-merge)`. -/
def declDecl : FnDecl := ⟨0, 1, some .noMerge⟩

def declB : Database := { declA with sig := Function.update declA.sig "f" (some declDecl) }
def declD : Database := { declC with sig := Function.update declC.sig "f" (some declDecl) }

theorem declTerms_subterms : ∀ t ∈ declTerms, t.subterms ⊆ declTerms := by
  intro t ht s hs
  simp only [declTerms, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl <;> cases hs <;> simp [declTerms, d0, d1, d2]

theorem declA_solid : declA.Solid := by
  refine ⟨⟨declTerms_subterms, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp; exact absurd hp (by simp [declA])
  · intro b hb; exact absurd hb (by simp [declA])
  · intro r hr
    simp only [declA, Set.mem_singleton_iff] at hr
    subst hr
    refine ⟨fun a ha => ?_, fun v hv => ?_⟩
    · rw [List.mem_singleton] at ha; subst ha; simp [declA, declTerms]
    · rw [List.mem_singleton] at hv; subst hv; simp [declA, declTerms]
  · intro r hr
    obtain ⟨-, hmem⟩ := hr
    simp only [declA, declTerms, Set.mem_insert_iff, Set.mem_singleton_iff, d0, d1, d2] at hmem
    rcases hmem with h | h | h <;> exact absurd h (by simp)

/-- Before the declaration `f` is a constructor, so its two rows are an `fd` premise. -/
theorem declC_isCtor : declC.sig.IsCtor "f" := rfl

theorem declC_mcong : MCong declC d0 d1 :=
  MCong.fd (f := "f") (as := []) (bs := []) (a := [d0]) (b := [d1])
    (by simp [declC]) (by simp [declC]) declC_isCtor .nil (by simp)

theorem declA_recorded : declA.Recorded declC := by
  refine ⟨subset_rfl, ?_, subset_rfl⟩
  intro r hr
  simp only [declA, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨[d1], .cons declC_mcong .nil, by simp [declC]⟩

/-- After it, `f` is not a constructor and nothing else relates the two keys. -/
theorem declD_not_mcong : ¬ MCong declD d0 d1 := by
  intro h
  have hEq : d0 = d1 := by
    refine MCong.le (R := fun a b => a = b) (by simp [declD, declC]) (fun _ _ => rfl)
      (fun _ _ h => h.symm) (fun _ _ _ h₁ h₂ => h₁.trans h₂) ?_ h
    intro fn as bs a b u v hra hrb hu hl huv
    simp only [declD, declC, Set.mem_insert_iff, Set.mem_singleton_iff,
      Row.mk.injEq] at hra hrb
    rcases hra with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
    · exact absurd hu (by simp [declD, Signature.IsCtor, Signature.mergeOf, declDecl])
    · exact absurd hu (by simp [declD, Signature.IsCtor, Signature.mergeOf, declDecl])
    · rcases hrb with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, rfl⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · rw [show ([d2] : List Term).zip [d2] = [(d2, d2)] from rfl, List.mem_singleton,
          Prod.mk.injEq] at huv
        exact huv.1.trans huv.2.symm
  simp [d0, d1] at hEq

theorem declB_not_recorded : ¬ declB.Recorded declD := by
  intro h
  obtain ⟨bs, hl, hrow⟩ := h.rows ⟨"g", [d0], [d2]⟩ (by simp [declB, declA])
  simp only [declD, declC, Set.mem_insert_iff, Set.mem_singleton_iff, Row.mk.injEq] at hrow
  rcases hrow with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨-, rfl, -⟩
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · cases hl with
    | cons hab _ => exact declD_not_mcong hab

/-- **`CmdStep.mono_recorded` is false at `.decl`.** Every hypothesis it carries holds and
the conclusion does not, so the case needs a hypothesis about `f` that the theorem does
not yet have. -/
theorem mono_recorded_decl_false :
    ∃ (A C B : Database) (f : FnName) (dc : FnDecl),
      A.Recorded C ∧ A.sig = C.sig ∧ A.env = C.env ∧ A.rules = C.rules ∧ A.Solid ∧
      CmdStep A (.decl f dc) B ∧
      ¬ ∃ D, CmdStep C (.decl f dc) D ∧ B.Recorded D :=
  ⟨declA, declC, declB, "f", declDecl, declA_recorded, rfl, rfl, rfl, declA_solid, .decl, by
    rintro ⟨D, hD, hrec⟩
    cases hD
    exact declB_not_recorded hrec⟩

/-! ### …and the hypothesis it needs is not available -/

/-- `(function M () i64 :merge new)`. -/
def staleDecl : FnDecl := ⟨0, 1, some (.merge [] [.var "new"])⟩

/-- `(rule ((= 0 (M))) ((f)))`. Its head names `f`, which nothing has declared; only a
`set` is constrained by `Action.SetLegal`, so the rule is legal. -/
def staleRule : Rule := ⟨[.values [.lit (.int 0)] "M" []], [.expr (.app "f" [])]⟩

/-- The row `(set (M) 0)` writes. The merge phase overwrites it in the interpreter and
leaves it standing in the specification, which never removes a row. -/
def staleRow : Row := ⟨"M", [], [.lit (.int 0)]⟩

/-- The constructor row of `(f)`, which only the specification ever builds. -/
def staleFRow : Row := ⟨"f", [], [.app "f" []]⟩

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
  refine ⟨trivial, ?_, ?_, ⟨trivial, trivial⟩, trivial, trivial⟩ <;>
    · change ¬ Signature.IsCtor staleSig "M"
      rw [Signature.IsCtor, staleSig_mergeOf]
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

/-- **Every specification run of `staleProgram` holds a row of the undeclared `"f"`.**

`(set (M) 0)`'s row survives into the round, `MValidSubst.values` reads it — the
specification's lookup returns any recorded output, not the current one — and the rule's
head builds `(f)` together with its constructor row. The interpreter's own merge phase
replaced that row by `(M) ↦ 1`, so the rule does not fire there and
`Cmd.DeclUnused (.decl "f" _)` still holds of the interpreter's state: appending
`.decl "f" dc` leaves `FDatabase.ProgramLegal` satisfied.

So `CmdStep.mono_recorded`'s missing hypothesis cannot be "the specification witness holds
no row of `f`". -/
theorem undeclared_row_reachable {C : Database}
    (h : ProgramStep FDatabase.empty.toDatabase staleProgram C) :
    C.sig "f" = none ∧ staleFRow ∈ C.rows := by
  rw [staleProgram] at h
  obtain ⟨C1, h1, h⟩ := h.cons_inv
  obtain ⟨C2, h2, h⟩ := h.cons_inv
  obtain ⟨C3, h3, h⟩ := h.cons_inv
  obtain ⟨C4, h4, h⟩ := h.cons_inv
  obtain ⟨C5, h5, h⟩ := h.cons_inv
  have e := h.nil_inv
  subst e
  have hs1 : C1.sig = staleSig := by rw [h1.sig]; rfl
  have hs2 : C2.sig = C1.sig := by rw [h2.sig]; rfl
  have hs3 : C3.sig = C2.sig := by rw [h3.sig]; rfl
  have hs4 : C4.sig = C3.sig := by rw [h4.sig]; rfl
  have hf : C4.sig "f" = none := by
    rw [hs4, hs3, hs2, hs1, staleSig, Function.update_of_ne (by decide)]
  have hctor : C4.sig.IsCtor "f" := by
    change Signature.mergeOf _ "f" = none
    rw [Signature.mergeOf, hf]
    rfl
  -- the row `(set (M) 0)` wrote is still standing at `C4`
  have hstale : staleRow ∈ C4.rows := by
    have hd : staleRow ∈ C2.rows := by
      cases h2 with
      | action ha hm =>
        refine (MergeClosure.contained hm).rows ?_
        rw [evalAction, Option.bind_eq_some_iff] at ha
        obtain ⟨as, has, ha⟩ := ha
        rw [Option.map_eq_some_iff] at ha
        obtain ⟨vs, hvs, rfl⟩ := ha
        cases has
        cases hvs
        exact Set.mem_insert _ _
    exact (CmdStep.contained h4).rows ((CmdStep.contained h3).rows hd)
  have hrule : staleRule ∈ C4.rules := by cases h4; exact Set.mem_insert _ _
  refine ⟨?_, ?_⟩
  · rw [h5.sig]; exact hf
  cases h5 with
  | run hrun =>
    refine (MergeClosure.contained hrun).rows ?_
    have heval : Expr.eval C4.sig (.app "f" []) (C4.env ++ []) = some (.app "f" []) := by
      rw [Expr.eval]
      simp only [show Prim.ofName "f" = none from rfl, if_pos hctor, Expr.evalList]
      rfl
    have hmemS :
        ({ ({ C4 with env := C4.env ++ [] }.addTerm (.app "f" [])) with
            env := C4.env, rules := C4.rules } : Database)
          ∈ {d | ∃ r ∈ C4.rules, d ∈ RuleResults C4 r} := by
      refine ⟨staleRule, hrule, [], ⟨[[]], ?_, .single []⟩, ?_⟩
      · exact List.Forall₂.cons
          (MValidSubst.values (us := [.lit (.int 0)]) (ts := []) (ws := [.lit (.int 0)])
            (bs := []) ⟨by simp [Env.dom], by simp⟩ rfl rfl .nil
            (.cons (.refl (Database.mem_terms_addTerms (by simp))) .nil) hstale)
          List.Forall₂.nil
      · change (evalActions { C4 with env := C4.env ++ [] } staleRule.actions).map _ = some _
        rw [show staleRule.actions = [Action.expr (.app "f" [])] from rfl,
          evalActions, evalAction,
          show ((Expr.app "f" []).eval ({ C4 with env := C4.env ++ [] } : Database).sig
              ({ C4 with env := C4.env ++ [] } : Database).env)
            = some (.app "f" []) from heval]
        rfl
    exact (Database.Contained.mem_sUnion hmemS).rows (Or.inr ⟨rfl, Term.IsSubterm.refl _⟩)

end Falsity
end Egglog
