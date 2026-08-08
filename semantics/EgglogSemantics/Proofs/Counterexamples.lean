import EgglogSemantics.Proofs.Merge

/-!
# Machine-checked falsity witnesses for `Proofs/Merge.lean`'s refinement chain

Two defects, each with a concrete compiling counterexample, plus three refutations of
statements that were tried without the hypotheses they now carry. Nothing here is
admitted, nothing uses `native_decide`, and no `Classical.choice` enters beyond what
`Mathlib` already pulls in.

There was a third defect — `execCmdM_contained` was false at `.action`, because the
interpreter runs a merge phase after a top-level action and `CmdStep.action` had none.
That was a defect in the *specification*: egglog compiles a bare action into a one-rule
run and every rule-set run ends in `merge_all`. `CmdStep.action` now carries a
`MergeClosure` phase, so the witness no longer witnesses anything and has been removed
along with its data; `FDatabase.execCmdM_contained` is proved.

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
