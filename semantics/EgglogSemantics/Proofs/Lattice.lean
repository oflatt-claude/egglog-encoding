import EgglogSemantics.Impl.Check
import EgglogSemantics.Proofs.Merge

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# `execM_current_of_lattice` is **false**

Machine-checked refutations of `Proofs/Merge.lean`'s `execM_current_of_lattice`, each
isolating one hypothesis the statement is missing.

`execM_contained` is a containment, and a do-nothing implementation satisfies it, so the
chain wants a completeness companion saying the interpreter keeps the `le`-greatest
recorded output at each key class rather than merely some subset. `Database.Current` is
that companion for a merge that is a join. The statement as written does not hold, and no
rearrangement of its existing hypotheses rescues it: `hanti` and `hjoin` do not axiomatize
"join", and `hjoin` says nothing at all about a merge that fails to produce a value.
-/

namespace Egglog
namespace Lattice

/-! ## Inversion helpers for `Expr.eval`

Reading an evaluation backwards, one syntactic form at a time. A nullary application is
the interesting one: `Expr.eval` builds it only at a constructor, so the other two merge
kinds are ruled out by the evaluation succeeding at all. -/

theorem mevalList_nil {sig : Signature} {σ : Env} {ts : List Term}
    (h : Expr.evalList sig [] σ = some ts) : ts = [] :=
  (Option.some.inj h).symm

theorem meval_lit {sig : Signature} {σ : Env} {l : Lit} {t : Term}
    (h : Expr.eval sig (.lit l) σ = some t) : t = .lit l :=
  (Option.some.inj h).symm

theorem meval_var {sig : Signature} {σ : Env} {v : Var} {t : Term}
    (h : Expr.eval sig (.var v) σ = some t) : Env.lookup v σ = some t := h

theorem meval_nullary {sig : Signature} {σ : Env} {f : FnName} {t : Term}
    (hp : Prim.ofName f = none) (h : Expr.eval sig (.app f []) σ = some t) :
    t = .app f [] := by
  cases hu : sig.mergeOf f with
  | union =>
    rw [Expr.eval_app_ctor hp hu, Expr.evalList_nil, Option.map_some,
      Option.some.injEq] at h
    exact h.symm
  | merge b r => rw [Expr.eval_app_merge hp hu] at h; simp at h
  | noMerge => rw [Expr.eval_app_noMerge hp hu] at h; simp at h

theorem mevalList_one {sig : Signature} {σ : Env} {e : Expr} {ts : List Term}
    (h : Expr.evalList sig [e] σ = some ts) :
    ∃ t, ts = [t] ∧ Expr.eval sig e σ = some t := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, hrest⟩ := h
  obtain ⟨us, hus, heq⟩ := Option.map_eq_some_iff.mp hrest
  exact ⟨t, by rw [← heq, mevalList_nil hus], ht⟩

theorem mevalList_two {sig : Signature} {σ : Env} {e₁ e₂ : Expr} {ts : List Term}
    (h : Expr.evalList sig [e₁, e₂] σ = some ts) :
    ∃ u v, ts = [u, v] ∧ Expr.eval sig e₁ σ = some u ∧ Expr.eval sig e₂ σ = some v := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨u, hu, hrest⟩ := h
  obtain ⟨vs, hvs, heq⟩ := Option.map_eq_some_iff.mp hrest
  obtain ⟨v, rfl, hv⟩ := mevalList_one hvs
  exact ⟨u, v, heq.symm, hu, hv⟩

theorem mevalList_single_nullary {sig : Signature} {σ : Env} {f : FnName} {vs : List Term}
    (hp : Prim.ofName f = none) (h : Expr.evalList sig [.app f []] σ = some vs) :
    vs = [.app f []] := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, hrest⟩ := h
  obtain ⟨us, hus, heq⟩ := Option.map_eq_some_iff.mp hrest
  rw [← heq, mevalList_nil hus, meval_nullary hp ht]

/-! ## Only the declared name has a `:merge` body -/

theorem mergeOf_update_inv {dc : FnDecl} {f g : FnName} {body₀ body : List Action}
    {res₀ res : List Expr} (hdc : dc.merge = MergeSpec.merge body₀ res₀)
    (h : Signature.mergeOf (Function.update (fun _ => none) f (some dc)) g =
      MergeSpec.merge body res) : body = body₀ ∧ res = res₀ := by
  rw [Signature.mergeOf, Function.update_apply] at h
  by_cases hg : g = f
  · rw [if_pos hg] at h
    change dc.merge = _ at h
    rw [hdc] at h
    exact ⟨((MergeSpec.merge.injEq .. ▸ h : _ ∧ _).1).symm,
      ((MergeSpec.merge.injEq .. ▸ h : _ ∧ _).2).symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## The statement under test -/

/-- `Proofs/Merge.lean`'s `execM_current_of_lattice`, restated with every binder
explicit so that it can be negated.  Nothing has been weakened: `hexec`, `hanti`,
`hjoin`, `hmerge` and `hrow` are the theorem's five hypotheses verbatim. -/
def CurrentOfLattice : Prop :=
  ∀ (p : Program) (d : FDatabase) (le : List Term → List Term → Prop),
    execM p = some d →
    (∀ x y, le x y → le y x → x = y) →
    (∀ (f : FnName) (body : List Action) (res : List Expr) (a b vs : List Term),
      d.sig.mergeOf f = MergeSpec.merge body res →
      (∃ e, evalActions { d.toDatabase with env := mergeEnv a b } body = some e ∧
        Expr.evalList e.sig res e.env = some vs) → le a vs ∧ le b vs) →
    ∀ (f : FnName) (as vs : List Term) (body : List Action) (res : List Expr),
      d.sig.mergeOf f = MergeSpec.merge body res →
      Row.mk f as vs ∈ d.rows →
      ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ db.Current le f as vs

/-! ## Shared vocabulary -/

def tA : Term := .app "a" []
def tB : Term := .app "b" []
def eA : Expr := .app "a" []
def eB : Expr := .app "b" []

/-! ## Counterexample A — nothing forces `le` to be reflexive

`Database.Current db le f as vs` is `db.Out f as vs ∧ ∀ ws, db.Out f as ws → le ws vs`;
instantiating the second conjunct at `ws := vs` and feeding it the first gives
`le vs vs`.  `hanti` is an antisymmetry and `hjoin` is an *implication* — "if the body
computes `vs` from `a` and `b` then `vs` is above both" — so a merge whose body never
computes anything satisfies `hjoin` vacuously, and `le := fun _ _ => False` then
satisfies both hypotheses. -/

/-- `(function f () i64 :merge (min 1 (a)))`.  The result column is stuck at *every*
pair of operands: `min` is an `i64` primitive and `(a)` is a constructor term, so
`Prim.apply` is `none` however the collision arose. -/
def stuckDecl : FnDecl :=
  { arity := 0, outArity := 1,
    merge := .merge [] [.app "min" [.lit (.int 1), eA]] }

/-- `(function f () i64 :merge (min 1 (a)))  (set (f) (a))`. -/
def pA : Program := [.decl "f" stuckDecl, .action (.set "f" [] [eA])]

def dA : FDatabase := (execM pA).getD FDatabase.empty

theorem execM_pA : execM pA = some dA := rfl

theorem dA_sig : dA.sig = Function.update (fun _ => none) "f" (some stuckDecl) := rfl

theorem dA_row : (Row.mk "f" [] [tA]) ∈ dA.rows := by decide

theorem dA_mergeOf {g : FnName} {body : List Action} {res : List Expr}
    (h : dA.sig.mergeOf g = MergeSpec.merge body res) :
    res = [.app "min" [.lit (.int 1), eA]] :=
  (mergeOf_update_inv (f := "f") rfl (dA_sig ▸ h)).2

/-- The stuck merge, machine-checked: no `a`, `b`, `vs` satisfy `hjoin`'s premise. -/
theorem dA_no_merge_value {a b vs : List Term} {body : List Action} {res : List Expr}
    (hres : res = [.app "min" [.lit (.int 1), eA]])
    (he : ∃ e, evalActions { dA.toDatabase with env := mergeEnv a b } body = some e ∧
      Expr.evalList e.sig res e.env = some vs) : False := by
  obtain ⟨e, -, hev⟩ := he
  subst hres
  obtain ⟨t, rfl, hv⟩ := mevalList_one hev
  rw [Expr.eval_app_prim (p := Prim.intMin) rfl, Option.bind_eq_some_iff] at hv
  obtain ⟨ts, hts, happ⟩ := hv
  obtain ⟨u, v, rfl, h1, h2⟩ := mevalList_two hts
  rw [meval_lit h1, meval_nullary (show Prim.ofName "a" = none from rfl) h2,
    show Prim.intMin.apply [Term.lit (Lit.int 1), Term.app "a" []] = none from rfl] at happ
  simp at happ

/-- **Refutation A.** -/
theorem currentOfLattice_false : ¬ CurrentOfLattice := by
  intro H
  obtain ⟨_, -, hcur⟩ :=
    H pA dA (fun _ _ => False) execM_pA (fun _ _ h _ => h.elim)
      (fun _ _ _ _ _ _ hg he => (dA_no_merge_value (dA_mergeOf hg) he).elim)
      "f" [] [tA] _ _ rfl dA_row
  exact hcur.2 _ hcur.1


/-! ## Counterexample B — `le` is a genuine partial order and the statement still fails

`(function f () i64 :merge (min old new))` is the shape `tests/interval.egg` uses, and
`min` really is a join for the order `leB` below (reflexive, transitive, antisymmetric).
The program `set`s two *constructor* terms into it.  The model has no sort discipline —
`Prim.apply` is `none` on a non-literal operand, which its own docstring records — so the
collision is unresolvable, `mergeOneWith` returns `none`, the pass reports `settled`, and
the interpreter's final state holds **both** rows at the one key class.  `hjoin` says
nothing about that, because it only constrains merges that *do* produce a value. -/

theorem prim_intMin_inv {t₁ t₂ v : Term} (h : Prim.intMin.apply [t₁, t₂] = some v) :
    ∃ m n : Int, t₁ = .lit (.int m) ∧ t₂ = .lit (.int n) ∧ v = .lit (.int (min m n)) := by
  match t₁, t₂, h with
  | .lit (.int m), .lit (.int n), h => exact ⟨m, n, rfl, rfl, (Option.some.inj h).symm⟩
  | .lit (.int _), .app _ _, h => simp [Prim.apply] at h
  | .app _ _, _, h => simp [Prim.apply] at h

/-- `mergeEnv` binds `old`/`new` only when both outputs are single columns; at any other
shape either the environment does not bind `old` at all, or both sides have at least two
columns.  This is the only fact about `mergeEnv` the join hypothesis needs, and it avoids
reasoning about the indexed names `old0`, `new0`, … at an unbounded index. -/
theorem mergeEnv_cases (a b : List Term) :
    (∃ x y, a = [x] ∧ b = [y]) ∨ Env.lookup "old" (mergeEnv a b) = none
      ∨ (2 ≤ a.length ∧ 2 ≤ b.length) := by
  match a, b with
  | [], _ => exact Or.inr (Or.inl rfl)
  | [_], [] => exact Or.inr (Or.inl rfl)
  | [x], [y] => exact Or.inl ⟨x, y, rfl, rfl⟩
  | [_], _ :: _ :: _ => exact Or.inr (Or.inl rfl)
  | _ :: _ :: _, [] => exact Or.inr (Or.inl rfl)
  | _ :: _ :: _, [_] => exact Or.inr (Or.inl rfl)
  | _ :: _ :: _, _ :: _ :: _ => exact Or.inr (Or.inr ⟨by simp, by simp⟩)

/-- `x` is a single `i64` column. -/
def IntSing (x : List Term) : Prop := ∃ m : Int, x = [.lit (.int m)]

theorem not_intSing_of_two {x : List Term} (h : 2 ≤ x.length) : ¬ IntSing x := by
  rintro ⟨m, rfl⟩; simp at h

/-- The order `min` is a join for: numerically reversed on single `i64` columns, with
everything that is not a single `i64` column strictly below every one that is. -/
def leB (x y : List Term) : Prop :=
  x = y ∨ (∃ m n : Int, x = [.lit (.int m)] ∧ y = [.lit (.int n)] ∧ n ≤ m)
        ∨ (IntSing y ∧ ¬ IntSing x)

theorem leB_refl (x : List Term) : leB x x := Or.inl rfl

theorem leB_trans (x y z : List Term) (h₁ : leB x y) (h₂ : leB y z) : leB x z := by
  rcases h₁ with rfl | ⟨m, n, hx, hy, hmn⟩ | ⟨hy1, hx1⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨m', n', hy', hz', hmn'⟩ | ⟨_, hy2⟩
    · exact Or.inr (Or.inl ⟨m, n, hx, hy, hmn⟩)
    · rw [hy] at hy'
      obtain rfl : n = m' := by injection (List.cons.inj hy').1 with h; injection h
      exact Or.inr (Or.inl ⟨m, n', hx, hz', le_trans hmn' hmn⟩)
    · exact absurd ⟨n, hy⟩ hy2
  · rcases h₂ with rfl | ⟨m', n', hy', hz', _⟩ | ⟨hz2, hy2⟩
    · exact Or.inr (Or.inr ⟨hy1, hx1⟩)
    · exact Or.inr (Or.inr ⟨⟨n', hz'⟩, hx1⟩)
    · exact absurd hy1 hy2

theorem leB_anti (x y : List Term) (h₁ : leB x y) (h₂ : leB y x) : x = y := by
  rcases h₁ with rfl | ⟨m, n, hx, hy, hmn⟩ | ⟨hy1, hx1⟩
  · rfl
  · rcases h₂ with h | ⟨m', n', hy', hx', hmn'⟩ | ⟨hx2, hy2⟩
    · exact h.symm
    · rw [hx] at hx'; rw [hy] at hy'
      obtain rfl : m = n' := by injection (List.cons.inj hx').1 with h; injection h
      obtain rfl : n = m' := by injection (List.cons.inj hy').1 with h; injection h
      rw [hx, hy, le_antisymm hmn hmn']
    · exact absurd ⟨n, hy⟩ hy2
  · rcases h₂ with h | ⟨_, n', hy', hx', _⟩ | ⟨hx2, _⟩
    · exact h.symm
    · exact absurd ⟨n', hx'⟩ hx1
    · exact absurd hx2 hx1

/-- `(function f () i64 :merge (min old new))`. -/
def minDecl : FnDecl :=
  { arity := 0, outArity := 1,
    merge := .merge [] [.app "min" [.var "old", .var "new"]] }

/-- `(function f () i64 :merge (min old new))  (set (f) (a))  (set (f) (b))`. -/
def pB : Program :=
  [.decl "f" minDecl, .action (.set "f" [] [eA]), .action (.set "f" [] [eB])]

def dB : FDatabase := (execM pB).getD FDatabase.empty

theorem execM_pB : execM pB = some dB := rfl

theorem dB_sig : dB.sig = Function.update (fun _ => none) "f" (some minDecl) := rfl

/-- **The interpreter's final state holds both rows at the one key class.** -/
theorem dB_rowA : (Row.mk "f" [] [tA]) ∈ dB.rows := by decide

theorem dB_rowB : (Row.mk "f" [] [tB]) ∈ dB.rows := by decide

theorem dB_mergeOf : dB.sig.mergeOf "f" =
    MergeSpec.merge [] [.app "min" [.var "old", .var "new"]] := rfl

/-- **`hjoin` holds**, and not vacuously: `min` is a join for `leB`. -/
theorem dB_join (g : FnName) (body : List Action) (res : List Expr) (a b vs : List Term)
    (hg : dB.sig.mergeOf g = MergeSpec.merge body res)
    (he : ∃ e, evalActions { dB.toDatabase with env := mergeEnv a b } body = some e ∧
      Expr.evalList e.sig res e.env = some vs) : leB a vs ∧ leB b vs := by
  obtain ⟨hbody, hres⟩ := mergeOf_update_inv (f := "f") rfl (dB_sig ▸ hg)
  subst hbody; subst hres
  obtain ⟨e, hstep, hev⟩ := he
  rw [evalActions_nil, Option.some.injEq] at hstep
  subst hstep
  obtain ⟨t, rfl, hv⟩ := mevalList_one hev
  rw [Expr.eval_app_prim (p := Prim.intMin) rfl, Option.bind_eq_some_iff] at hv
  obtain ⟨ts, hts, happ⟩ := hv
  obtain ⟨u, v, rfl, hva, hvb⟩ := mevalList_two hts
  have h1 : Env.lookup "old" (mergeEnv a b) = some _ := meval_var hva
  have h2 : Env.lookup "new" (mergeEnv a b) = some _ := meval_var hvb
  obtain ⟨m, n, ht1, ht2, rfl⟩ := prim_intMin_inv happ
  rcases mergeEnv_cases a b with ⟨x, y, rfl, rfl⟩ | hnone | ⟨ha2, hb2⟩
  · rw [show mergeEnv [x] [y] = [("old", x), ("new", y)] from rfl] at h1 h2
    rw [show Env.lookup "old" [("old", x), ("new", y)] = some x from rfl] at h1
    rw [show Env.lookup "new" [("old", x), ("new", y)] = some y from rfl] at h2
    obtain rfl : x = _ := Option.some.inj h1
    obtain rfl : y = _ := Option.some.inj h2
    rw [ht1, ht2]
    exact ⟨Or.inr (Or.inl ⟨m, min m n, rfl, rfl, min_le_left m n⟩),
      Or.inr (Or.inl ⟨n, min m n, rfl, rfl, min_le_right m n⟩)⟩
  · rw [hnone] at h1; simp at h1
  · exact ⟨Or.inr (Or.inr ⟨⟨min m n, rfl⟩, not_intSing_of_two ha2⟩),
      Or.inr (Or.inr ⟨⟨min m n, rfl⟩, not_intSing_of_two hb2⟩)⟩


/-- `hjoin` is **not** vacuous here: `min` really does merge two `i64` columns, and the
value it produces is above both for `leB`. -/
theorem dB_join_nonvacuous :
    ∃ e, evalActions
        { dB.toDatabase with env := mergeEnv [.lit (.int 1)] [.lit (.int 2)] } [] = some e ∧
      Expr.evalList e.sig [.app "min" [.var "old", .var "new"]] e.env
        = some [.lit (.int 1)] :=
  ⟨_, rfl, rfl⟩

/-- **Every state the specification reaches on `pB` records the second value too.**
The last command's `set` writes it and `MergeClosure` never removes a row. -/
theorem pB_reaches_rowB {db : Database}
    (h : ProgramStep FDatabase.empty.toDatabase pB db) :
    Row.mk "f" [] [tB] ∈ db.rows := by
  cases h with
  | cons _ r1 =>
    cases r1 with
    | cons _ r2 =>
      cases r2 with
      | cons h3 r3 =>
        cases r3 with
        | nil =>
          cases h3 with
          | action hact hcl =>
            simp only [evalAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hact
            obtain ⟨as, hargs, vs, hout, rfl⟩ := hact
            rw [show eB = Expr.app "b" [] from rfl] at hout
            rw [mevalList_nil hargs,
              mevalList_single_nullary (show Prim.ofName "b" = none from rfl) hout] at hcl
            exact (MergeClosure.contained hcl).rows (Set.mem_insert _ _)

/-- **Refutation B.**  `leB` is reflexive, transitive and antisymmetric, `hjoin` holds
non-vacuously, and the conclusion still fails: the interpreter's surviving row at the
class holds `(a)`, the specification also records `(b)` there, and `leB [(b)] [(a)]` is
false. -/
theorem currentOfLattice_false_partialOrder : ¬ CurrentOfLattice := by
  intro H
  obtain ⟨db, hstep, hcur⟩ :=
    H pB dB leB execM_pB leB_anti dB_join "f" [] [tA] _ _ dB_mergeOf dB_rowA
  have hbad := hcur.2 [tB] ⟨[], .nil, pB_reaches_rowB hstep⟩
  rcases hbad with h | ⟨_, _, h, _⟩ | ⟨⟨_, h⟩, _⟩ <;> simp [tA, tB] at h


/-! ## Counterexample C — the merge is total, `le` is reflexive, and transitivity is the
gap

`hjoin` says the merged value is *above both operands*.  For a chain of three collisions
that is not enough: the survivor is above the previous survivor, which is above the first
operand, and nothing lets those two steps compose.  `(function f () S :merge (C old new))`
with `C` a constructor is a **total** merge — it computes a value at every pair of single
columns — and the relation `leC` it generates is reflexive and antisymmetric but not
transitive. -/

def tD : Term := .app "d" []
def eD : Expr := .app "d" []

theorem size_cycle {u w p q p' q' : Term} {f g : FnName}
    (hu : u = Term.app f [p', q']) (hw : w = Term.app g [p, q])
    (hup : u = p ∨ u = q) (hwp : w = p' ∨ w = q') : False := by
  have h1 : sizeOf p' < sizeOf u := by rw [hu]; simp; omega
  have h2 : sizeOf q' < sizeOf u := by rw [hu]; simp; omega
  have h3 : sizeOf p < sizeOf w := by rw [hw]; simp; omega
  have h4 : sizeOf q < sizeOf w := by rw [hw]; simp; omega
  rcases hup with rfl | rfl <;> rcases hwp with rfl | rfl <;> omega

/-- `y` is a single column holding a binary `C`-application. -/
def CApp (y : List Term) : Prop := ∃ p q : Term, y = [.app "C" [p, q]]

/-- The relation `hjoin` generates for the merge `(C old new)`, closed under reflexivity
and nothing else.  Antisymmetric, **not** transitive. -/
def leC (x y : List Term) : Prop :=
  x = y ∨ (∃ p q : Term, y = [.app "C" [p, q]] ∧ (x = [p] ∨ x = [q]))
        ∨ (CApp y ∧ x.length ≠ 1)

theorem leC_refl (x : List Term) : leC x x := Or.inl rfl

theorem leC_anti (x y : List Term) (h₁ : leC x y) (h₂ : leC y x) : x = y := by
  rcases h₁ with rfl | ⟨p, q, hy, hx⟩ | ⟨⟨p, q, hy⟩, hxl⟩
  · rfl
  · rcases h₂ with h | ⟨p', q', hx', hy'⟩ | ⟨⟨p', q', hx'⟩, hyl⟩
    · exact h.symm
    · exfalso
      rw [hy] at hy'
      rcases hx with rfl | rfl <;> rw [List.cons.injEq] at hx' <;>
        rcases hy' with hy' | hy' <;> rw [List.cons.injEq] at hy' <;>
        exact size_cycle hx'.1 hy'.1.symm (by tauto) (by tauto)
    · exact absurd (hy ▸ rfl : y.length = 1) hyl
  · rcases h₂ with h | ⟨p', q', hx', hy'⟩ | ⟨⟨p', q', hx'⟩, hyl⟩
    · exact h.symm
    · exact absurd (hx' ▸ rfl : x.length = 1) hxl
    · exact absurd (hy ▸ rfl : y.length = 1) hyl

/-- `(function f () S :merge (C old new))`. -/
def cDecl : FnDecl :=
  { arity := 0, outArity := 1,
    merge := .merge [] [.app "C" [.var "old", .var "new"]] }

/-- Three `set`s at one key class, so the merge phase runs a chain of two collisions. -/
def pC : Program :=
  [.decl "f" cDecl, .action (.set "f" [] [eA]), .action (.set "f" [] [eB]),
   .action (.set "f" [] [eD])]

def dC : FDatabase := (execM pC).getD FDatabase.empty

theorem execM_pC : execM pC = some dC := rfl

theorem dC_sig : dC.sig = Function.update (fun _ => none) "f" (some cDecl) := rfl

theorem dC_mergeOf : dC.sig.mergeOf "f" =
    MergeSpec.merge [] [.app "C" [.var "old", .var "new"]] := rfl

/-- The value the interpreter's one surviving `f`-row holds.  Read off the interpreter
rather than written out, so that the refutation does not depend on which of the two
colliding rows `mergeEnv` calls `old` or which one the pass overwrites. -/
def vsC : List Term :=
  ((dC.rows.find? fun r => r.fn == "f").getD ⟨"f", [], []⟩).out

theorem dC_row : (Row.mk "f" [] vsC) ∈ dC.rows := by decide

/-- `[(a)]` is neither the survivor nor one of its two `C`-children. -/
def okA (vs : List Term) : Bool :=
  decide (vs ≠ [tA]) &&
    (match vs with
     | [.app "C" [p, q]] => decide (p ≠ tA) && decide (q ≠ tA)
     | _ => true)

theorem dC_okA : okA vsC = true := by decide

theorem not_leC_of_okA {vs : List Term} (h : okA vs = true) : ¬ leC [tA] vs := by
  rintro (rfl | ⟨p, q, rfl, hx⟩ | ⟨-, hlen⟩)
  · have h' : (decide (([tA] : List Term) ≠ [tA]) && true) = true := h
    simp at h'
  · have h' : (decide (([Term.app "C" [p, q]] : List Term) ≠ [tA]) &&
        (decide (p ≠ tA) && decide (q ≠ tA))) = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    rcases hx with h₂ | h₂
    · exact h'.2.1 (by simpa using h₂.symm)
    · exact h'.2.2 (by simpa using h₂.symm)
  · simp at hlen

/-- **`hjoin` holds**, and the merge is total: `(C old new)` computes a value at every
pair of single columns. -/
theorem dC_join (g : FnName) (body : List Action) (res : List Expr) (a b vs : List Term)
    (hg : dC.sig.mergeOf g = MergeSpec.merge body res)
    (he : ∃ e, evalActions { dC.toDatabase with env := mergeEnv a b } body = some e ∧
      Expr.evalList e.sig res e.env = some vs) : leC a vs ∧ leC b vs := by
  obtain ⟨hbody, hres⟩ := mergeOf_update_inv (f := "f") rfl (dC_sig ▸ hg)
  subst hbody; subst hres
  obtain ⟨e, hstep, hev⟩ := he
  rw [evalActions_nil, Option.some.injEq] at hstep
  subst hstep
  obtain ⟨t, rfl, hv⟩ := mevalList_one hev
  rw [Expr.eval_app_ctor (show Prim.ofName "C" = none from rfl)
    (show Signature.mergeOf _ "C" = MergeSpec.union from rfl),
    Option.map_eq_some_iff] at hv
  obtain ⟨ts, hts, rfl⟩ := hv
  obtain ⟨u, v, rfl, hva, hvb⟩ := mevalList_two hts
  have h1 : Env.lookup "old" (mergeEnv a b) = some _ := meval_var hva
  have h2 : Env.lookup "new" (mergeEnv a b) = some _ := meval_var hvb
  rcases mergeEnv_cases a b with ⟨x, y, rfl, rfl⟩ | hnone | ⟨ha2, hb2⟩
  · rw [show mergeEnv [x] [y] = [("old", x), ("new", y)] from rfl] at h1 h2
    rw [show Env.lookup "old" [("old", x), ("new", y)] = some x from rfl] at h1
    rw [show Env.lookup "new" [("old", x), ("new", y)] = some y from rfl] at h2
    obtain rfl : x = _ := Option.some.inj h1
    obtain rfl : y = _ := Option.some.inj h2
    exact ⟨Or.inr (Or.inl ⟨_, _, rfl, Or.inl rfl⟩),
      Or.inr (Or.inl ⟨_, _, rfl, Or.inr rfl⟩)⟩
  · rw [hnone] at h1; simp at h1
  · exact ⟨Or.inr (Or.inr ⟨⟨_, _, rfl⟩, by omega⟩),
      Or.inr (Or.inr ⟨⟨_, _, rfl⟩, by omega⟩)⟩


/-- `hjoin` is not vacuous here either, and the merge is **total**: `(C old new)`
computes a value at every pair of single columns. -/
theorem dC_join_nonvacuous (x y : Term) :
    ∃ e, evalActions { dC.toDatabase with env := mergeEnv [x] [y] } [] = some e ∧
      Expr.evalList e.sig [.app "C" [.var "old", .var "new"]] e.env
        = some [.app "C" [x, y]] :=
  ⟨_, rfl, rfl⟩

/-- Every state the specification reaches on `pC` still records the first value. -/
theorem pC_reaches_rowA {db : Database}
    (h : ProgramStep FDatabase.empty.toDatabase pC db) :
    Row.mk "f" [] [tA] ∈ db.rows := by
  cases h with
  | cons _ r1 =>
    cases r1 with
    | cons h2 r2 =>
      cases h2 with
      | action hact hcl =>
        simp only [evalAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hact
        obtain ⟨as, hargs, vs, hout, rfl⟩ := hact
        rw [show eA = Expr.app "a" [] from rfl] at hout
        rw [mevalList_nil hargs,
          mevalList_single_nullary (show Prim.ofName "a" = none from rfl) hout] at hcl
        exact (ProgramStep.contained r2).rows
          ((MergeClosure.contained hcl).rows (Set.mem_insert _ _))

/-- **Refutation C.**  `leC` is reflexive and antisymmetric, the merge is total and
`hjoin` holds, and the conclusion still fails: the survivor of the two-collision chain is
above the intermediate value, which is above `[(a)]`, but `leC` does not compose. -/
theorem currentOfLattice_false_total : ¬ CurrentOfLattice := by
  intro H
  obtain ⟨db, hstep, hcur⟩ :=
    H pC dC leC execM_pC leC_anti dC_join "f" [] vsC _ _ dC_mergeOf dC_row
  exact not_leC_of_okA dC_okA (hcur.2 [tA] ⟨[], .nil, pC_reaches_rowA hstep⟩)


/-! ## The three programs satisfy the side conditions the refinement chain imposes

`execM_current_of_lattice` carries **no** legality hypothesis, but adding the ones
`execM_contained` needs would not rescue it: all three programs satisfy
`FDatabase.ProgramLegal` from `FDatabase.empty`, and `Impl/Check.lean`'s `ReadsAreAtoms`,
so no merge body or result column reads a table. -/

theorem mergeOf_update_self {dc : FnDecl} {f : FnName} {body₀ : List Action}
    {res₀ : List Expr} (hdc : dc.merge = MergeSpec.merge body₀ res₀) :
    Signature.mergeOf (Function.update (fun _ => none) f (some dc)) f =
      MergeSpec.merge body₀ res₀ := by
  rw [Signature.mergeOf, Function.update_apply, if_pos rfl]
  exact hdc

theorem mergesLegal_update {dc : FnDecl} {f : FnName} {res₀ : List Expr}
    (hdc : dc.merge = MergeSpec.merge [] res₀) :
    Signature.MergesLegal (Function.update (fun _ => none) f (some dc)) := by
  intro g body res hg
  rw [(mergeOf_update_inv hdc hg).1]
  trivial

theorem legal_decl_cons {dc : FnDecl} {f : FnName} {res₀ : List Expr} {rest : Program}
    {d' : FDatabase} (hdc : dc.merge = MergeSpec.merge [] res₀)
    (hstep : FDatabase.empty.execCmdM (Cmd.decl f dc) = some d')
    (htail : d'.ProgramLegal rest) :
    FDatabase.empty.ProgramLegal (Cmd.decl f dc :: rest) := by
  refine ⟨trivial, ⟨rfl, by simp [FDatabase.empty]⟩, mergesLegal_update hdc, ?_⟩
  intro d'' h''
  rw [hstep, Option.some.injEq] at h''
  exact h'' ▸ htail

theorem legal_action_cons {d d' : FDatabase} {dc : FnDecl} {f : FnName} {res₀ : List Expr}
    {e : Expr} {rest : Program} (hdc : dc.merge = MergeSpec.merge [] res₀)
    (hsig : d.sig = Function.update (fun _ => none) f (some dc))
    (hstep : d.execCmdM (Cmd.action (.set f [] [e])) = some d')
    (htail : d'.ProgramLegal rest) :
    d.ProgramLegal (Cmd.action (.set f [] [e]) :: rest) := by
  refine ⟨?_, trivial, ?_, ?_⟩
  · change Signature.mergeOf d.sig f ≠ MergeSpec.union
    rw [hsig, mergeOf_update_self hdc]
    simp
  · change Signature.MergesLegal d.sig
    rw [hsig]
    exact mergesLegal_update hdc
  · intro d'' h''
    rw [hstep, Option.some.injEq] at h''
    exact h'' ▸ htail

theorem pA_legal : FDatabase.empty.ProgramLegal pA :=
  legal_decl_cons rfl rfl (legal_action_cons rfl rfl rfl trivial)

theorem pB_legal : FDatabase.empty.ProgramLegal pB :=
  legal_decl_cons rfl rfl
    (legal_action_cons rfl rfl rfl (legal_action_cons rfl rfl rfl trivial))

theorem pC_legal : FDatabase.empty.ProgramLegal pC :=
  legal_decl_cons rfl rfl
    (legal_action_cons rfl rfl rfl
      (legal_action_cons rfl rfl rfl (legal_action_cons rfl rfl rfl trivial)))

theorem pA_reads : ReadsAreAtoms pA := rfl
theorem pB_reads : ReadsAreAtoms pB := rfl
theorem pC_reads : ReadsAreAtoms pC := rfl

/-! ## What `Current` demands, isolated

The one-line observation that drives Counterexample A. -/

theorem current_forces_refl {db : Database} {le : List Term → List Term → Prop}
    {f : FnName} {as vs : List Term} (h : db.Current le f as vs) : le vs vs :=
  h.2 vs h.1


/-! ## Diagnosis

Three hypotheses are missing, and each counterexample above isolates one.

1. **`le` must be reflexive.**  `Database.Current` demands `le vs vs`
   (`current_forces_refl`), and `hjoin` supplies it only when the merge is defined and
   idempotent on the diagonal.  Counterexample A.

2. **`le` must be transitive.**  `hjoin` bounds *one* collision; a key class that
   collides `k` times needs the bounds to compose.  Counterexample C, where `le` is
   reflexive and antisymmetric and the merge is total, yet the chain of two collisions
   already breaks.

3. **The merge must actually resolve every collision the interpreter can reach.**
   `hjoin` is an implication and says nothing when `execActions`/`Expr.evalList` return
   `none`.  When they do, `mergeOneWith` returns `none`, `settled` is reached with two
   rows at one key class, and `Current` is unsatisfiable at either of them however good
   `le` is.  Counterexample B, where `le` is a full partial order.  The trigger is
   `Prim.apply`'s partiality — `min`/`max` are `i64` primitives and the model has no sort
   discipline — but a merge body that gets stuck for any other reason does the same.

A corrected statement would therefore read: `hexec`, `hanti`, plus `hrefl : ∀ x, le x x`,
`htrans : ∀ x y z, le x y → le y z → le x z`, plus `hjoin` strengthened from an
implication to an existence — for every `a b` there *is* a `vs` the body computes, and it
is an upper bound — plus `FDatabase.empty.ProgramLegal p` for the `ProgramStep` half.
None of that is proved here.

**A fourth risk this file cannot settle.**  `MergeStep` never removes a row, so a
specification state holds every superseded output, and `MValidSubst.values` lets a rule
*read* one.  `RunRules` is a total function, so after a `(run)` every reachable `db`
records whatever those extra matches wrote — rows the interpreter, which overwrites the
superseded row, never had, and which need not be below its survivor.  That would refute
the corrected statement too, for programs with rules.  It cannot be machine-checked the
way the three above are: `patternHolds` computes `closureF` at every pattern
whose tuples are non-empty, and `closureF`'s well-founded recursion does not reduce in the
kernel, so no program with a rule has an `execM` that evaluates by `rfl`. -/

end Lattice
end Egglog
