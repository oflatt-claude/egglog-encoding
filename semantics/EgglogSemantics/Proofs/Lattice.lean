import EgglogSemantics.Impl.Check
import EgglogSemantics.Proofs.Merge

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# What a completeness companion has to assume

`execM_contained` is a containment, and a do-nothing implementation satisfies it, so the
refinement chain wants a completeness companion: the interpreter keeps the `le`-greatest
recorded output at each key class rather than merely some subset. `Database.Current`
(`Proofs/Merge.lean`) is that notion for a merge that is a join, and **no theorem says the
interpreter computes it**. These historical-row contracts await the live-table port.

`CurrentOfLattice` below is that companion in its naive shape: `execM_contained`'s
premises, plus antisymmetry of `le` and "the merged value is above both operands". Three
refutations show it false. Each satisfies every hypothesis the naive statement has and
fails only its conclusion, so each shows one further hypothesis to be **necessary**:

* **A** — `le` is reflexive. `Current` demands `le vs vs`, and an implication-shaped
  `hjoin` is vacuous under `le := fun _ _ => False`.
* **B** — the merge resolves every collision the interpreter can reach. `hjoin` is silent
  when the body computes nothing, and then two entries survive at one key class.
* **C** — `le` is transitive. `hjoin` bounds one collision, and a class that collides
  twice needs the bounds to compose.

`Proofs/Merge.lean`, "Two statements removed rather than carried", records the corrected
statement these three witness. It has not been written, so this file is what stops the
naive one coming back.

The deleted `execM_current_of_lattice` was the naive statement; `CurrentOfLattice` is it
verbatim, kept here so the refutations have a subject.
-/

namespace Egglog

variable {oldVars newVars oldVars₀ newVars₀ : List Var}

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
    (h : Expr.eval sig (.app f []) σ = some t) : t = .app f [] := by
  by_cases hu : sig.IsCtor f
  · rw [Expr.eval_app_ctor hu, Expr.evalList_nil, Option.map_some, Option.some.injEq] at h
    exact h.symm
  · rw [Expr.eval_app_not_ctor hu] at h; simp at h

theorem meval_min {sig : Signature} {σ : Env} {a b : Expr} {t : Term}
    (h : Expr.eval sig (.min a b) σ = some t) :
    ∃ x y, Expr.eval sig a σ = some x ∧ Expr.eval sig b σ = some y ∧ t = Term.least x y := by
  rw [Expr.eval_min, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, h⟩ := h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨x, y, hx, hy, rfl⟩

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
    (h : Expr.evalList sig [.app f []] σ = some vs) : vs = [.app f []] := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, hrest⟩ := h
  obtain ⟨us, hus, heq⟩ := Option.map_eq_some_iff.mp hrest
  rw [← heq, mevalList_nil hus, meval_nullary ht]

/-! ## The constructors the three programs build

Declaration is required, so every constructor a program applies has to be declared before
it: `Expr.eval` has no rule for an undeclared name and `execM` would simply get stuck. The
header below is shared by all three programs, which keeps one base signature for the
lemmas that read one. -/

/-- The constructors `a`, `b`, `d` and `(C S S)`, as four declarations. -/
def ctorDecl (n : Nat) : FnDecl := { arity := n, outArity := 1, merge := none }

def ctorHeader : Program :=
  [.decl "a" (ctorDecl 0), .decl "b" (ctorDecl 0), .decl "d" (ctorDecl 0),
   .decl "C" (ctorDecl 2)]

/-- The signature `ctorHeader` leaves. -/
def baseSig : Signature :=
  Function.update (Function.update (Function.update (Function.update
    (fun _ => none) "a" (some (ctorDecl 0))) "b" (some (ctorDecl 0)))
    "d" (some (ctorDecl 0))) "C" (some (ctorDecl 2))

theorem allConstructors_update {sig : Signature} (h : sig.AllConstructors) {f : FnName}
    {dc : FnDecl} (hdc : dc.merge = none) :
    Signature.AllConstructors (Function.update sig f (some dc)) :=
  h.sigBind (c := .decl f dc) hdc

theorem baseSig_allConstructors : baseSig.AllConstructors :=
  allConstructors_update (allConstructors_update (allConstructors_update
    (allConstructors_update (fun _ => rfl) rfl) rfl) rfl) rfl

/-- The state `ctorHeader` runs to: `FDatabase.empty` with the constructors declared. -/
def dHdr : FDatabase := { FDatabase.empty with sig := baseSig }

/-! ## Only the declared merge function has a `:merge` body -/

theorem mergeOf_update_inv {sig : Signature} (hsig : sig.AllConstructors) {dc : FnDecl}
    {f g : FnName} {body₀ body : List Action}
    {res₀ res : List Expr} (hdc : dc.merge = some (MergeSpec.merge oldVars₀ newVars₀ body₀ res₀))
    (h : Signature.mergeOf (Function.update sig f (some dc)) g =
      some (MergeSpec.merge oldVars newVars body res)) :
    oldVars = oldVars₀ ∧ newVars = newVars₀ ∧ body = body₀ ∧ res = res₀ := by
  by_cases hg : g = f
  · subst hg
    rw [Signature.mergeOf, Function.update_self, Option.bind_some, hdc,
      Option.some.injEq] at h
    exact MergeSpec.merge.inj h.symm
  · rw [Signature.mergeOf_update_of_ne hg, hsig g] at h; exact absurd h (by simp)

/-! ## The statement under test -/

/-- The naive completeness companion, with every binder explicit so that it can be
negated: `execM` reached `d`, `le` is antisymmetric, and `f`'s merge body sends every pair
of operands it evaluates at to an upper bound of both.  Nothing is weakened — this is the
deleted `execM_current_of_lattice`'s statement unchanged.

The conclusion is deliberately generous: not that the interpreter's own denotation is
`Current`, but that *some* specification state the program reaches is.  It is false even
so. -/
def CurrentOfLattice : Prop :=
  ∀ (p : Program) (d : FDatabase) (le : List Term → List Term → Prop),
    execM p = some d →
    (∀ x y, le x y → le y x → x = y) →
    (∀ (f : FnName) (oldVars newVars : List Var) (body : List Action) (res : List Expr)
      (a b vs : List Term),
      d.sig.mergeOf f = some (MergeSpec.merge oldVars newVars body res) →
      (∃ e, evalActions { d.toDatabase with env := mergeEnv oldVars newVars a b } body = some e ∧
        Expr.evalList e.sig res e.env = some vs) → le a vs ∧ le b vs) →
    ∀ (f : FnName) (as vs : List Term) (oldVars newVars : List Var) (body : List Action)
      (res : List Expr),
      d.sig.mergeOf f = some (MergeSpec.merge oldVars newVars body res) →
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

/-- `(function f () i64 :merge (min 1 x))`.  The result column is stuck at *every* pair
of operands: `x` is absent from the declared parameter lists `[old]` and `[new]`,
so `Expr.eval` is `none` however the collision arose. -/
def stuckDecl : FnDecl :=
  { arity := 0, outArity := 1,
    merge := some (.merge ["old"] ["new"] [] [.min (.lit (.int 1)) (.var "x")]) }

/-- `(function f () i64 :merge (min 1 x))  (set (f) (a))`. -/
def pA : Program := ctorHeader ++ [.decl "f" stuckDecl, .action (.expr (.app "f" [eA]))]

def dA : FDatabase := (execM pA).getD FDatabase.empty

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem execM_pA : execM pA = some dA := rfl

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dA_sig : dA.sig = Function.update baseSig "f" (some stuckDecl) := rfl

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dA_row : (Row.mk "f" [] [tA]) ∈ dA.rows := by decide

theorem dA_mergeOf {g : FnName} {body : List Action} {res : List Expr}
    (h : dA.sig.mergeOf g = some (MergeSpec.merge oldVars newVars body res)) :
    oldVars = ["old"] ∧ newVars = ["new"] ∧ res = [.min (.lit (.int 1)) (.var "x")] := by
  obtain ⟨ho, hn, _, hr⟩ :=
    mergeOf_update_inv baseSig_allConstructors (f := "f") rfl (dA_sig ▸ h)
  exact ⟨ho, hn, hr⟩

/-- This merge's explicit parameter lists do not bind `x`. -/
theorem lookup_x_mergeEnv (a b : List Term) :
    Env.lookup "x" (mergeEnv ["old"] ["new"] a b) = none := by
  cases a <;> cases b <;> simp [mergeEnv, Env.lookup]

/-- The stuck merge, machine-checked: no `a`, `b`, `vs` satisfy `hjoin`'s premise. -/
theorem dA_no_merge_value {a b vs : List Term} {body : List Action} {res : List Expr}
    (hparams : oldVars = ["old"] ∧ newVars = ["new"] ∧
      res = [.min (.lit (.int 1)) (.var "x")])
    (he : ∃ e, evalActions { dA.toDatabase with env := mergeEnv oldVars newVars a b } body = some e ∧
      Expr.evalList e.sig res e.env = some vs) : False := by
  obtain ⟨e, hbody, hev⟩ := he
  obtain ⟨rfl, rfl, rfl⟩ := hparams
  obtain ⟨t, rfl, hv⟩ := mevalList_one hev
  obtain ⟨_, y, -, hy, -⟩ := meval_min hv
  have henv : e.env = mergeEnv ["old"] ["new"] a b := evalActions_env hbody
  have hx : Env.lookup "x" e.env = some y := meval_var hy
  rw [henv, lookup_x_mergeEnv] at hx
  exact absurd hx (by simp)

/-- **Refutation A.** -/
theorem currentOfLattice_false : ¬ CurrentOfLattice := by
  intro H
  obtain ⟨_, -, hcur⟩ :=
    H pA dA (fun _ _ => False) execM_pA (fun _ _ h _ => h.elim)
      (fun _ _ _ _ _ _ _ _ hg he => (dA_no_merge_value (dA_mergeOf hg) he).elim)
      "f" [] [tA] _ _ _ _ rfl dA_row
  exact hcur.2 _ hcur.1

/-! ## Counterexample B — `le` is a genuine partial order and the statement still fails

`(function f () i64 :merge (min old new))` is the shape `tests/interval.egg` uses, and
`min` really is a join for the order `leB` below (reflexive, transitive, antisymmetric):
the term order reversed on single columns, which on `i64` is numerically reversed.  The
merge here runs the body `(union old new)` before that result, and the program `set`s two
*literals* into it.  `union` wants an eq-sort, and the untyped model refuses one on a
literal only dynamically — `evalAction` is stuck — so the collision is unresolvable:
`mergeOneWith` returns `none`, the pass reports `settled`, and the interpreter's final
state holds **both** rows at the one key class.  `hjoin` says nothing about that, because
it only constrains merges that *do* produce a value. -/

/-- Reading both singleton parameters requires both input tuples to be nonempty. -/
theorem mergeEnv_cases (a b : List Term) :
    (∃ x as y bs, a = x :: as ∧ b = y :: bs) ∨
      Env.lookup "old" (mergeEnv ["old"] ["new"] a b) = none ∨
      Env.lookup "new" (mergeEnv ["old"] ["new"] a b) = none := by
  match a, b with
  | [], [] => exact Or.inr (Or.inl rfl)
  | [], _ :: _ => exact Or.inr (Or.inl rfl)
  | _ :: _, [] => exact Or.inr (Or.inr rfl)
  | x :: as, y :: bs => exact Or.inl ⟨x, as, y, bs, rfl, rfl⟩

theorem mergeEnv_lookup_old (x y : Term) (as bs : List Term) :
    Env.lookup "old" (mergeEnv ["old"] ["new"] (x :: as) (y :: bs)) = some x := rfl

theorem mergeEnv_lookup_new (x y : Term) (as bs : List Term) :
    Env.lookup "new" (mergeEnv ["old"] ["new"] (x :: as) (y :: bs)) = some y := rfl

/-- `x` is a single column. -/
def Sing (x : List Term) : Prop := ∃ t, x = [t]

theorem not_sing_of_two {x : List Term} (h : 2 ≤ x.length) : ¬ Sing x := by
  rintro ⟨t, rfl⟩; simp at h

/-- The order `min` is a join for: the term order reversed on single columns — numerically
reversed on `i64` — with everything that is not a single column strictly below every one
that is. -/
def leB (x y : List Term) : Prop :=
  x = y ∨ (∃ s t : Term, x = [s] ∧ y = [t] ∧ Term.blt t s = true) ∨ (Sing y ∧ ¬ Sing x)

theorem leB_refl (x : List Term) : leB x x := Or.inl rfl

/-- Whatever is below a single column at a single column is below it at every width: a
wider first argument falls under the third clause. -/
theorem leB_cons {x t : Term} {as : List Term} (h : leB [x] [t]) : leB (x :: as) [t] := by
  cases as with
  | nil => exact h
  | cons _ _ => exact Or.inr (Or.inr ⟨⟨t, rfl⟩, not_sing_of_two (by simp)⟩)

theorem leB_trans (x y z : List Term) (h₁ : leB x y) (h₂ : leB y z) : leB x z := by
  rcases h₁ with rfl | ⟨s, t, hx, hy, hts⟩ | ⟨hy1, hx1⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨s', t', hy', hz', hts'⟩ | ⟨_, hy2⟩
    · exact Or.inr (Or.inl ⟨s, t, hx, hy, hts⟩)
    · rw [hy] at hy'
      obtain rfl : t = s' := by simpa using hy'
      exact Or.inr (Or.inl ⟨s, t', hx, hz', Term.blt_trans t' t s hts' hts⟩)
    · exact absurd ⟨t, hy⟩ hy2
  · rcases h₂ with rfl | ⟨s', t', hy', hz', _⟩ | ⟨hz2, hy2⟩
    · exact Or.inr (Or.inr ⟨hy1, hx1⟩)
    · exact Or.inr (Or.inr ⟨⟨t', hz'⟩, hx1⟩)
    · exact absurd hy1 hy2

theorem leB_anti (x y : List Term) (h₁ : leB x y) (h₂ : leB y x) : x = y := by
  rcases h₁ with rfl | ⟨s, t, hx, hy, hts⟩ | ⟨hy1, hx1⟩
  · rfl
  · rcases h₂ with h | ⟨s', t', hy', hx', hts'⟩ | ⟨hx2, hy2⟩
    · exact h.symm
    · rw [hx] at hx'; rw [hy] at hy'
      obtain rfl : s = t' := by simpa using hx'
      obtain rfl : t = s' := by simpa using hy'
      rw [Term.blt_asymm t s hts] at hts'
      exact absurd hts' (by simp)
    · exact absurd ⟨t, hy⟩ hy2
  · rcases h₂ with h | ⟨_, t', hy', hx', _⟩ | ⟨hx2, _⟩
    · exact h.symm
    · exact absurd ⟨t', hx'⟩ hx1
    · exact absurd hx2 hx1

/-- **`min` is a join for `leB`** on single columns: the smaller term is above both. -/
theorem leB_least (x y : Term) : leB [x] [Term.least x y] ∧ leB [y] [Term.least x y] := by
  by_cases hyx : Term.blt y x = true
  · have h : Term.least x y = y := by unfold Term.least; rw [if_pos hyx]
    rw [h]
    exact ⟨Or.inr (Or.inl ⟨x, y, rfl, rfl, hyx⟩), leB_refl _⟩
  · have h : Term.least x y = x := by unfold Term.least; rw [if_neg hyx]
    rw [h]
    refine ⟨leB_refl _, ?_⟩
    rcases eq_or_ne y x with rfl | hne
    · exact leB_refl _
    · rcases Term.blt_total y x hne with h' | h'
      · exact absurd h' hyx
      · exact Or.inr (Or.inl ⟨y, x, rfl, rfl, h'⟩)

/-- `(function f () i64 :merge (min old new))`, with the body `(union old new)` run before
the result. -/
def minDecl : FnDecl :=
  { arity := 0, outArity := 1,
    merge := some (.merge ["old"] ["new"] [.union (.var "old") (.var "new")]
      [.min (.var "old") (.var "new")]) }

def t1 : Term := .lit (.int 1)
def t2 : Term := .lit (.int 2)
def e1 : Expr := .lit (.int 1)
def e2 : Expr := .lit (.int 2)

/-- `(function f () i64 :merge (union old new) (min old new))  (set (f) 1)  (set (f) 2)`. -/
def pB : Program :=
  ctorHeader ++
    [.decl "f" minDecl, .action (.expr (.app "f" [e1])), .action (.expr (.app "f" [e2]))]

def dB : FDatabase := (execM pB).getD FDatabase.empty

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem execM_pB : execM pB = some dB := rfl

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dB_sig : dB.sig = Function.update baseSig "f" (some minDecl) := rfl

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
/-- **The interpreter's final state holds both rows at the one key class.** -/
theorem dB_row1 : (Row.mk "f" [] [t1]) ∈ dB.rows := by decide

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dB_row2 : (Row.mk "f" [] [t2]) ∈ dB.rows := by decide

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dB_mergeOf : dB.sig.mergeOf "f" =
    some (MergeSpec.merge ["old"] ["new"] [.union (.var "old") (.var "new")]
      [.min (.var "old") (.var "new")]) := rfl

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
/-- **`hjoin` holds**, and not vacuously: `min` is a join for `leB`. -/
theorem dB_join (g : FnName) (oldVars newVars : List Var) (body : List Action)
    (res : List Expr) (a b vs : List Term)
    (hg : dB.sig.mergeOf g = some (MergeSpec.merge oldVars newVars body res))
    (he : ∃ e, evalActions { dB.toDatabase with env := mergeEnv oldVars newVars a b } body = some e ∧
      Expr.evalList e.sig res e.env = some vs) : leB a vs ∧ leB b vs := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    mergeOf_update_inv baseSig_allConstructors (f := "f") rfl (dB_sig ▸ hg)
  obtain ⟨e, hstep, hev⟩ := he
  have henv : e.env = mergeEnv ["old"] ["new"] a b := evalActions_env hstep
  obtain ⟨t, rfl, hv⟩ := mevalList_one hev
  obtain ⟨x, y, hx, hy, rfl⟩ := meval_min hv
  have h1 : Env.lookup "old" (mergeEnv ["old"] ["new"] a b) = some x := by
    rw [← henv]; exact meval_var hx
  have h2 : Env.lookup "new" (mergeEnv ["old"] ["new"] a b) = some y := by
    rw [← henv]; exact meval_var hy
  rcases mergeEnv_cases a b with ⟨x', as, y', bs, rfl, rfl⟩ | hnone | hnone
  · rw [mergeEnv_lookup_old] at h1
    rw [mergeEnv_lookup_new] at h2
    obtain rfl : x' = x := Option.some.inj h1
    obtain rfl : y' = y := Option.some.inj h2
    exact ⟨leB_cons (leB_least _ _).1, leB_cons (leB_least _ _).2⟩
  · rw [hnone] at h1; simp at h1
  · rw [hnone] at h2; simp at h2

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
/-- `hjoin` is **not** vacuous here: on two constructor terms the body's `union` goes
through, `min` chooses `(a)`, and that value is above both for `leB`. -/
theorem dB_join_nonvacuous :
    ∃ e, evalActions { dB.toDatabase with env := mergeEnv ["old"] ["new"] [tA] [tB] }
        [.union (.var "old") (.var "new")] = some e ∧
      Expr.evalList e.sig [.min (.var "old") (.var "new")] e.env = some [tA] :=
  ⟨_, rfl, rfl⟩

/-- **Every state the specification reaches on `pB` records the first value too.**
The first `set` writes the entry term `f(1)` and nothing ever removes one. -/
theorem pB_reaches_entry1 {db : Database}
    (h : ProgramStep FDatabase.empty.toDatabase pB db) :
    Term.app "f" [t1] ∈ db.terms := by
  rw [pB, ctorHeader, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.nil_append] at h
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, h1, r1⟩ := h.cons_inv
  obtain ⟨_, hact, hcl⟩ := h1
  simp only [cmdReach, evalAction, Option.map_eq_some_iff] at hact
  obtain ⟨t, ht, rfl⟩ := hact
  obtain ⟨ts, hts, rfl⟩ := Expr.evalAtom_app_inv ht
  rw [show e1 = Expr.lit (.int 1) from rfl] at hts
  obtain ⟨u, rfl, hu⟩ := mevalList_one hts
  obtain rfl := meval_lit hu
  exact (ProgramStep.contained r1).terms
    ((MergeClosure.contained hcl).terms (Database.mem_addTerm _ _))

/-- `[2]` is not above `[1]`: the term order reversed puts `1` above `2`. -/
theorem not_leB_t1_t2 : ¬ leB [t1] [t2] := by
  rintro (h | ⟨s, t, hs, ht, hlt⟩ | ⟨-, hs⟩)
  · simp [t1, t2] at h
  · obtain rfl : s = t1 := by simpa using hs.symm
    obtain rfl : t = t2 := by simpa using ht.symm
    simp [t1, t2, Term.blt, Lit.blt] at hlt
  · exact hs ⟨t1, rfl⟩

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
/-- **Refutation B.**  `leB` is reflexive, transitive and antisymmetric, `hjoin` holds
non-vacuously, and the conclusion still fails: the interpreter keeps a row holding `2`,
the specification also records `1` there, and `leB [1] [2]` is false. -/
theorem currentOfLattice_false_partialOrder : ¬ CurrentOfLattice := by
  intro H
  obtain ⟨db, hstep, hcur⟩ :=
    H pB dB leB execM_pB leB_anti dB_join "f" [] [t2] _ _ _ _ dB_mergeOf dB_row2
  exact not_leB_t1_t2 (hcur.2 [t1] ⟨[], .nil, pB_reaches_entry1 hstep⟩)

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

/-- `leB_cons` for `leC`: a wider first argument falls under the third clause. -/
theorem leC_cons {x p q : Term} {as : List Term} (h : leC [x] [.app "C" [p, q]]) :
    leC (x :: as) [.app "C" [p, q]] := by
  cases as with
  | nil => exact h
  | cons _ _ => exact Or.inr (Or.inr ⟨⟨p, q, rfl⟩, by simp⟩)

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
    merge := some (.merge ["old"] ["new"] [] [.app "C" [.var "old", .var "new"]]) }

/-- Three `set`s at one key class, so the merge phase runs a chain of two collisions. -/
def pC : Program :=
  ctorHeader ++
    [.decl "f" cDecl, .action (.expr (.app "f" [eA])), .action (.expr (.app "f" [eB])),
     .action (.expr (.app "f" [eD]))]

def dC : FDatabase := (execM pC).getD FDatabase.empty

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem execM_pC : execM pC = some dC := rfl

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dC_sig : dC.sig = Function.update baseSig "f" (some cDecl) := rfl

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dC_mergeOf : dC.sig.mergeOf "f" =
    some (MergeSpec.merge ["old"] ["new"] [] [.app "C" [.var "old", .var "new"]]) := rfl

/-- The value the interpreter's one surviving `f`-row holds.  Read off the interpreter
rather than written out, so that the refutation does not depend on which of the two
colliding rows `mergeEnv` calls `old` or which one the pass overwrites. -/
def vsC : List Term :=
  ((dC.rows.find? fun r => r.fn == "f").getD ⟨"f", [], []⟩).out

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dC_row : (Row.mk "f" [] vsC) ∈ dC.rows := by decide

/-- `[(a)]` is neither the survivor nor one of its two `C`-children. -/
def okA (vs : List Term) : Bool :=
  decide (vs ≠ [tA]) &&
    (match vs with
     | [.app "C" [p, q]] => decide (p ≠ tA) && decide (q ≠ tA)
     | _ => true)

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
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

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
/-- **`hjoin` holds**, and the merge is total: `(C old new)` computes a value at every
pair of single columns. -/
theorem dC_join (g : FnName) (oldVars newVars : List Var) (body : List Action)
    (res : List Expr) (a b vs : List Term)
    (hg : dC.sig.mergeOf g = some (MergeSpec.merge oldVars newVars body res))
    (he : ∃ e, evalActions { dC.toDatabase with env := mergeEnv oldVars newVars a b } body = some e ∧
      Expr.evalList e.sig res e.env = some vs) : leC a vs ∧ leC b vs := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    mergeOf_update_inv baseSig_allConstructors (f := "f") rfl (dC_sig ▸ hg)
  obtain ⟨e, hstep, hev⟩ := he
  rw [evalActions_nil, Option.some.injEq] at hstep
  subst hstep
  obtain ⟨t, rfl, hv⟩ := mevalList_one hev
  rw [Expr.eval_app_ctor (show Signature.IsCtor _ "C" from ⟨ctorDecl 2, rfl, rfl⟩),
    Option.map_eq_some_iff] at hv
  obtain ⟨ts, hts, rfl⟩ := hv
  obtain ⟨u, v, rfl, hva, hvb⟩ := mevalList_two hts
  have h1 : Env.lookup "old" (mergeEnv ["old"] ["new"] a b) = some _ := meval_var hva
  have h2 : Env.lookup "new" (mergeEnv ["old"] ["new"] a b) = some _ := meval_var hvb
  rcases mergeEnv_cases a b with ⟨x, as, y, bs, rfl, rfl⟩ | hnone | hnone
  · rw [mergeEnv_lookup_old] at h1
    rw [mergeEnv_lookup_new] at h2
    obtain rfl : x = _ := Option.some.inj h1
    obtain rfl : y = _ := Option.some.inj h2
    exact ⟨leC_cons (Or.inr (Or.inl ⟨_, _, rfl, Or.inl rfl⟩)),
      leC_cons (Or.inr (Or.inl ⟨_, _, rfl, Or.inr rfl⟩))⟩
  · rw [hnone] at h1; simp at h1
  · rw [hnone] at h2; simp at h2

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
/-- `hjoin` is not vacuous here either, and the merge is **total**: `(C old new)`
computes a value at every pair of single columns. -/
theorem dC_join_nonvacuous (x y : Term) :
    ∃ e, evalActions { dC.toDatabase with env := mergeEnv ["old"] ["new"] [x] [y] } [] = some e ∧
      Expr.evalList e.sig [.app "C" [.var "old", .var "new"]] e.env
        = some [.app "C" [x, y]] :=
  ⟨_, rfl, rfl⟩

/-- Every state the specification reaches on `pC` still records the first value. -/
theorem pC_reaches_entryA {db : Database}
    (h : ProgramStep FDatabase.empty.toDatabase pC db) :
    Term.app "f" [tA] ∈ db.terms := by
  rw [pC, ctorHeader, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.nil_append] at h
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, -, h⟩ := h.cons_inv
  obtain ⟨_, h2, r2⟩ := h.cons_inv
  obtain ⟨_, hact, hcl⟩ := h2
  simp only [cmdReach, evalAction, Option.map_eq_some_iff] at hact
  obtain ⟨t, ht, rfl⟩ := hact
  obtain ⟨ts, hts, rfl⟩ := Expr.evalAtom_app_inv ht
  rw [show eA = Expr.app "a" [] from rfl] at hts
  rw [mevalList_single_nullary hts] at hcl
  exact (ProgramStep.contained r2).terms
    ((MergeClosure.contained hcl).terms (Database.mem_addTerm _ _))

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
/-- **Refutation C.**  `leC` is reflexive and antisymmetric, the merge is total and
`hjoin` holds, and the conclusion still fails: the survivor of the two-collision chain is
above the intermediate value, which is above `[(a)]`, but `leC` does not compose. -/
theorem currentOfLattice_false_total : ¬ CurrentOfLattice := by
  intro H
  obtain ⟨db, hstep, hcur⟩ :=
    H pC dC leC execM_pC leC_anti dC_join "f" [] vsC _ _ _ _ dC_mergeOf dC_row
  exact not_leC_of_okA dC_okA (hcur.2 [tA] ⟨[], .nil, pC_reaches_entryA hstep⟩)

/-! ## Neither B nor C blames the specification's over-approximation

Both refutations above reach for a specification state, because that is the shape the
naive statement has.  Neither needs one.  `Impl/Interp.lean`'s `addRow` records the entry
term beside the index row and the merge phase deletes only from the *index*, so a
superseded output is still a term of `execM`'s own final state, and `Database.Out` — which
reads `terms`, not `rows` — finds it at every congruent key.  So the conclusion already
fails at `d.toDatabase`, with no `ProgramStep` and no `MergeStep` in sight.

This is what makes the three counterexamples robust to a repair of `hjoin`: they are not
artefacts of the specification reaching states the interpreter does not. -/

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dB_out_1 : dB.toDatabase.Out "f" [] [t1] :=
  ⟨[], .nil, by
    rw [FDatabase.toDatabase_terms]
    change Term.app "f" [t1] ∈ dB.terms
    decide⟩

/-- **Refutation B, with the specification removed.** -/
theorem dB_not_current : ¬ dB.toDatabase.Current leB "f" [] [t2] :=
  fun hcur => not_leB_t1_t2 (hcur.2 [t1] dB_out_1)

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem dC_out_a : dC.toDatabase.Out "f" [] [tA] :=
  ⟨[], .nil, by
    rw [FDatabase.toDatabase_terms]
    change Term.app "f" [tA] ∈ dC.terms
    decide⟩

/-- **Refutation C, with the specification removed.** -/
theorem dC_not_current : ¬ dC.toDatabase.Current leC "f" [] vsC :=
  fun hcur => not_leC_of_okA dC_okA (hcur.2 [tA] dC_out_a)

/-! ## The three programs satisfy the side conditions the refinement chain imposes

`execM_current_of_lattice` carries **no** legality hypothesis, but adding the ones
`execM_contained` needs would not rescue it: all three programs satisfy
`FDatabase.ProgramLegal` from `FDatabase.empty`, and `Impl/Check.lean`'s `ReadsAreAtoms`,
so no merge body or result column reads a table. -/

theorem mergeOf_update_self {sig : Signature} {dc : FnDecl} {f : FnName}
    {body₀ : List Action} {res₀ : List Expr}
    (hdc : dc.merge = some (MergeSpec.merge oldVars₀ newVars₀ body₀ res₀)) :
    Signature.mergeOf (Function.update sig f (some dc)) f =
      some (MergeSpec.merge oldVars₀ newVars₀ body₀ res₀) := by
  rw [Signature.mergeOf, Function.update_self, Option.bind_some]
  exact hdc

/-- `Signature.mergeOf`, read off a declaration. -/
theorem mergeOf_of_decl {sig : Signature} {g : FnName} {dc : FnDecl} {m : MergeSpec}
    (hd : sig g = some dc) (hm : dc.merge = some m) : sig.mergeOf g = some m := by
  rw [Signature.mergeOf, hd, Option.bind_some, hm]

theorem mergesLegal_of_allConstructors {sig : Signature} (h : sig.AllConstructors) :
    Signature.MergesLegal sig := fun _ _ _ _ _ _ hd hm => (h.elim (mergeOf_of_decl hd hm)).elim

/-- Every action is a legal write: the structural predicate is automatic. -/
theorem actions_writeLegal (as : List Action) (sig : Signature) :
    Actions.WriteLegal as sig := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨trivial, ih⟩

/-- `hwidth` is `Signature.MergesLegal`'s second half: one result expression per value
column.  All three merges above have a single value column, so it is `rfl` at each use. -/
theorem mergesLegal_update {sig : Signature} (hsig : sig.AllConstructors) {dc : FnDecl}
    {f : FnName} {body₀ : List Action} {res₀ : List Expr}
    (hdc : dc.merge = some (MergeSpec.merge oldVars₀ newVars₀ body₀ res₀))
    (hwidth : res₀.length = dc.outArity) :
    Signature.MergesLegal (Function.update sig f (some dc)) := by
  intro g dc' oldVars newVars body res hd hm
  by_cases hg : g = f
  · subst hg
    rw [Function.update_self, Option.some.injEq] at hd
    subst hd
    rw [hdc, Option.some.injEq, MergeSpec.merge.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
    exact ⟨actions_writeLegal _ _, hwidth⟩
  · rw [Function.update_of_ne hg] at hd
    exact (hsig.elim (mergeOf_of_decl hd hm)).elim

/-- A constructor declaration is legal wherever the name is fresh and the state holds no
terms — which is every prefix of `ctorHeader`. -/
theorem legal_ctor_cons {d : FDatabase} {f : FnName} {n : Nat} {rest : Program}
    (hsig : d.sig.AllConstructors) (hfresh : d.sig f = none) (hterms : d.terms = [])
    (htail : ({ d with sig := Function.update d.sig f (some (ctorDecl n)) }
      : FDatabase).ProgramLegal rest) :
    d.ProgramLegal (Cmd.decl f (ctorDecl n) :: rest) := by
  refine ⟨trivial, ⟨hfresh, ?_⟩,
    mergesLegal_of_allConstructors
      (allConstructors_update hsig (dc := ctorDecl n) rfl), ?_⟩
  · intro as hm; rw [hterms] at hm; simp at hm
  · intro d'' h''
    rw [show d.execCmdM (Cmd.decl f (ctorDecl n)) = some _ from rfl,
      Option.some.injEq] at h''
    exact h'' ▸ htail

/-- The four constructor declarations, at the front of every program here. -/
theorem legal_header {rest : Program} (htail : dHdr.ProgramLegal rest) :
    FDatabase.empty.ProgramLegal (ctorHeader ++ rest) :=
  legal_ctor_cons (fun _ => rfl) rfl rfl
    (legal_ctor_cons (allConstructors_update (fun _ => rfl) rfl) rfl rfl
      (legal_ctor_cons
        (allConstructors_update (allConstructors_update (fun _ => rfl) rfl) rfl) rfl rfl
        (legal_ctor_cons (allConstructors_update (allConstructors_update
          (allConstructors_update (fun _ => rfl) rfl) rfl) rfl) rfl rfl htail)))

theorem legal_decl_cons {dc : FnDecl} {f : FnName} {body₀ : List Action} {res₀ : List Expr}
    {rest : Program} {d' : FDatabase}
    (hdc : dc.merge = some (MergeSpec.merge oldVars₀ newVars₀ body₀ res₀))
    (hwidth : res₀.length = dc.outArity)
    (hfresh : dHdr.sig f = none)
    (hstep : dHdr.execCmdM (Cmd.decl f dc) = some d')
    (htail : d'.ProgramLegal rest) :
    dHdr.ProgramLegal (Cmd.decl f dc :: rest) := by
  refine ⟨trivial, ⟨hfresh, by simp [dHdr, FDatabase.empty]⟩,
    mergesLegal_update baseSig_allConstructors hdc hwidth, ?_⟩
  intro d'' h''
  rw [hstep, Option.some.injEq] at h''
  exact h'' ▸ htail

/-- `harity` and `hout` discharge `Action.SetWidthOk`: the `set` fills exactly the
declared key and value columns.  All three programs declare `f` nullary with one value
column, which is what makes `(set (f) e)` the right shape. -/
theorem legal_action_cons {d d' : FDatabase} {dc : FnDecl} {f : FnName}
    {body₀ : List Action} {res₀ : List Expr} {e : Expr} {rest : Program}
    (hdc : dc.merge = some (MergeSpec.merge oldVars₀ newVars₀ body₀ res₀))
    (hwidth : res₀.length = dc.outArity)
    (harity : dc.arity = 0) (hout : dc.outArity = 1)
    (hsig : d.sig = Function.update baseSig f (some dc))
    (hstep : d.execCmdM (Cmd.action (.expr (.app f [e]))) = some d')
    (htail : d'.ProgramLegal rest) :
    d.ProgramLegal (Cmd.action (.expr (.app f [e])) :: rest) := by
  refine ⟨trivial, trivial, ?_, ?_⟩
  · change Signature.MergesLegal d.sig
    rw [hsig]
    exact mergesLegal_update baseSig_allConstructors hdc hwidth
  · intro d'' h''
    rw [hstep, Option.some.injEq] at h''
    exact h'' ▸ htail

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem pA_legal : FDatabase.empty.ProgramLegal pA :=
  legal_header (legal_decl_cons rfl rfl rfl rfl
    (legal_action_cons rfl rfl rfl rfl rfl rfl trivial))

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem pB_legal : FDatabase.empty.ProgramLegal pB :=
  legal_header (legal_decl_cons rfl rfl rfl rfl
    (legal_action_cons rfl rfl rfl rfl rfl rfl
      (legal_action_cons rfl rfl rfl rfl rfl rfl trivial)))

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem pC_legal : FDatabase.empty.ProgramLegal pC :=
  legal_header (legal_decl_cons rfl rfl rfl rfl
    (legal_action_cons rfl rfl rfl rfl rfl rfl
      (legal_action_cons rfl rfl rfl rfl rfl rfl
        (legal_action_cons rfl rfl rfl rfl rfl rfl trivial))))

set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem pA_reads : ReadsAreAtoms pA := rfl
set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem pB_reads : ReadsAreAtoms pB := rfl
set_option maxHeartbeats 8000000 in
-- The kernel evaluates the program here. Declaring the constructors lengthens every
-- signature lookup's `Function.update` chain, which is enough to exceed the default.
theorem pC_reads : ReadsAreAtoms pC := rfl

/-! ## What `Current` demands, isolated

The one-line observation that drives Counterexample A. -/

theorem current_forces_refl {db : Database} {le : List Term → List Term → Prop}
    {f : FnName} {as vs : List Term} (h : db.Current le f as vs) : le vs vs :=
  h.2 vs h.1

/-! ## Diagnosis

Four hypotheses are missing; the counterexamples above isolate the first three, and the
fourth is a consequence of `Database.Out` being term-based.

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
   `le` is.  Counterexample B, where `le` is a full partial order.  The trigger is a
   `union` on two literals — `union` wants an eq-sort, and the untyped model refuses one
   only when the operands are values — but a merge body that gets stuck for any other
   reason does the same.

4. **The key width must be the declared one.**  `Database.Out` is term-based:
   `f(bs ++ vs) ∈ db.terms` with `bs` congruent to `as`, so the key/value split is fixed
   by `as.length` and by nothing else — `Database.WF` has no `DeclaredTerms` clause to
   pin it.  `Database.Current le f as vs` accordingly ranges over the *suffixes* beyond
   position `as.length`, which are the declared value columns only when `as.length` is
   `f`'s arity.  `CurrentOfLattice` gets that for free from `Row.mk f as vs ∈ d.rows`,
   since `FDatabase.IndexOk` fixes a row's key width; a corrected statement phrased over
   `Database.Out` alone has to carry `as.length = dc.arity` itself, or it quantifies over
   a different set of `ws` than it reads.  Nothing here needs the hypothesis, because all
   three programs declare `f` nullary and instantiate at `as = []`.

A corrected statement would therefore read: `hexec`, `hanti`, plus `hrefl : ∀ x, le x x`,
`htrans : ∀ x y z, le x y → le y z → le x z`, plus `hjoin` strengthened from an
implication to an existence — for every `a b` there *is* a `vs` the body computes, and it
is an upper bound — plus `FDatabase.empty.ProgramLegal p` for the `ProgramStep` half and
`as.length = dc.arity` for the read.  None of that is proved here.

It is also a stronger obligation than it looks.  `Out` reads `terms`, which nothing ever
deletes from, so "greatest recorded output" ranges over the *whole write history* of the
key class and not over the entries that happen to survive.  A corrected statement is
therefore asking that the merge be a join for `le` on every value ever written at the
class, not merely on the pairs that collided.

**A risk this file cannot settle.**  Neither side ever loses a superseded output — the
specification because `MergeStep` only adds, the interpreter because `addRow` records the
entry term beside the index row — but the interpreter *matches* on the index, which its
merge phase does prune (`patternHolds`, at a `.values` pattern on a merge function, scans
`d.rows`), while `Matches.values` reads `db.terms`.  So a specification rule can read an
output no interpreter match can see.  `RunRules` is a total function, so after a `(run)`
every reachable `db` records whatever those extra matches wrote — entries the interpreter
never had, and which need not be below its survivor.  That would refute the corrected
statement too, for programs with rules.  It cannot be machine-checked the way the three
above are: `patternHolds` computes `closureF` at every pattern whose tuples are non-empty,
and `closureF`'s well-founded recursion does not reduce in the kernel, so no program with
a rule has an `execM` that evaluates by `rfl`. -/

end Lattice
end Egglog
