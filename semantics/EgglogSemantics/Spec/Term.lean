import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Syntax

/-!
# Ground terms

What an expression evaluates to, and what the database holds:

```
Term = number | (constructor Term ...)
```

A term is its own identity — there are no e-class ids on this side of the
encoding, and the e-graph is a set of terms plus a congruence relation over them.

`Term` nests `List Term`, so the recursor Lean derives carries a second motive
over `List Term`. `Term.recTerm` repackages it as ordinary structural induction
with the hypothesis available for every argument.
-/

namespace Egglog
/-- A ground term. -/
inductive Term where
  | lit : Lit → Term
  | app : FnName → List Term → Term

namespace Term
mutual

/-- Decidable equality, written by hand because no `deriving` handler sees through the
`List Term` nesting. The relational semantics needs none of this; a `Finset`-based
executable interpreter does (`PLAN.md`, M10). -/
def decEq : (s t : Term) → Decidable (s = t)
  | .lit l₁, .lit l₂ =>
    if h : l₁ = l₂ then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .lit _, .app _ _ => .isFalse (by simp)
  | .app _ _, .lit _ => .isFalse (by simp)
  | .app f₁ as₁, .app f₂ as₂ =>
    if hf : f₁ = f₂ then
      match decEqList as₁ as₂ with
      | .isTrue ha => .isTrue (by rw [hf, ha])
      | .isFalse ha => .isFalse (by simp [ha])
    else .isFalse (by simp [hf])

/-- `decEq` over argument lists. -/
def decEqList : (as bs : List Term) → Decidable (as = bs)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | a :: as, b :: bs =>
    match decEq a b with
    | .isTrue hab =>
      match decEqList as bs with
      | .isTrue h => .isTrue (by rw [hab, h])
      | .isFalse h => .isFalse (by simp [h])
    | .isFalse hab => .isFalse (by simp [hab])

end

instance : DecidableEq Term := decEq

/-- `IsSubterm s t` holds when `s` occurs in `t`, including `s = t`. An e-graph that
holds a term holds its children, which is `Database.WF.subtermClosed` stated with
this. -/
inductive IsSubterm : Term → Term → Prop where
  | refl (t : Term) : IsSubterm t t
  | arg {s a : Term} {f : FnName} {args : List Term} :
      a ∈ args → IsSubterm s a → IsSubterm s (.app f args)

/-- The subterms of `t`, as a set. -/
def subterms (t : Term) : Set Term := {s | IsSubterm s t}

mutual

/-- `subterms` as a list, for the executable interpreter, in **reverse creation order**:
`t`, then its arguments right to left, each preceded by its own subterms.

The order is load-bearing, not cosmetic: `FDatabase.addTerm` prepends this list, so a
position in `FDatabase.terms` is the age of the term at it, which is what
`Impl/Merge.lean`'s `canonKey` reads to pick a canonical key. `MERGE.md`, "`old` is the
row at the canonical key", is why age is the right notion.

`mem_subtermList` is the bridge to the relation, and it is what every other consumer
uses, so the order is invisible to them. -/
def subtermList : Term → List Term
  | .lit l => [.lit l]
  | .app f args => .app f args :: subtermListL args

/-- `subtermList` over an argument list, **later arguments first**: an argument is
evaluated after the ones to its left, so it is the newer term. -/
def subtermListL : List Term → List Term
  | [] => []
  | t :: ts => subtermListL ts ++ subtermList t

end

end Term
/-! ### Rows

A database maps each function's key tuple to its value columns. For a constructor there
is one value column and it holds the application itself, which is what makes congruence
and the functional dependency one rule (`Cong.fd`). -/
/-- One tuple of one function's table: `fn args… ↦ out…`.

`out` is a *list*, one entry per value column. egglog's tables are multi-column and the
encoding depends on it — `@UF_<Sort>` carries a parent *and* a proof. -/
@[ext]
structure Row where
  fn : FnName
  args : List Term
  out : List Term
  deriving DecidableEq

namespace Term
/-- The constructor rows of `t`: one per application among its subterms, each mapping
its own children to itself.

Only a *constructor* application ever occurs inside a `Term` — a `:merge` function's
application evaluates to its recorded output — so this needs no signature. -/
def ctorRows (t : Term) : Set Row :=
  {r | r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ t.subterms}

/-- `ctorRows` as a list, for the executable interpreter. -/
def ctorRowList (t : Term) : List Row :=
  t.subtermList.filterMap fun s =>
    match s with
    | .app f as => some ⟨f, as, [.app f as]⟩
    | .lit _ => none

end Term
/-! ### The term order

One definition with two jobs. `ordering-min`/`ordering-max` are part of the *program*
the encoding writes — the union-find's merge body is literally
`(set (@UF_<S> (ordering-max old new)) (values (ordering-min old new) ()))` — and they
are also what makes an interpreter's choice of which collision to fire deterministic.

`Term.blt` is a *structural* order where egglog's is an allocation order, so the two pick
different class representatives. That is an accepted deviation and a hypothesis of any
future simulation theorem; `MERGE.md`, "The representative deviation", has the argument
and two repros against the binary. -/
mutual

/-- A total order on terms: literals below applications, then by argument count, then
by name, then lexicographically. Written by hand and mutually, for the same reason
`Term.decEq` is. -/
def Term.blt : Term → Term → Bool
  | .lit (.int m), .lit (.int n) => decide (m < n)
  | .lit _, .app _ _ => true
  | .app _ _, .lit _ => false
  | .app f as, .app g bs =>
      if as.length ≠ bs.length then decide (as.length < bs.length)
      else if f ≠ g then decide (f < g)
      else Term.bltList as bs

/-- `Term.blt` lexicographically over argument lists. -/
def Term.bltList : List Term → List Term → Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then Term.bltList as bs else Term.blt a b

end

/-- egglog's `ordering-min`. -/
def Term.orderingMin (s t : Term) : Term := if Term.blt s t then s else t

/-- egglog's `ordering-max`. -/
def Term.orderingMax (s t : Term) : Term := if Term.blt s t then t else s

/-! ### Primitives -/
/-- The primitives this fragment has. egglog resolves a primitive by name out of a
table that shares a namespace with user functions, which is why these are `Expr.app`
of a reserved name rather than a new `Expr` constructor — see `MERGE.md`, "Primitives
without churning `Expr`". -/
inductive Prim where
  | orderingMin
  | orderingMax
  /-- egglog's `i64` `min`. -/
  | intMin
  /-- egglog's `i64` `max`. -/
  | intMax
  deriving DecidableEq, Repr

/-- The reserved names. A user function of the same name is shadowed, as in egglog. See
`MERGE.md`, "Primitives without churning `Expr`", for why `min`/`max` are among them. -/
def Prim.ofName : FnName → Option Prim
  | "ordering-min" => some .orderingMin
  | "ordering-max" => some .orderingMax
  | "min" => some .intMin
  | "max" => some .intMax
  | _ => none

/-- A primitive's meaning. `none` for the wrong arity, and for `min`/`max` also for a
non-literal operand — they are `i64` primitives, and this model has no sort discipline to
reject the application statically. -/
def Prim.apply : Prim → List Term → Option Term
  | .orderingMin, [s, t] => some (Term.orderingMin s t)
  | .orderingMax, [s, t] => some (Term.orderingMax s t)
  | .intMin, [.lit (.int m), .lit (.int n)] => some (.lit (.int (min m n)))
  | .intMax, [.lit (.int m), .lit (.int n)] => some (.lit (.int (max m n)))
  | _, _ => none

end Egglog
