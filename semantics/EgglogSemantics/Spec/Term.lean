import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Syntax

/-!
# Ground terms

What an expression evaluates to, and what the database holds:

```
Term = number | (constructor Term ...)
```

A term is its own identity: there are no e-class ids, and the e-graph is a set of terms
plus a congruence relation over them.
-/

namespace Egglog
/-- A ground term. -/
inductive Term where
  | lit : Lit → Term
  | app : FnName → List Term → Term

namespace Term
mutual

/-- Decidable equality. -/
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

/-- `t` is a base value. egglog's `union` requires an eq-sort and so rejects one;
`evalAction` reads this to refuse the same. -/
def isLit : Term → Bool
  | .lit _ => true
  | .app _ _ => false

/-- `s` occurs in `t`, including `s = t`. -/
inductive IsSubterm : Term → Term → Prop where
  | refl (t : Term) : IsSubterm t t
  | arg {s a : Term} {f : FnName} {args : List Term} :
      a ∈ args → IsSubterm s a → IsSubterm s (.app f args)

/-- The subterms of `t`, as a set. -/
def subterms (t : Term) : Set Term := {s | IsSubterm s t}

mutual

/-- `subterms` as a list, in **reverse creation order**: `t`, then its arguments right to
left, each preceded by its own subterms. The order is load-bearing. -/
def subtermList : Term → List Term
  | .lit l => [.lit l]
  | .app f args => .app f args :: subtermListL args

/-- `subtermList` over an argument list, **later arguments first**: a later argument is the
newer term. -/
def subtermListL : List Term → List Term
  | [] => []
  | t :: ts => subtermListL ts ++ subtermList t

end

end Term
/-! ### The term order

`ordering-gt` is the primitive a `:merge` body compares with; `Term.blt` is what it reads. -/

/-- A total order on base values: integers by `<`, `false` below `true`, every integer below
every boolean. -/
def Lit.blt : Lit → Lit → Bool
  | .int m, .int n => decide (m < n)
  | .bool a, .bool b => !a && b
  | .int _, .bool _ => true
  | .bool _, .int _ => false

mutual

/-- A total order on terms: literals below applications, then by argument count, then by
name, then lexicographically. -/
def Term.blt : Term → Term → Bool
  | .lit l, .lit m => Lit.blt l m
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

/-! ### Primitives -/
/-- The primitives this fragment has. A primitive is applied as `Expr.app` of a reserved
name, not by a constructor of its own. egglog's `ordering-min`, `ordering-max`,
`proof-of-min` and `proof-of-max` are `if`s over `ordering-gt`, spelled out in
`Encoding/Encode.lean`. -/
inductive Prim where
  /-- egglog's value ordering as a `bool`: `(ordering-gt s t)` is `t < s`
  (`egglog/src/lib.rs:530-535`). **Strict**, so a tie is `false` and every `if` over it
  takes its `else` branch. -/
  | orderingGt
  /-- `(if c a b)`: selection on a `bool`, between two values already computed. -/
  | ifThenElse
  /-- egglog's `i64` `min`. -/
  | intMin
  /-- egglog's `i64` `max`. -/
  | intMax
  deriving DecidableEq, Repr

/-- The reserved names; a user function of the same name is shadowed. -/
def Prim.ofName : FnName → Option Prim
  | "ordering-gt" => some .orderingGt
  | "if" => some .ifThenElse
  | "min" => some .intMin
  | "max" => some .intMax
  | _ => none

/-- A primitive's meaning. `none` for the wrong arity, for an `if` on a non-`bool`, and for
`min`/`max` on a non-`i64`. -/
def Prim.apply : Prim → List Term → Option Term
  | .orderingGt, [s, t] => some (.lit (.bool (Term.blt t s)))
  | .ifThenElse, [.lit (.bool c), a, b] => some (if c then a else b)
  | .intMin, [.lit (.int m), .lit (.int n)] => some (.lit (.int (min m n)))
  | .intMax, [.lit (.int m), .lit (.int n)] => some (.lit (.int (max m n)))
  | _, _ => none

end Egglog
