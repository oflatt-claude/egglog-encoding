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

mutual

/-- The expression that rebuilds a ground term. -/
def toExpr : Term → Expr
  | .lit l => .lit l
  | .app f args => .app f (toExprList args)

/-- `Term.toExpr` over an argument list. -/
def toExprList : List Term → List Expr
  | [] => []
  | t :: ts => toExpr t :: toExprList ts

end

@[simp] theorem toExpr_lit (l : Lit) : (Term.lit l).toExpr = .lit l := rfl

@[simp] theorem toExpr_app (f : FnName) (ts : List Term) :
    (Term.app f ts).toExpr = .app f (Term.toExprList ts) := rfl

@[simp] theorem toExprList_nil : Term.toExprList [] = [] := rfl

@[simp] theorem toExprList_cons (t : Term) (ts : List Term) :
    Term.toExprList (t :: ts) = t.toExpr :: Term.toExprList ts := rfl

end Term
/-! ### The term order

`Expr.min` chooses by it; `Term.blt` is what it reads. -/

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

/-- The smaller of two terms in `Term.blt`, egglog's `ordering-min`: the right operand when
it is strictly below the left one, else the left. -/
def Term.least (s t : Term) : Term := if Term.blt t s then t else s

end Egglog
