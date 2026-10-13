import EgglogSemantics.Spec.Syntax
import EgglogSemantics.Spec.Term

/-! Names and ordering expressions shared by the encoding passes. -/

namespace Egglog

/-! ### Names -/
/-- The union-find table. The modelled language has one eq-sort, so where egglog emits
`@UF_<Sort>` per sort there is one table here. -/
def ufName : FnName := "@UF"

/-- The ruleset the maintenance rules join, and the one the emitted rebuild runs.

**One flat ruleset, one `saturate`.** egglog's rebuild schedule nests three
(`egglog/src/proofs/proof_encoding.rs:1928-1943`); this is exactly as strong, because a
fixpoint of the union of rulesets is a fixpoint of each, and `Cmd.saturate` runs to a
fixpoint. It is not the *only* ruleset the maintenance rules join: `allMaintenanceRules`
copies them into each ruleset a source `Cmd.saturate` names, which is what rebuilds between
that command's rounds. -/
def rebuildRuleset : RulesetName := "@rebuild"

/-- The view table for source constructor `f`; its key is the tuple of child ids. -/
def viewName (f : FnName) : FnName := "@" ++ f ++ "View"

/-- The legacy encoder's construction-history relation. The congruence pass does not
emit this table. -/
def termName (f : FnName) : FnName := "@" ++ f ++ "Term"

/-- The `n`th generated variable. -/
def freshVar (n : Nat) : Var := "@v" ++ toString n

/-! ### Ordering expressions -/

/-- `(ordering-gt x y)`: egglog's value ordering, `y < x`. -/
def gtE (x y : Expr) : Expr := .app "ordering-gt" [x, y]

/-- `(if c a b)`: strict three-way selection. -/
def ifE (c a b : Expr) : Expr := .app "if" [c, a, b]

/-- `(ordering-max x y)`, egglog's tie-break: `x` when `x > y`, else `y`. -/
def maxE (x y : Expr) : Expr := ifE (gtE x y) x y

/-- `(ordering-min x y)`: `y` when `x > y`, else `x`. -/
def minE (x y : Expr) : Expr := ifE (gtE x y) y x

theorem Prim.ofName_of_atPrefix {f : FnName} (h : "@".isPrefixOf f = true) :
    Prim.ofName f = none := by
  unfold Prim.ofName
  split <;> simp_all [show "@".isPrefixOf "ordering-gt" = false from by decide +kernel,
    show "@".isPrefixOf "min" = false from by decide +kernel,
    show "@".isPrefixOf "max" = false from by decide +kernel,
    show "@".isPrefixOf "if" = false from by decide +kernel]

@[simp] theorem prim_viewName (f : FnName) : Prim.ofName (viewName f) = none :=
  Prim.ofName_of_atPrefix (by
    simp [viewName, String.isPrefixOf, String.startsWith_string_iff, String.toList_append])

@[simp] theorem prim_termName (f : FnName) : Prim.ofName (termName f) = none :=
  Prim.ofName_of_atPrefix (by
    simp [termName, String.isPrefixOf, String.startsWith_string_iff, String.toList_append])

/-- View names identify their source constructors uniquely. -/
theorem viewName_inj {f g : FnName} (h : viewName f = viewName g) : f = g := by
  have h2 := congrArg String.toList h
  rw [viewName, viewName, String.toList_append, String.toList_append, String.toList_append,
    String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_left (List.append_cancel_right h2))

/-- No generated view name can be the UF table name. -/
theorem viewName_ne_ufName {f : FnName} : viewName f ≠ ufName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [viewName, ufName, String.toList_append, List.reverse_append] at h2

/-- **A generated variable is in the generated namespace.** -/
theorem atPrefix_freshVar (n : Nat) : "@".isPrefixOf (freshVar n) = true := by
  rw [freshVar, String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@v").toList = ['@', 'v'] from by decide]
  exact ⟨'v' :: (toString n).toList, rfl⟩


end Egglog
