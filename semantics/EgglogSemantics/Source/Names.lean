import EgglogSemantics.Spec.Syntax
import EgglogSemantics.Spec.Term

/-! Names shared by the encoding passes. -/

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

/-- The `n`th generated variable. -/
def freshVar (n : Nat) : Var := "@v" ++ toString n

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
