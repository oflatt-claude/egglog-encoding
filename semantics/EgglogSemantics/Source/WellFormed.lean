import EgglogSemantics.Source.Domain

/-! Static well-formedness for the constructor source language. These conditions are
separate from the compiler's supported fragment and from whether a check is true. -/

namespace Egglog

/-- Every application names an earlier declaration with the same arity. This inspects
syntax, not the database's term set: a declared constructor may have no instances. -/
def Cmd.ApplicationsDeclared (c : Cmd) (sig : Signature) : Prop :=
  ∀ fk ∈ c.ctors, (sig fk.1).map FnDecl.arity = some fk.2

/-- Static checks at a source command boundary. Checks bind variables only inside their
query. Declarations are fresh; every other application has an earlier declaration. -/
def Cmd.WellFormed (sig : Signature) : Cmd → Prop
  | .decl f _ => (sig f).isNone = true
  | .rule r => r.Scoped [] ∧ (Cmd.rule r).ApplicationsDeclared sig
  | .check q => (∀ p ∈ q, p.Scoped) ∧ (Cmd.check q).ApplicationsDeclared sig
  | .run _ | .saturate _ => True

/-- Check a program in declaration order. Commands never extend the variable scope. -/
def Program.WellFormedFrom : Signature → Program → Prop
  | _, [] => True
  | sig, c :: cs => c.WellFormed sig ∧ Program.WellFormedFrom (c.sigBind sig) cs

/-- The paper's static premise, used together with `Program.Fragment`. -/
def Program.WellFormed (P : Program) : Prop := P.WellFormedFrom (fun _ => none)

instance (c : Cmd) (sig : Signature) : Decidable (c.ApplicationsDeclared sig) :=
  inferInstanceAs (Decidable (∀ fk ∈ c.ctors, (sig fk.1).map FnDecl.arity = some fk.2))

instance (sig : Signature) : ∀ c : Cmd, Decidable (c.WellFormed sig)
  | .decl f _ => inferInstanceAs (Decidable ((sig f).isNone = true))
  | .rule r => inferInstanceAs (Decidable (((∀ p ∈ r.query, p.Scoped) ∧
        Actions.Scoped r.actions (Query.bind r.query [])) ∧
        (Cmd.rule r).ApplicationsDeclared sig))
  | .check q => inferInstanceAs (Decidable ((∀ p ∈ q, p.Scoped) ∧
      (Cmd.check q).ApplicationsDeclared sig))
  | .run _ | .saturate _ => .isTrue trivial

instance instDecidableWellFormedFrom : ∀ (sig : Signature) (P : Program),
    Decidable (P.WellFormedFrom sig)
  | _, [] => .isTrue trivial
  | sig, c :: cs => @instDecidableAnd _ _ (inferInstanceAs (Decidable (c.WellFormed sig)))
      (instDecidableWellFormedFrom (c.sigBind sig) cs)

instance (P : Program) : Decidable P.WellFormed :=
  inferInstanceAs (Decidable (P.WellFormedFrom (fun _ => none)))

end Egglog
