import EgglogSemantics.Spec.Step

/-!
# Sequential readings

Not part of the specification. The interpreter and many proofs run actions one at a time,
read a round as a union of rule results, and read a merge as a body execution.
`Proofs/Writes.lean` proves each reading equal to its definition in `Spec/Eval.lean` and
`Spec/Step.lean`.
-/

namespace Egglog

/-- Run one action in the database's evaluation context. -/
def evalAction (db : Database) : Action → Option Database
  | .expr e =>
      (e.evalAtom db.sig db.env).map fun t => db.addTerm t
  | .union e₁ e₂ =>
      (e₁.eval db.sig db.env).bind fun t₁ =>
        (e₂.eval db.sig db.env).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some (db.addEq t₁ t₂)

/-- Run the actions in order, threading the database through. -/
def evalActions (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction db a).bind fun db' => evalActions db' as

/-- Run a rule's actions under its query substitution, then restore the surrounding context. -/
def evalLocalActions (db : Database) (as : List Action) (σ : Env) : Option Database :=
  (evalActions { db with env := σ } as).map fun db' =>
    { db' with env := db.env, rules := db.rules }

/-- Execute the merge body, then evaluate its output tuple. -/
def evalMerge (db : Database) (body : List Action) (res : List Expr) :
    Option (Database × List Term) :=
  (evalActions db body).bind fun d => (Expr.evalList d.sig res d.env).map (d, ·)

/-- Run the declared body and result, restoring the caller's temporary environment. -/
inductive MergeValues (db : Database) (decl : FnDecl) (old new : List Term) :
    Database → List Term → Prop where
  | eval {d : Database} {vs : List Term} {oldVars newVars : List Var} {body : List Action}
      {res : List Expr} :
      decl.merge = some (.merge oldVars newVars body res) →
      evalMerge { db with env := mergeEnv oldVars newVars old new } body res = some (d, vs) →
      MergeValues db decl old new { d with env := db.env, rules := db.rules } vs

/-- Merge until no conflict remains: the merge phase of `RunStep`. -/
def MergeNormalize (db db' : Database) : Prop :=
  MergeClosure db db' ∧ db'.conflicts = ∅

/-- At most one row per function and congruent key: `Database.conflicts` is empty. -/
def MergeNormal (db : Database) : Prop :=
  ∀ a ∈ db.entries, ∀ b ∈ db.entries,
    a.name = b.name → CongList db a.key b.key → a = b

/-- The databases one rule contributes, one per substitution satisfying its query. -/
def RuleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ, ValidQuerySubst db r.query σ ∧ evalLocalActions db r.actions σ = some d}

/-- A merge-normal state whose next round preserves its meaning. -/
def RunSaturated (R : RulesetName) (d : Database) : Prop :=
  MergeNormal d ∧ ∃ d', RunStep R d d' ∧ d.SameMeaning d'

/-- What a command reaches before any merging of its own. -/
def cmdReach (db : Database) : Cmd → Database → Prop
  | .rule r, d => d = { db with rules := insert r db.rules }
  | .run R, d => d = RunRules R db
  | .saturate R, d => SaturateReach R db d
  | .decl f dc, d => d = { db with sig := Function.update db.sig f (some dc) }
  | .check q, d => QueryHolds db q ∧ d = db

end Egglog
