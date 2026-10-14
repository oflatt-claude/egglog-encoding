import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# Steps

Merge closure, and what a command and a program do: `Prop`-valued, relational because merge
closure and rule firing are order- and choice-dependent; `Spec/Eval.lean` is `Option`-valued.
-/

namespace Egglog
/-! ### Reading a table -/
namespace Database
/-- `vs` are outputs `db` records for `f` at the class of the key `as`: a lookup searches
the key's congruence class rather than the term set, and a class may record several. -/
def Out (db : Database) (f : FnName) (as : List Term) (vs : List Term) : Prop :=
  ∃ bs, CongList db as bs ∧ Term.app f (bs ++ vs) ∈ db.terms

end Database
/-! ### The merge step -/
/-- Componentwise substitution of the two output tuples for a merge's parameters. -/
def mergeEnv (oldVars newVars : List Var) (old new : List Term) : Env :=
  oldVars.zip old ++ newVars.zip new

/-- How many leading value columns a collision must leave unchanged to count as no change
at all (`egglog-bridge/src/lib.rs:1418`): the declared identity columns, or — for a `:merge`
with an action block — every value column. A single-expression `:merge` has no width and so
resolves every collision, since it may be non-idempotent: `:merge (+ old new)` on two rows
both holding `2` still gives `4`. -/
def FnDecl.unchangedWidth (d : FnDecl) (body : List Action) : Option Nat :=
  d.identityVals <|> if body.isEmpty then none else some d.outArity

/-- The two colliding value tuples **conflict**: they differ in a value column that counts
(`FnDecl.unchangedWidth`), which is the whole of when a collision resolves to anything.
`Impl/Merge.lean`'s `noConflict` is this test, decided and negated. -/
def MergeConflict (decl : FnDecl) (body : List Action) (a b : List Term) : Prop :=
  match decl.unchangedWidth body with
  | some k => a.take k ≠ b.take k
  | none => True

/-- One `:merge` firing: two entries of `f` on congruent keys **whose values conflict**,
resolved by running `f`'s body once and then evaluating `res`, one expression per value
column, and recorded at the key `as` alone. The `arity` premises supply the key/value
split, without which the split `key = []` fires every entry of `f` against every other; an
entry also collides with itself, and `MergeConflict` is what keeps that collision from
resolving to anything unless the function asked for it. -/
inductive MergeStep : Database → Database → Prop where
  | collide {db d : Database} {f : FnName} {decl : FnDecl} {as bs a b vs : List Term}
      {oldVars newVars : List Var} {body : List Action} {res : List Expr} :
      db.sig f = some decl → decl.merge = some (.merge oldVars newVars body res) →
      MergeConflict decl body a b →
      as.length = decl.arity → bs.length = decl.arity →
      Term.app f (as ++ a) ∈ db.terms → Term.app f (bs ++ b) ∈ db.terms →
      CongList db as bs →
      evalActions { db with env := mergeEnv oldVars newVars a b } body = some d →
      Expr.evalList d.sig res d.env = some vs →
      MergeStep db
        { d.addTerm (.app f (as ++ vs)) with env := db.env, rules := db.rules }

/-- Merge closure: any number of merge steps. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-- No merge collision *changes* anything. Not "no step applies": a `:merge` with no block
conflicts with itself (`MergeConflict`), so at such a function a step always applies. -/
def MergeSaturated (db : Database) : Prop := ∀ db', MergeStep db db' → db' = db

/-! ### Running -/
/-- The databases one rule contributes, one per substitution satisfying its query. -/
def RuleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ, ValidQuerySubst db r.query σ ∧ evalLocalActions db r.actions σ = some d}

/-- The rule-firing half of a round of the ruleset `R`: every rule *of `R`* fires on every
substitution satisfying its query *in the pre-state*, and all the results are unioned
in. -/
def RunRules (R : RulesetName) (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ db.rules, r.ruleset = R ∧ d ∈ RuleResults db r}

/-- One round of `R`: rule firing, then a merge phase. What `Cmd.run R` does once and
`Cmd.saturate R` repeats. -/
def RunStep (R : RulesetName) (db db' : Database) : Prop :=
  MergeClosure (RunRules R db) db'

/-- `R` has saturated: no rule of `R` adds anything, and no merge step changes anything. -/
def RunSaturated (R : RulesetName) (d : Database) : Prop :=
  RunRules R d = d ∧ MergeSaturated d

/-- `Cmd.saturate R` reaches `d`: rounds of `R` until it has saturated. A fixpoint
condition rather than a function, because no expression computes the round count — it
grows with the data. -/
def SaturateReach (R : RulesetName) (db d : Database) : Prop :=
  Relation.ReflTransGen (RunStep R) db d ∧ RunSaturated R d

/-- What a command reaches before its merge phase. Rules are registered as written; variable
bindings are supplied when they fire. Saturation is a fixpoint condition rather than a
function because it may not terminate. -/
def cmdReach (db : Database) : Cmd → Database → Prop
  | .action a, d => evalAction db a = some d
  | .rule r, d => d = { db with rules := insert r db.rules }
  | .run R, d => d = RunRules R db
  | .saturate R, d => SaturateReach R db d
  | .decl f dc, d => d = { db with sig := Function.update db.sig f (some dc) }
  | .check q, d => QueryHolds db q ∧ d = db

/-- Successful execution of a command. A check only observes its input. Every other
command merges, so a
top-level `set` is its own merge phase, and `run` is one round of rule firing followed by
one. The phase is neutral after a `Cmd.saturate`, which ends merge-saturated
(`cmdStep_saturate_iff`). -/
def CmdStep (db : Database) (c : Cmd) (db' : Database) : Prop :=
  match c with
  | .check q => QueryHolds db q ∧ db' = db
  | _ => ∃ d, cmdReach db c d ∧ MergeClosure d db'

/-- The successful transition still decomposes into a reach and a merge closure; for a
check that closure is reflexive. The converse requires the check to leave the state alone. -/
theorem CmdStep.reach {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    ∃ d, cmdReach db c d ∧ MergeClosure d db' := by
  cases c <;> try exact h
  obtain ⟨hq, rfl⟩ := h
  exact ⟨_, ⟨hq, rfl⟩, .refl⟩

/-- A command may finish with a reflexive merge phase. For checks this is the only phase. -/
theorem CmdStep.of_reach {db db' : Database} {c : Cmd} (h : cmdReach db c db') :
    CmdStep db c db' := by
  cases c <;> try exact ⟨db', h, .refl⟩
  exact h

/-- State-changing commands may additionally take a merge closure. -/
theorem CmdStep.of_merge {db mid db' : Database} {c : Cmd}
    (hc : ∀ q, c ≠ .check q) (hr : cmdReach db c mid) (hm : MergeClosure mid db') :
    CmdStep db c db' := by
  cases c <;> try exact ⟨mid, hr, hm⟩
  exact (hc _ rfl).elim

/-- Run the commands in order. `ProgramStep Database.empty p` is running the program `p`. -/
inductive ProgramStep : Database → Program → Database → Prop where
  | nil {db : Database} : ProgramStep db [] db
  | cons {db d d' : Database} {c : Cmd} {cs : Program} :
      CmdStep db c d → ProgramStep d cs d' → ProgramStep db (c :: cs) d'

/-- A finite execution either finishes with a database or stops at a failed check.
Divergence and interpreter fuel exhaustion are not semantic results. -/
inductive Result where
  | ok (db : Database)
  | checkFailed

/-- The observation compared by compiler correctness, independent of the final database. -/
def Result.succeeded : Result → Bool
  | .ok _ => true
  | .checkFailed => false

/-- Command evaluation with an explicit check-failure outcome. -/
inductive CmdEval : Database → Cmd → Result → Prop where
  | ok {db db' : Database} {c : Cmd} : CmdStep db c db' → CmdEval db c (.ok db')
  | checkFailed {db : Database} {q : Query} :
      ¬ QueryHolds db q → CmdEval db (.check q) .checkFailed

/-- Finite program evaluation. Failure short-circuits the suffix, even if that suffix
would diverge. Only successful commands pass their resulting database to the next one. -/
inductive Eval : Database → Program → Result → Prop where
  | nil {db : Database} : Eval db [] (.ok db)
  | cons {db db' : Database} {c : Cmd} {cs : Program} {r : Result} :
      CmdEval db c (.ok db') → Eval db' cs r → Eval db (c :: cs) r
  | fail {db : Database} {c : Cmd} {cs : Program} :
      CmdEval db c .checkFailed → Eval db (c :: cs) .checkFailed

end Egglog
