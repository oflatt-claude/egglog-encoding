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
  ∃ bs, CongList db as bs ∧ Entry.mk f bs vs ∈ db.entries

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

/-- Resolve two output tuples, preserving the merge body's effects. Equal identity
columns skip the body. This relation does not invent a second input by colliding a
resident row with itself: the caller supplies an actual write or a distinct row. -/
inductive MergeValues (db : Database) (decl : FnDecl) (old new : List Term) :
    Database → List Term → Prop where
  | unchanged {oldVars newVars : List Var} {body : List Action} {res : List Expr} :
      decl.merge = some (.merge oldVars newVars body res) →
      ¬ MergeConflict decl body old new → MergeValues db decl old new db old
  | changed {d : Database} {vs : List Term} {oldVars newVars : List Var}
      {body : List Action} {res : List Expr} :
      decl.merge = some (.merge oldVars newVars body res) →
      MergeConflict decl body old new →
      evalActions { db with env := mergeEnv oldVars newVars old new } body = some d →
      Expr.evalList d.sig res d.env = some vs →
      MergeValues db decl old new { d with env := db.env, rules := db.rules } vs

/-- One insertion or destructive merge. Consumed inputs disappear before the body
runs, so writes produced by that body remain pending. Constructor existence and
asserted equalities are preserved when a function entry is replaced. -/
inductive MergeStep : Database → Database → Prop where
  | insert {db : Database} {row : Entry} {decl : FnDecl} :
      db.sig row.name = some decl → decl.merge ≠ none →
      row ∈ db.pending →
      (∀ old ∈ db.entries, old.name = row.name → ¬ CongList db old.key row.key) →
      MergeStep db ((db.consumeWrite row).putEntry row)
  | write {db d : Database} {old new : Entry} {decl : FnDecl} {vs : List Term} :
      new ∈ db.pending → old ∈ db.entries → old.name = new.name →
      db.sig old.name = some decl → CongList db old.key new.key →
      MergeValues ((db.consumeWrite new).eraseEntry old) decl old.value new.value d vs →
      MergeStep db (d.putEntry ⟨old.name, old.key, vs⟩)
  | collide {db d : Database} {old new : Entry} {decl : FnDecl} {vs : List Term} :
      old ∈ db.entries → new ∈ db.entries → old ≠ new → old.name = new.name →
      db.sig old.name = some decl → CongList db old.key new.key →
      MergeValues ((db.eraseEntry old).eraseEntry new) decl old.value new.value d vs →
      MergeStep db (d.putEntry ⟨old.name, old.key, vs⟩)

/-- Merge closure: any finite sequence of insertions and merges. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-- A completed merge phase has no pending writes and one current entry per
function/key congruence class. A lone row is not an outstanding collision. -/
structure MergeSaturated (db : Database) : Prop where
  pending : db.pending = ∅
  unique : ∀ a ∈ db.entries, ∀ b ∈ db.entries,
    a.name = b.name → CongList db a.key b.key → a = b

/-- Normalization must finish processing writes, including writes emitted by merges. -/
def MergeNormalize (db db' : Database) : Prop :=
  MergeClosure db db' ∧ MergeSaturated db'

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
  MergeNormalize (RunRules R db) db'

/-- Saturation compares the meaning of completed rounds. Redundant constructor
spellings and writes absorbed by merging do not prevent saturation. -/
def RunSaturated (R : RulesetName) (d : Database) : Prop :=
  MergeSaturated d ∧ ∃ d', RunStep R d d' ∧ d.SameMeaning d'

/-- Repeat completed rounds, stopping at the first one that preserves meaning. The
final round's writes are allowed and its normalized post-state is returned. Continuing
past an unchanged round is not an execution of `saturate`.

For the constructor source fragment, a congruence-respecting round makes this a semantic
fixed point. The general language also has `min`, so that stability is a theorem with
fragment premises, not part of this operational stopping rule. -/
inductive SaturateReach (R : RulesetName) : Database → Database → Prop where
  | done {db d : Database} :
      RunStep R db d → db.SameMeaning d → SaturateReach R db d
  | step {db mid d : Database} :
      RunStep R db mid → ¬ db.SameMeaning mid → SaturateReach R mid d →
      SaturateReach R db d

theorem SaturateReach.reach {R : RulesetName} {db d : Database}
    (h : SaturateReach R db d) : Relation.ReflTransGen (RunStep R) db d := by
  induction h with
  | done hs _ => exact .single hs
  | step hs _ _ ih => exact (Relation.ReflTransGen.single hs).trans ih

theorem SaturateReach.mergeSaturated {R : RulesetName} {db d : Database}
    (h : SaturateReach R db d) : MergeSaturated d := by
  induction h with
  | done hs _ => exact hs.2
  | step _ _ _ ih => exact ih

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
  | _ => ∃ d, cmdReach db c d ∧ MergeNormalize d db'

/-- The successful transition still decomposes into a reach and a merge closure; for a
check that closure is reflexive. The converse requires the check to leave the state alone. -/
theorem CmdStep.reach {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    ∃ d, cmdReach db c d ∧ MergeClosure d db' := by
  cases c <;> try exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩
  obtain ⟨hq, rfl⟩ := h
  exact ⟨_, ⟨hq, rfl⟩, .refl⟩

/-- A command may finish with a reflexive merge phase. For checks this is the only phase. -/
theorem CmdStep.of_reach {db db' : Database} {c : Cmd} (h : cmdReach db c db')
    (hn : MergeSaturated db') :
    CmdStep db c db' := by
  cases c <;> try exact ⟨db', h, .refl, hn⟩
  exact h

/-- State-changing commands may additionally take a merge closure. -/
theorem CmdStep.of_merge {db mid db' : Database} {c : Cmd}
    (hc : ∀ q, c ≠ .check q) (hr : cmdReach db c mid) (hm : MergeNormalize mid db') :
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
