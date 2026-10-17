import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# Steps

Merging and program execution. A merge step resolves one pair of conflicting entries;
normalization repeats these steps until every key has one entry. Rule saturation repeats
completed rounds until `SameMeaning` holds. These relations need not terminate.
-/

namespace Egglog
/-! ### The merge step -/
/-- Componentwise substitution of the two output tuples for a merge's parameters. -/
def mergeEnv (oldVars newVars : List Var) (old new : List Term) : Env :=
  oldVars.zip old ++ newVars.zip new

/-- Run the declared body and result, restoring the caller's temporary environment. -/
inductive MergeValues (db : Database) (decl : FnDecl) (old new : List Term) :
    Database → List Term → Prop where
  | eval {d : Database} {vs : List Term} {oldVars newVars : List Var} {body : List Action} {res : List Expr} :
      decl.merge = some (.merge oldVars newVars body res) →
      evalMerge { db with env := mergeEnv oldVars newVars old new } body res = some (d, vs) →
      MergeValues db decl old new { d with env := db.env, rules := db.rules } vs

/-- Resolve two distinct entries at congruent keys. Consume both before running the
body, so entries written by the body survive. Constructor existence and equations
are preserved when entries are replaced. Identical writes coalesce as set insertion. -/
@[blueprint "def:merging"
  (statement := /--
  \[
  \ir{Collide}{
    a=f(\bar k;\bar v)\in\rows D\quad b=f(\bar k';\bar w)\in\rows D\quad
      a\ne b\quad\bar k\sim_E\bar k'\\\\
    \Sigma(f)=\kw{fun}(k,\ell,\kw{merge}(\bar x,\bar y,H,\bar e))\quad
      \sigma=[\bar x\mapsto\bar v,\bar y\mapsto\bar w]\\\\
    E_1=(E\setminus\{(a,a)\})\cup\{(t,t)\mid t\in\operatorname{cols}(a)\}\quad
    E_2=(E_1\setminus\{(b,b)\})\cup\{(t,t)\mid t\in\operatorname{cols}(b)\}\\\\
    D[E\gets E_2],\sigma\vdash H\Downarrow D'\quad\eval{\bar e}=\bar u}
    {D\to_m D'+(f(\bar k;\bar u),f(\bar k;\bar u))}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive MergeStep : Database → Database → Prop where
  | collide {db d : Database} {old new : Entry} {decl : FnDecl} {vs : List Term} :
      old ∈ db.entries → new ∈ db.entries → old ≠ new → old.name = new.name →
      db.sig old.name = some decl → CongList db old.key new.key →
      MergeValues ((db.eraseEntry old).eraseEntry new) decl old.value new.value d vs →
      MergeStep db (d.putEntry ⟨old.name, old.key, vs⟩)

/-- Zero or more merge steps, possibly stopping before merging is complete.
In mathematical notation this is simply `→ₘ*`. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-- Merging is complete when every function/key congruence class has one entry.
A lone entry is already normal, even when its merge body is non-idempotent. -/
def MergeNormal (db : Database) : Prop :=
  ∀ a ∈ db.entries, ∀ b ∈ db.entries,
    a.name = b.name → CongList db a.key b.key → a = b

/-- Reach a merge-normal state by finitely many merge steps. -/
@[blueprint "def:normalization"
  (statement := /--
\[
  \operatorname{Normal}(D)\iff
  \forall a,b\in\rows D.\ (a.f=b.f\land a.\bar k\sim_E b.\bar k)\Rightarrow a=b
  \qquad
  \ir{Normalize}{D\to_m^*D'\\\operatorname{Normal}(D')}{D\Downarrow_m D'}
  \]
  -/)
  (latexEnv := "paperfragment")]
def MergeNormalize (db db' : Database) : Prop :=
  MergeClosure db db' ∧ MergeNormal db'

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
@[blueprint "def:round"
  (statement := /--
\[
  \fire_R(D)\triangleq
    D\left[E\gets E\cup\bigcup\left\{E_{D'}\ \middle|\ \exists Q,H,\sigma.\
      (R,Q\Rightarrow H)\in\mathcal R,\ D,\sigma\models Q,\ D,\sigma\vdash H\Downarrow D'
    \right\}\right]
  \qquad
  \ir{Round}{\fire_R(D)\Downarrow_m D'}{D\xrightarrow{R}D'}
  \]
  -/)
  (latexEnv := "paperfragment")]
def RunStep (R : RulesetName) (db db' : Database) : Prop :=
  MergeNormalize (RunRules R db) db'

/-- Saturation compares the meaning of completed rounds. Redundant constructor
spellings and writes absorbed by merging do not prevent saturation. -/
def RunSaturated (R : RulesetName) (d : Database) : Prop :=
  MergeNormal d ∧ ∃ d', RunStep R d d' ∧ d.SameMeaning d'

/-- Repeat completed rounds, stopping at the first one that preserves meaning. The
final round's writes are allowed and its normalized post-state is returned. Continuing
past an unchanged round is not an execution of `saturate`.

For the constructor source fragment, a congruence-respecting round makes this a semantic
fixed point. The general language also has `min`, so that stability is a theorem with
fragment premises, not part of this operational stopping rule. -/
@[blueprint "def:saturation"
  (statement := /--
\[
  D\simeq D'\iff\Sigma=\Sigma'\land\mathcal R=\mathcal R'\land{\sim_E}={\sim_{E'}}
  \qquad
  \ir{Stop}{D\xrightarrow{R}D'\\D\simeq D'}{D\Downarrow_R D'}\quad
  \ir{Repeat}{D\xrightarrow{R}D_1\\D\not\simeq D_1\\D_1\Downarrow_R D'}{D\Downarrow_R D'}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive SaturateReach (R : RulesetName) : Database → Database → Prop where
  | done {db d : Database} :
      RunStep R db d → db.SameMeaning d → SaturateReach R db d
  | step {db mid d : Database} :
      RunStep R db mid → ¬ db.SameMeaning mid → SaturateReach R mid d →
      SaturateReach R db d

/-- What a command reaches before its merge phase. Rules are registered as written; variable
bindings are supplied when they fire. Saturation is a fixpoint condition rather than a
function because it may not terminate. -/
def cmdReach (db : Database) : Cmd → Database → Prop
  | .rule r, d => d = { db with rules := insert r db.rules }
  | .run R, d => d = RunRules R db
  | .saturate R, d => SaturateReach R db d
  | .decl f dc, d => d = { db with sig := Function.update db.sig f (some dc) }
  | .check q, d => QueryHolds db q ∧ d = db

/-- Successful command execution. Checks only observe; every other command completes
merging. Saturation already ends merge-normal (`cmdStep_saturate_iff`). -/
def CmdStep (db : Database) (c : Cmd) (db' : Database) : Prop :=
  match c with
  | .check q => QueryHolds db q ∧ db' = db
  | _ => ∃ d, cmdReach db c d ∧ MergeNormalize d db'

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
