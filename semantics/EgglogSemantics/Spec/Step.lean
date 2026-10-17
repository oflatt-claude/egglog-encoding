import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# Steps

Merging and program execution. A merge step resolves one pair of conflicting rows;
a run fires its rules and then merges until no conflict remains. Saturation repeats runs
until one leaves congruence unchanged. These relations need not terminate.
-/

namespace Egglog
/-! ### Merging -/
/-- Componentwise substitution of the two output tuples for a merge's parameters. -/
def mergeEnv (oldVars newVars : List Var) (old new : List Term) : Env :=
  oldVars.zip old ++ newVars.zip new

/-- Pairs of distinct rows of one function at congruent keys. -/
@[blueprint "def:conflicts"
  (statement := /--
\[
  \conf D\triangleq\{(a,b)\mid a=f(\bar k;\bar v)\in\rows D,\
    b=f(\bar k';\bar w)\in\rows D,\ a\ne b,\ \bar k\sim_E\bar k'\}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Database.conflicts (db : Database) : Set (Entry × Entry) :=
  {p | p.1 ∈ db.entries ∧ p.2 ∈ db.entries ∧ p.1 ≠ p.2 ∧ p.1.name = p.2.name ∧
    CongList db p.1.key p.2.key}

/-- Resolve two conflicting rows. Both are removed before the body's writes and the merged
row are added, so rows the body writes survive. -/
@[blueprint "def:merging"
  (statement := /--
  \[
  \ir{Collide}{
    (a,b)\in\conf D\quad a=f(\bar k;\bar v)\quad b=f(\bar k';\bar w)\\\\
    \Sigma(f)=\kw{fun}(\_,\_,\kw{merge}(\bar x,\bar y,H,\bar e))\quad
    \sigma=[\bar x\mapsto\bar v,\bar y\mapsto\bar w]\quad r=f(\bar k;\eval{\bar e})}
    {D\to_m(D\ominus a\ominus b)+\writes H+(r,r)}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive MergeStep : Database → Database → Prop where
  | collide {db : Database} {old new : Entry} {oldVars newVars : List Var}
      {body : List Action} {res : List Expr} {W : Set (Term × Term)} {vs : List Term} :
      (old, new) ∈ db.conflicts →
      db.sig.mergeOf old.name = some (.merge oldVars newVars body res) →
      Action.writes db.sig (mergeEnv oldVars newVars old.value new.value) body = some W →
      Expr.evalList db.sig res (mergeEnv oldVars newVars old.value new.value) = some vs →
      MergeStep db
        ((((db.eraseEntry old).eraseEntry new).addEqs W).putEntry ⟨old.name, old.key, vs⟩)

/-- Zero or more merge steps, written `→ₘ*`. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-! ### Rounds and saturation -/
/-- Every rule of `R` fires on every substitution satisfying its query in the pre-state;
their writes are added together. -/
def RunRules (R : RulesetName) (db : Database) : Database :=
  db.addEqs (⋃₀ {W | ∃ r ∈ db.rules, r.ruleset = R ∧
    ∃ σ, QueryMatches db r.query σ ∧ Action.writes db.sig σ r.actions = some W})

/-- `⟨run R, D⟩ ⇓ D'`: fire the rules of `R`, then merge until no conflict remains. -/
@[blueprint "def:round"
  (statement := /--
\[
  \fire_R(D)\triangleq D+\bigcup\{\writes H\mid(R,Q\Rightarrow H)\in\mathcal R,\
    D,\sigma\models Q\}
  \qquad
  \ir{Run}{\fire_R(D)\to_m^*D'\\\conf{D'}=\emptyset}{\langle\kw{run}\ R,D\rangle\Downarrow D'}
  \]
  -/)
  (latexEnv := "paperfragment")]
def RunStep (R : RulesetName) (db db' : Database) : Prop :=
  MergeClosure (RunRules R db) db' ∧ db'.conflicts = ∅

/-- `⟨saturate R, D⟩ ⇓ D'`: run `R` until a run leaves congruence unchanged, returning
that run's result. Redundant spellings and writes absorbed by merging do not prevent
saturation. -/
@[blueprint "def:saturation"
  (statement := /--
\[
  \ir{Fixpoint}{\langle\kw{run}\ R,D\rangle\Downarrow D'\\{\sim_E}={\sim_{E'}}}
    {\langle\kw{saturate}\ R,D\rangle\Downarrow D'}
  \qquad
  \ir{Repeat}{\langle\kw{run}\ R,D\rangle\Downarrow D_1\\{\sim_E}\ne{\sim_{E_1}}\\
    \langle\kw{saturate}\ R,D_1\rangle\Downarrow D'}
    {\langle\kw{saturate}\ R,D\rangle\Downarrow D'}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive SaturateReach (R : RulesetName) : Database → Database → Prop where
  | fixpoint {db d : Database} :
      RunStep R db d → Cong db = Cong d → SaturateReach R db d
  | again {db mid d : Database} :
      RunStep R db mid → Cong db ≠ Cong mid → SaturateReach R mid d → SaturateReach R db d

/-! ### Commands and programs -/
/-- Successful command execution. A check only observes. Rules are registered as written;
variable bindings are supplied when they fire. -/
def CmdStep (db : Database) : Cmd → Database → Prop
  | .decl f dc, db' => db' = { db with sig := Function.update db.sig f (some dc) }
  | .rule r, db' => db' = { db with rules := insert r db.rules }
  | .run R, db' => RunStep R db db'
  | .saturate R, db' => SaturateReach R db db'
  | .check q, db' => QueryHolds db q ∧ db' = db

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
@[blueprint "def:behavior"
  (statement := /--
  \[
  \ir{Declare}{}
    {\langle\kw{declare}\ f:d,D\rangle\Downarrow D[\Sigma\gets\Sigma[f\mapsto d]]}\quad
  \ir{Rule}{}{\langle\kw{rule}\ \rho,D\rangle\Downarrow D[\mathcal R\gets\mathcal R\cup\{\rho\}]}\quad
  \ir{Check}{D,\sigma\models Q}{\langle\kw{check}\ Q,D\rangle\Downarrow D}\quad
  \ir{Fail}{\nexists\sigma.\ D,\sigma\models Q}{\langle\kw{check}\ Q,D\rangle\Downarrow\kw{error}}
  \]
  \[
  \ir{Done}{}{\langle\epsilon,D\rangle\Downarrow D}\quad
  \ir{Next}{\langle C,D\rangle\Downarrow D_1\\\langle P,D_1\rangle\Downarrow o}
    {\langle C;P,D\rangle\Downarrow o}\quad
  \ir{Abort}{\langle C,D\rangle\Downarrow\kw{error}}{\langle C;P,D\rangle\Downarrow\kw{error}}
  \qquad o\in\mathit{Database}\cup\{\kw{error}\}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive Eval : Database → Program → Result → Prop where
  | nil {db : Database} : Eval db [] (.ok db)
  | cons {db db' : Database} {c : Cmd} {cs : Program} {r : Result} :
      CmdEval db c (.ok db') → Eval db' cs r → Eval db (c :: cs) r
  | fail {db : Database} {c : Cmd} {cs : Program} :
      CmdEval db c .checkFailed → Eval db (c :: cs) .checkFailed

end Egglog
