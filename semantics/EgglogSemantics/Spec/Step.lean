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
/-- The environment a `:merge` body runs in: the two colliding entries' outputs, every
column bound, named `old<i>`/`new<i>` per value column, and nothing else. -/
def mergeEnvIdx : Nat → List Term → List Term → Env
  | _, [], _ => []
  | _, _, [] => []
  | i, o :: os, n :: ns =>
      ("old" ++ toString i, o) :: ("new" ++ toString i, n) :: mergeEnvIdx (i + 1) os ns

/-- `mergeEnvIdx`, with the unindexed names `old`/`new` for a single value column. -/
def mergeEnv : List Term → List Term → Env
  | [o], [n] => [("old", o), ("new", n)]
  | os, ns => mergeEnvIdx 0 os ns

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
      {body : List Action} {res : List Expr} :
      db.sig f = some decl → decl.merge = some (.merge body res) →
      MergeConflict decl body a b →
      as.length = decl.arity → bs.length = decl.arity →
      Term.app f (as ++ a) ∈ db.terms → Term.app f (bs ++ b) ∈ db.terms →
      CongList db as bs →
      evalActions { db with env := mergeEnv a b } body = some d →
      Expr.evalList d.sig res d.env = some vs →
      MergeStep db
        { d.addTerm (.app f (as ++ vs)) with env := db.env, rules := db.rules }

/-- Merge closure: any number of merge steps. -/
def MergeClosure : Database → Database → Prop := Relation.ReflTransGen MergeStep

/-- No merge collision *changes* anything. Not "no step applies": a `:merge` with no block
conflicts with itself (`MergeConflict`), so at such a function a step always applies. -/
def MergeSaturated (db : Database) : Prop := ∀ db', MergeStep db db' → db' = db

/-- `:no-merge` is respected: no two entries of a `.noMerge` function collide on congruent
keys with different outputs. The `arity` premises play the same role as in `MergeStep`. -/
def Database.NoMergeOk (db : Database) : Prop :=
  ∀ f decl as bs (a b : List Term), db.sig f = some decl → decl.merge = some .noMerge →
    as.length = decl.arity → bs.length = decl.arity →
    Term.app f (as ++ a) ∈ db.terms → Term.app f (bs ++ b) ∈ db.terms →
    CongList db as bs → a = b

/-! ### Resolving a rule's globals

**A rule's globals are resolved when it is declared, not when it fires.** egglog resolves
variables one command at a time (`egglog/src/lib.rs:2615-2617`), and `remove_globals` rewrites
only a reference the typechecker already marked `is_global_ref`
(`egglog/src/ast/remove_globals.rs:183-238`), so a name that is not yet a global when the rule
is read stays an ordinary match variable forever. A later top-level `let` on that name is still
legal — `check_shadowing` puts a rule's pattern names through a *clone* of the accumulated
names (`egglog/src/ast/check_shadowing.rs:60-66`), so they never reach the table the `let` is
checked against — and it does not reach back into the rule.

The head is left alone: it reads the firing state's environment under `σ`
(`evalLocalActions`), which is where a global the rule was declared under still lives. -/
mutual

/-- Read `e` through the globals `σ`: a name `σ` binds becomes the expression that rebuilds
its value, and one it does not is a match variable. -/
def Expr.resolveGlobals (σ : Env) : Expr → Expr
  | .lit l => .lit l
  | .var v => match Env.lookup v σ with
      | some t => t.toExpr
      | none => .var v
  | .app f args => .app f (Expr.resolveGlobalsList σ args)

/-- `Expr.resolveGlobals` over an argument list. -/
def Expr.resolveGlobalsList (σ : Env) : List Expr → List Expr
  | [] => []
  | e :: es => Expr.resolveGlobals σ e :: Expr.resolveGlobalsList σ es

end

@[simp] theorem Expr.resolveGlobals_lit (σ : Env) (l : Lit) :
    Expr.resolveGlobals σ (.lit l) = .lit l := rfl

theorem Expr.resolveGlobals_var (σ : Env) (v : Var) :
    Expr.resolveGlobals σ (.var v)
      = match Env.lookup v σ with | some t => t.toExpr | none => .var v := rfl

@[simp] theorem Expr.resolveGlobals_var_none {σ : Env} {v : Var}
    (h : Env.lookup v σ = none) : Expr.resolveGlobals σ (.var v) = .var v := by
  rw [Expr.resolveGlobals_var, h]

@[simp] theorem Expr.resolveGlobals_var_some {σ : Env} {v : Var} {t : Term}
    (h : Env.lookup v σ = some t) : Expr.resolveGlobals σ (.var v) = t.toExpr := by
  rw [Expr.resolveGlobals_var, h]

@[simp] theorem Expr.resolveGlobals_app (σ : Env) (f : FnName) (args : List Expr) :
    Expr.resolveGlobals σ (.app f args) = .app f (Expr.resolveGlobalsList σ args) := rfl

@[simp] theorem Expr.resolveGlobalsList_nil (σ : Env) :
    Expr.resolveGlobalsList σ [] = [] := rfl

@[simp] theorem Expr.resolveGlobalsList_cons (σ : Env) (e : Expr) (es : List Expr) :
    Expr.resolveGlobalsList σ (e :: es)
      = Expr.resolveGlobals σ e :: Expr.resolveGlobalsList σ es := rfl

/-- `Expr.resolveGlobals` over a pattern. -/
def Pattern.resolveGlobals (σ : Env) : Pattern → Pattern
  | .expr e => .expr (e.resolveGlobals σ)
  | .eq e₁ e₂ => .eq (e₁.resolveGlobals σ) (e₂.resolveGlobals σ)
  | .values vs f as =>
      .values (Expr.resolveGlobalsList σ vs) f (Expr.resolveGlobalsList σ as)

/-- `Pattern.resolveGlobals` over a query. -/
def Query.resolveGlobals (σ : Env) (q : Query) : Query := q.map (Pattern.resolveGlobals σ)

/-- **The rule the database stores**: the declared rule with its *query* read through the
globals then in scope. `Encoding/Encode.lean`'s `Rule.substGlobals` is this same step on the
encoder's syntactic globals, applied at the same command, which is what makes the two agree by
construction rather than by arrival order. -/
def Rule.resolveGlobals (σ : Env) (r : Rule) : Rule :=
  { r with query := Query.resolveGlobals σ r.query }

@[simp] theorem Rule.resolveGlobals_actions (σ : Env) (r : Rule) :
    (r.resolveGlobals σ).actions = r.actions := rfl

@[simp] theorem Rule.resolveGlobals_query (σ : Env) (r : Rule) :
    (r.resolveGlobals σ).query = Query.resolveGlobals σ r.query := rfl

@[simp] theorem Rule.resolveGlobals_ruleset (σ : Env) (r : Rule) :
    (r.resolveGlobals σ).ruleset = r.ruleset := rfl

@[simp] theorem Query.resolveGlobals_nil (q : Query) : Query.resolveGlobals [] q = q := by
  have hE : ∀ e : Expr, Expr.resolveGlobals [] e = e := by
    intro e
    induction e using Expr.rec
      (motive_2 := fun es => Expr.resolveGlobalsList [] es = es) with
    | lit l => rfl
    | var v => rfl
    | app f args ih => rw [Expr.resolveGlobals, ih]
    | nil => rfl
    | cons e es ihe ihes => rw [Expr.resolveGlobalsList, ihe, ihes]
  have hP : ∀ p : Pattern, Pattern.resolveGlobals [] p = p := by
    have hL : ∀ es : List Expr, Expr.resolveGlobalsList [] es = es := by
      intro es; induction es with
      | nil => rfl
      | cons e es ih => rw [Expr.resolveGlobalsList, hE, ih]
    intro p
    cases p with
    | expr e => rw [Pattern.resolveGlobals, hE]
    | eq e₁ e₂ => rw [Pattern.resolveGlobals, hE, hE]
    | values vs f as => rw [Pattern.resolveGlobals, hL, hL]
  rw [Query.resolveGlobals]
  induction q with
  | nil => rfl
  | cons p ps ih => rw [List.map_cons, hP, ih]

@[simp] theorem Rule.resolveGlobals_nil (r : Rule) : r.resolveGlobals [] = r := by
  rw [Rule.resolveGlobals, Query.resolveGlobals_nil]

/-- A resolved global is closed, so resolving again leaves it alone. -/
theorem Expr.resolveGlobals_toExpr (σ : Env) :
    ∀ t : Term, Expr.resolveGlobals σ t.toExpr = t.toExpr := by
  intro t
  induction t using Term.rec
    (motive_2 := fun ts => Expr.resolveGlobalsList σ (Term.toExprList ts)
      = Term.toExprList ts) with
  | lit l => rfl
  | app f ts ih => rw [Term.toExpr_app, Expr.resolveGlobals_app, ih]
  | nil => rfl
  | cons t ts iht ihts =>
      rw [Term.toExprList_cons, Expr.resolveGlobalsList_cons, iht, ihts]

/-- **Resolving twice resolves through the concatenation.** A rule registered under `σ₀` and
resolved again under `σ₁` reads as one resolution, which is why a state's rules are always
`Rule.resolveGlobals`'d source text. -/
theorem Expr.resolveGlobals_resolveGlobals (σ₀ σ₁ : Env) :
    ∀ e : Expr,
      (e.resolveGlobals σ₀).resolveGlobals σ₁ = e.resolveGlobals (σ₀ ++ σ₁) := by
  intro e
  induction e using Expr.rec
    (motive_2 := fun es => Expr.resolveGlobalsList σ₁ (Expr.resolveGlobalsList σ₀ es)
      = Expr.resolveGlobalsList (σ₀ ++ σ₁) es) with
  | lit l => rfl
  | var v =>
      cases h₀ : Env.lookup v σ₀ with
      | some t =>
          rw [Expr.resolveGlobals_var_some h₀, Expr.resolveGlobals_toExpr,
            Expr.resolveGlobals_var_some (Env.lookup_append_of_some h₀)]
      | none =>
          rw [Expr.resolveGlobals_var_none h₀]
          cases h₁ : Env.lookup v σ₁ with
          | some t =>
              rw [Expr.resolveGlobals_var_some h₁,
                Expr.resolveGlobals_var_some (σ := σ₀ ++ σ₁)
                  (by rw [Env.lookup_append_of_none h₀]; exact h₁)]
          | none =>
              rw [Expr.resolveGlobals_var_none h₁,
                Expr.resolveGlobals_var_none (σ := σ₀ ++ σ₁)
                  (by rw [Env.lookup_append_of_none h₀]; exact h₁)]
  | app f args ih =>
      rw [Expr.resolveGlobals_app, Expr.resolveGlobals_app, ih, Expr.resolveGlobals_app]
  | nil => rfl
  | cons e es ihe ihes =>
      rw [Expr.resolveGlobalsList_cons, Expr.resolveGlobalsList_cons, ihe, ihes,
        Expr.resolveGlobalsList_cons]

@[inherit_doc Expr.resolveGlobals_resolveGlobals]
theorem Expr.resolveGlobalsList_resolveGlobalsList (σ₀ σ₁ : Env) :
    ∀ es : List Expr, Expr.resolveGlobalsList σ₁ (Expr.resolveGlobalsList σ₀ es)
      = Expr.resolveGlobalsList (σ₀ ++ σ₁) es := by
  intro es
  induction es with
  | nil => rfl
  | cons e es ih =>
      rw [Expr.resolveGlobalsList_cons, Expr.resolveGlobalsList_cons,
        Expr.resolveGlobals_resolveGlobals, ih, Expr.resolveGlobalsList_cons]

@[inherit_doc Expr.resolveGlobals_resolveGlobals]
theorem Pattern.resolveGlobals_resolveGlobals (σ₀ σ₁ : Env) (p : Pattern) :
    Pattern.resolveGlobals σ₁ (Pattern.resolveGlobals σ₀ p)
      = Pattern.resolveGlobals (σ₀ ++ σ₁) p := by
  cases p with
  | expr e => rw [Pattern.resolveGlobals, Pattern.resolveGlobals, Pattern.resolveGlobals,
      Expr.resolveGlobals_resolveGlobals]
  | eq e₁ e₂ => rw [Pattern.resolveGlobals, Pattern.resolveGlobals, Pattern.resolveGlobals,
      Expr.resolveGlobals_resolveGlobals, Expr.resolveGlobals_resolveGlobals]
  | values vs f as => rw [Pattern.resolveGlobals, Pattern.resolveGlobals,
      Pattern.resolveGlobals, Expr.resolveGlobalsList_resolveGlobalsList,
      Expr.resolveGlobalsList_resolveGlobalsList]

@[inherit_doc Expr.resolveGlobals_resolveGlobals]
theorem Query.resolveGlobals_resolveGlobals (σ₀ σ₁ : Env) (q : Query) :
    Query.resolveGlobals σ₁ (Query.resolveGlobals σ₀ q)
      = Query.resolveGlobals (σ₀ ++ σ₁) q := by
  rw [Query.resolveGlobals, Query.resolveGlobals, Query.resolveGlobals, List.map_map]
  exact List.map_congr_left fun p _ => Pattern.resolveGlobals_resolveGlobals σ₀ σ₁ p

@[inherit_doc Expr.resolveGlobals_resolveGlobals]
theorem Rule.resolveGlobals_resolveGlobals (σ₀ σ₁ : Env) (r : Rule) :
    (r.resolveGlobals σ₀).resolveGlobals σ₁ = r.resolveGlobals (σ₀ ++ σ₁) := by
  simp only [Rule.resolveGlobals, Rule.resolveGlobals_query,
    Query.resolveGlobals_resolveGlobals]

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
condition rather than a `cmdEffect`, because no expression computes the round count — it
grows with the data. -/
def SaturateReach (R : RulesetName) (db d : Database) : Prop :=
  Relation.ReflTransGen (RunStep R) db d ∧ RunSaturated R d

/-- What a command computes before its merge phase. `Option`-valued, so `Spec/Eval.lean`'s
kind of definition; it sits here because `.run` names `RunRules`. `Cmd.saturate` has no
such effect — `cmdReach` is what it steps by.

A top-level action is `evalTopAction`, not `evalAction`: a `let` **declares a global** here,
so it may not rebind a name the environment already holds.

A rule is stored `Rule.resolveGlobals`'d: the globals standing when it is declared are read
into its query then and there, and every variable the stored query still carries is a match
variable. -/
def cmdEffect (db : Database) : Cmd → Option Database
  | .action a => evalTopAction db a
  | .rule r => some { db with rules := insert (r.resolveGlobals db.env) db.rules }
  | .run R => some (RunRules R db)
  | .saturate _ => none
  | .decl f d => some { db with sig := Function.update db.sig f (some d) }

/-- **A rule declared where nothing is bound is stored as written.** The `resolveGlobals` a
registration performs is the identity at the empty environment, and saying so once keeps the
kernel from reducing a state's environment at every variable of every rule a witness
program declares. -/
theorem cmdEffect_rule_of_env_nil {db : Database} (h : db.env = []) (r : Rule) :
    cmdEffect db (.rule r) = some { db with rules := insert r db.rules } := by
  rw [cmdEffect, h, Rule.resolveGlobals_nil]

/-- What a command reaches before its merge phase. Every command but `Cmd.saturate` is a
`cmdEffect`; that one is a fixpoint condition. -/
def cmdReach (db : Database) : Cmd → Database → Prop
  | .saturate R => SaturateReach R db
  | c => fun d => cmdEffect db c = some d

/-- Run one command: what it reaches, then a merge phase. Every command merges, so a
top-level `set` is its own merge phase, and `run` is one round of rule firing followed by
one. The phase is neutral after a `Cmd.saturate`, which ends merge-saturated
(`cmdStep_saturate_iff`). -/
def CmdStep (db : Database) (c : Cmd) (db' : Database) : Prop :=
  ∃ d, cmdReach db c d ∧ MergeClosure d db'

/-- Run the commands in order. `ProgramStep Database.empty p` is running the program `p`. -/
inductive ProgramStep : Database → Program → Database → Prop where
  | nil {db : Database} : ProgramStep db [] db
  | cons {db d d' : Database} {c : Cmd} {cs : Program} :
      CmdStep db c d → ProgramStep d cs d' → ProgramStep db (c :: cs) d'

end Egglog
