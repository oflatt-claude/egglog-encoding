import EgglogSemantics.Spec.Step

/-!
# Scope checking

Ports the Redex `typed-expr`, `typed-query-expr`, `typed-action`, `typed-pattern`,
`typed-query`, `typed-actions`, `typed-rule` and `typed-program`.

The Redex has a single type, `no-type`, so its `TypeEnv` is a list of variables and
its judgments check nothing but scope. `Scope` is that list of variables with the
type erased; real sorts arrive with `:merge` functions, which need base-sorted
outputs (`PLAN.md`, M9).

Two things the Redex's judgments make relational are functions here:

* `typed-query-expr` always succeeds — its variable rule adds an unbound variable
  rather than rejecting it — so what it computes is just the scope extended with
  the pattern's variables. `Query.bind` is that.
* `typed-action`'s `let` rule carries the side condition
  `(not (member (TypeBinding ...) (TypeBinding ...)))`, which asks whether a *list*
  of bindings occurs as an *element* of itself. That is never true, so the negation
  always holds and the condition is vacuous; a `let` may shadow.

The payoff is `runProgram_isSome`: a well-scoped program never gets stuck.
`runRules` cannot get stuck either way — it drops firings whose actions fail — so
the corresponding statement about rules is
`evalLocalActions_isSome_of_scoped`: a well-scoped rule contributes on every
substitution its query admits.
-/

namespace Egglog
/-- The variables in scope. The Redex `TypeEnv`, with its one type erased. -/
abbrev Scope := List Var

/-- The scope describes the environment's domain exactly. Maintained across a run by
`runProgram_isSome`. -/
def Scope.Models (Γ : Scope) (σ : Env) : Prop := ∀ v, v ∈ Γ ↔ v ∈ Env.dom σ

/-- The Redex `typed-expr`: every variable of `e` is in scope. -/
def Expr.Scoped (e : Expr) (Γ : Scope) : Prop := ∀ v ∈ e.vars, v ∈ Γ

/-- `e` is a constructor application.

Query facts and `expr` actions are required to be applications, which the Redex does not
require: there a bare variable is a legal fact, matching any term, and a legal action,
adding one already present. egglog's grammar admits neither, so allowing them would leave
every later phase handling a case the real system cannot express. This is the one place
`WellScoped` is deliberately stricter than the Redex `typed-program`. -/
def Expr.IsApp : Expr → Prop
  | .app _ _ => True
  | _ => False

instance (e : Expr) : Decidable e.IsApp := by cases e <;> simp only [Expr.IsApp] <;>
  infer_instance

/-- The scope a query's patterns bind, i.e. what the Redex `typed-query` returns. -/
def Query.bind (q : Query) (Γ : Scope) : Scope := Γ ∪ Query.vars q

/-- A query fact. Only the application restriction; the Redex `typed-query` never fails,
and what it computes is `Query.bind`. -/
def Pattern.Scoped : Pattern → Prop
  | .expr e => e.IsApp
  | .eq _ _ => True
  | .values _ _ _ => True

/-- The Redex `typed-action`, minus its vacuous side condition and plus the application
restriction on a bare `expr`. -/
def Action.Scoped : Action → Scope → Prop
  | .expr e, Γ => e.IsApp ∧ e.Scoped Γ
  | .letBind _ e, Γ => e.Scoped Γ
  | .union e₁ e₂, Γ => e₁.Scoped Γ ∧ e₂.Scoped Γ
  | .set _ args out, Γ => (∀ e ∈ args, e.Scoped Γ) ∧ ∀ e ∈ out, e.Scoped Γ

/-- The scope after an action: only a `let` extends it. -/
def Action.bind : Action → Scope → Scope
  | .expr _, Γ => Γ
  | .letBind v _, Γ => v :: Γ
  | .union _ _, Γ => Γ
  | .set _ _ _, Γ => Γ

/-- The Redex `typed-actions`: each action is scoped in what the earlier ones bind. -/
def Actions.Scoped : List Action → Scope → Prop
  | [], _ => True
  | a :: as, Γ => a.Scoped Γ ∧ Actions.Scoped as (a.bind Γ)

/-- The scope after a sequence of actions. -/
def Actions.bind : List Action → Scope → Scope
  | [], Γ => Γ
  | a :: as, Γ => Actions.bind as (a.bind Γ)

/-- The Redex `typed-rule`: the actions are scoped in the query's bindings. -/
def Rule.Scoped (r : Rule) (Γ : Scope) : Prop :=
  (∀ p ∈ r.query, p.Scoped) ∧ Actions.Scoped r.actions (Query.bind r.query Γ)

/-- The Redex `typed-program`, one command at a time. -/
def Cmd.Scoped : Cmd → Scope → Prop
  | .action a, Γ => a.Scoped Γ
  | .rule r, Γ => r.Scoped Γ
  | .run, _ => True
  | .decl _ _, _ => True

/-- The scope after a command: only a top-level `let` extends it. -/
def Cmd.bind : Cmd → Scope → Scope
  | .action a, Γ => a.bind Γ
  | .rule _, Γ => Γ
  | .run, Γ => Γ
  | .decl _ _, Γ => Γ

/-- The Redex `typed-program`. -/
def Program.Scoped : Program → Scope → Prop
  | [], _ => True
  | c :: cs, Γ => c.Scoped Γ ∧ Program.Scoped cs (c.bind Γ)

/-- The scope after a program. -/
def Program.bind : Program → Scope → Scope
  | [], Γ => Γ
  | c :: cs, Γ => Program.bind cs (c.bind Γ)

/-- A program with no free variables: the Redex `(typed-program Program TypeEnv)`
starting from the empty environment. -/
def WellScoped (p : Program) : Prop := Program.Scoped p []

/-! ### `set` legality

A second static check, additive and deliberately kept apart from `Scoped`. Both are
things a real front end rejects in one pass, and folding this into `Action.Scoped` is
where it eventually belongs.

It is separate for now because of the parameter. `Scoped` relates an `Action` to a
`Scope`; this relates it to a `Signature`. Threading a signature through
`Actions.Scoped`, `Rule.Scoped`, `Cmd.Scoped` and `Program.Scoped` would put a signature
argument on every lemma in `Proofs/Scope.lean` and a new hypothesis on
`exec_toDatabase`, none of which the scope theorems have any use for. Fold the two
together once `Program.Scoped` needs the signature for its own sake — M9's sort
discipline (`PLAN.md`, M9 point 4) is that reason, since a merge function's output has a
base sort. Until then the pair to carry is `WellScoped p ∧ p.SetLegal sig`.
-/
/-- `(set (f …) …)` is legal only when `f` is not a constructor.

egglog rejects a `set` on a constructor while type-checking (`egglog/src/constraint.rs`,
"Check that we're not trying to set a constructor"), and constructors are exactly the
functions whose merge is `.union` — `Signature.mergeOf` sends an undeclared name there
too, so this covers the undeclared case as well.

It is what keeps `Database.CtorRows` an invariant. A `set` writes the row
`⟨f, as, [v]⟩` for whatever `v` its out expression denotes, and `Database.ctorRowsOf`
holds no such row unless `v` is `.app f as`. -/
def Action.SetLegal : Action → Signature → Prop
  | .expr _, _ => True
  | .letBind _ _, _ => True
  | .union _ _, _ => True
  | .set f _ _, sig => sig.mergeOf f ≠ MergeSpec.union

/-- Every action in the list is a legal `set`. Unlike `Actions.Scoped` this needs no
threading: no action changes the signature. -/
def Actions.SetLegal : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.SetLegal sig ∧ Actions.SetLegal as sig

/-- A rule is legal when its head is; a query writes nothing. -/
def Rule.SetLegal (r : Rule) (sig : Signature) : Prop := Actions.SetLegal r.actions sig

/-! A `Pattern.values` atom does **not** want the companion restriction, and extending this
family to the query would be wrong rather than merely premature. It is the model's only read
and covers every width, so at one value column it is `(= v (f a…))` — what an ordinary
constructor fact lowers to, and legal egglog — and demanding `sig.mergeOf f ≠ .union` there
would reject it. What is real about "egglog recognizes the tuple form only for a tuple
output" is already enforced, from the other side: `Pattern.arityOk` pins `|v…| = outArity f`
and `MergeSpec.arityOk` gives a `.union` function `outArity = 1`, so a *wide* read can never
name a constructor. The remaining query-side condition is `Rule.noLookup`'s: a
non-constructor is read here and nowhere else. -/

/-- The signature a command leaves behind. `Cmd.bind` for signatures instead of scopes,
and exactly what `stepCmd`'s `.decl` case does. -/
def Cmd.sigBind : Cmd → Signature → Signature
  | .decl f d, sig => Function.update sig f (some d)
  | _, sig => sig

/-- `Cmd.Scoped`'s companion for `set`. -/
def Cmd.SetLegal : Cmd → Signature → Prop
  | .action a, sig => a.SetLegal sig
  | .rule r, sig => r.SetLegal sig
  | .run, _ => True
  | .decl _ _, _ => True

/-- `Program.Scoped`'s companion for `set`: each command is checked against the
signature the earlier ones leave, as `Program.Scoped` checks against the scope they
leave. -/
def Program.SetLegal : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.SetLegal sig ∧ Program.SetLegal cs (c.sigBind sig)

/-- `c` declares only constructors.

Separate from `SetLegal` because it constrains a different thing: `SetLegal` says what a
head may write, this says what the signature may become. `Database.CtorRows` needs both
— declaring a `:merge` function makes rows *already present* a `MergeStep` collision,
whose combined row need not be a constructor row, and no `set` is involved. -/
def Cmd.CtorDecl : Cmd → Prop
  | .decl _ d => d.merge = MergeSpec.union
  | _ => True

/-- Every declaration in the program declares a constructor. -/
def Program.CtorDecls (p : Program) : Prop := ∀ c ∈ p, c.CtorDecl

/-! ### Arity

egglog fixes a function's column counts when it is declared and checks every use against
them. `FnDecl` records both counts and, until this section, nothing read them outside
`Tests/Egg.lean`'s renderer — so the model accepted programs egglog's typechecker throws
out.

egglog's check is one equation on the lowered atom: for an atom headed by `f`,
`|args| = |inputs f| + |outputs f|` (`constraint.rs`,
`get_atom_application_constraints`), reported as `TypeError::Arity`, "Arity mismatch,
expected {expected} args". What each surface form contributes to `|args|` is what makes
the one equation say different things:

* an *expression* `(f a…)` — a top-level action, a rule head, a merge body, an argument —
  and a *query fact* `(f a…)` or `(= e (f a…))` each append exactly one fresh output
  variable, so both need `|a| = arity f` and `outArity f = 1`. A two-column function is
  rejected in all of those positions; the binary answers `expected 2 args: (Dist k)`.
* `(set (f a…) v)` appends the value list — one entry for a bare `v`, `|v…|` for
  `(values v…)` — so it needs `|a| + |v…| = arity f + outArity f`.
* the row atom `Pattern.values` appends the read values and needs the same sum. It has no
  single surface form: egglog writes it `(= v (f a…))` at one value column and
  `(= (values v…) (f a…))` at more, and answers "Unbound function values" if the tuple
  form is used on a one-column function. `Tests/Egg.lean` renders whichever fits, so the
  check here is on the columns and not on the notation.

The last two are modelled by the stronger split `|a| = arity f` and `|v…| = outArity f`.
egglog's sum really does admit moving a column across the divide — with every sort `i64`,
`(= (values v) (Dist k j))` is accepted for `(function Dist (i64) (i64 i64) …)` — but only
because the sorts happen to agree. The model is untyped, so the sum alone would let it
accept a program whose meaning it then gets wrong. This is the one place the check is
stricter than egglog's.

Two declaration-side rules from the same pass:

* a `:merge` result has one expression per value column — `TupleMergeArity`, "The :merge of
  tuple-output function {name} has {actual} columns but the function has {expected} output
  columns" — and must be a `(values …)` at all for a tuple-output function
  (`TupleMergeNotValues`);
* a constructor has exactly one value column — `TupleOutputNotAllowed`, "Function {0} has a
  tuple output, which is only allowed for plain functions (not constructors, relations, or
  view tables)".

A merge body is checked against the signature *including* the function being declared, so
it may `set` its own table; a forward reference to a function declared later is instead
"Unbound function". Both checked against the release binary.

**Why here.** Arity is a typechecking error, raised per command by
`get_atom_application_constraints` before that command runs — the same pass, on the same
AST node, that raises `SetConstructorDisallowed` ten lines above it, which is what
`Action.SetLegal` already models. Two alternatives were rejected. A premise on
`Expr.MEval` would reject at *run* time what egglog rejects statically, and would put a
hypothesis on every lemma in `Proofs/Merge.lean`. A state invariant "every row has its
declared width" is the *derived* form and is what would let `Impl/Merge.lean`'s lookup
branch be proved total (`Proofs/Counterexamples.lean`'s `claim3`), but it belongs inside
`Database.WF` and needs preservation lemmas through `ActionStep` and `MergeStep`; it is
the follow-on, not this.

**`Bool`, unlike `Scoped` and `SetLegal`.** Those are `Prop`s with no computable
counterpart, so `Tests/Egg.lean` restates `SetLegal` as `illegalSets` and the two can
drift. This is defined once and `ArityOk` reads it, so the difftest's check and the
statement a proof would use are the same definition — and deciding it needs no instance
through the `List Expr` nesting.

Two things are deliberately not covered, both because there is no declaration to check
against. That every *undeclared* name is used at one arity: constructors are never declared
here — `Signature.mergeOf` sends an undeclared name to `.union` — so `Tests/Egg.lean`,
which invents the `datatype` header from uses, carries that half as
`Program.arityConflicts`. And a primitive's arity, which egglog also checks
("Arity mismatch, expected 2 args: (min old new 3)"): `Prim.ofName` lives downstream in
`Spec/Merge.lean`, and an undeclared name passes here, so this is permissive rather than
wrong.
-/

mutual

/-- Every application of a declared function inside `e` has its declared key arity and one
value column. An undeclared name is a constructor of unconstrained arity. -/
def Expr.arityOk : Expr → Signature → Bool
  | .lit _, _ => true
  | .var _, _ => true
  | .app f args, sig =>
      (match sig f with
       | none => true
       | some d => args.length == d.arity && d.outArity == 1) && Expr.arityOkList args sig

/-- `Expr.arityOk` over an argument list. -/
def Expr.arityOkList : List Expr → Signature → Bool
  | [], _ => true
  | e :: es, sig => Expr.arityOk e sig && Expr.arityOkList es sig

end

/-- A query fact. `.expr` and `.eq` hold ordinary expressions, which egglog lowers with a
single fresh output variable; the row atom names a declared function and its two column
counts directly. -/
def Pattern.arityOk : Pattern → Signature → Bool
  | .expr e, sig => e.arityOk sig
  | .eq e₁ e₂, sig => e₁.arityOk sig && e₂.arityOk sig
  | .values vs f as, sig =>
      (match sig f with
       | none => false
       | some d => as.length == d.arity && vs.length == d.outArity)
        && Expr.arityOkList vs sig && Expr.arityOkList as sig

/-- An action. A `set`'s key and value counts are checked together; a `set` on an
undeclared name needs no case here, `Action.SetLegal` already rejects it. -/
def Action.arityOk : Action → Signature → Bool
  | .expr e, sig => e.arityOk sig
  | .letBind _ e, sig => e.arityOk sig
  | .union e₁ e₂, sig => e₁.arityOk sig && e₂.arityOk sig
  | .set f args out, sig =>
      (match sig f with
       | none => true
       | some d => args.length == d.arity && out.length == d.outArity)
        && Expr.arityOkList args sig && Expr.arityOkList out sig

/-- Every action in the list. Like `Actions.SetLegal`, no threading: no action changes the
signature. -/
def Actions.arityOk (as : List Action) (sig : Signature) : Bool :=
  as.all (Action.arityOk · sig)

/-- A rule's query and head. -/
def Rule.arityOk (r : Rule) (sig : Signature) : Bool :=
  r.query.all (Pattern.arityOk · sig) && Actions.arityOk r.actions sig

/-- A declaration's own merge, against `outArity` value columns. `.union` is a constructor,
which egglog forbids a tuple output; `.noMerge` has no result to check. -/
def MergeSpec.arityOk : MergeSpec → Nat → Signature → Bool
  | .union, outArity, _ => outArity == 1
  | .noMerge, _, _ => true
  | .merge body res, outArity, sig =>
      res.length == outArity && Actions.arityOk body sig && res.all (Expr.arityOk · sig)

/-- A command. A declaration's merge body sees the signature the declaration itself
installs, so it may write the function's own table. -/
def Cmd.arityOk : Cmd → Signature → Bool
  | .action a, sig => a.arityOk sig
  | .rule r, sig => r.arityOk sig
  | .run, _ => true
  | .decl f d, sig => d.merge.arityOk d.outArity ((Cmd.decl f d).sigBind sig)

/-- `Program.SetLegal`'s shape: each command against the signature the earlier ones
leave. -/
def Program.arityOk : Program → Signature → Bool
  | [], _ => true
  | c :: cs, sig => c.arityOk sig && Program.arityOk cs (c.sigBind sig)

/-- `Program.arityOk` as a proposition, to sit beside `Program.SetLegal`. -/
def Program.ArityOk (p : Program) (sig : Signature) : Prop := p.arityOk sig = true

/-- The arity check from the empty signature, as `WellScoped` is the scope check from the
empty scope. -/
def WellArity (p : Program) : Prop := Program.ArityOk p (fun _ => none)

/-! ### Reading in an action

**All reading happens in the query; all writing happens in the actions.** An application
of a non-constructor is a *lookup* — it reads a recorded row rather than building a term —
and this section says no expression anywhere in a program contains one. The single place
a program may read is then the query atom `Pattern.values`, whose function name is not an
expression position at all.

egglog raises this as `check_no_function_lookups_in_actions`
(`egglog/src/typechecking.rs:1325`), `Value lookup of non-constructor function function in
rule is disallowed`, walking a `let`'s right-hand side, a `set`'s arguments *and* its
values, both sides of a `union`, and a bare `expr`. The action cases below are that walk. A
lookup is `FunctionSubtype::Custom` and not a global, which here is
`sig.mergeOf f ≠ .union` — `Signature.mergeOf` sends an undeclared name to `.union`, so a
constructor and a primitive both pass without a case of their own.

**Where this is stricter than egglog, and why.** egglog runs the check on a *rule head*
only, and only for a seminaive rule. Three other positions are allowed to read there:

* a **top-level action** — `(set (Copy (A)) (Dist (A)))` runs and copies the value;
* a **`:merge` body** — `(function Dist (Math) i64 :merge (max old (Zero)))` runs, reads
  `Zero`, and panics with `Lookup on Zero failed in the merge function for Dist` when the
  row is missing. The body is typechecked by `typecheck_standalone_actions` under
  `Context::Write`, which never calls the check;
* a **nested read in a query fact** — `(F (Dist k))` is legal, because egglog *flattens* a
  fact into a conjunction of atoms and so lowers it to `Dist(k, v), F(v, o)`. This model
  has no flattening pass, so a read has to be written flat: `(= v (Dist k))` and `(F v)`.

`Rule.noLookup`'s action half is therefore egglog's condition and everything else is ours.
That narrows the modelled language, and it buys the thing the whole relational layer was
paying for: with nothing able to read but a query atom, `Expr.MEval` needs no `lookup`
constructor, is deterministic, and consults the database only for its signature. Each of
the three shapes has a flat equivalent — `(rule ((= v (Dist k))) ((set (Copy k) v)))` for
the first — so what is lost is notation, except in a `:merge` body, where reading another
table cannot be written at all.

**It already caught something.** `Spec/Encode.lean`'s `encodeBuild` interns an application
by `set`ting the view and reading it straight back, `(let x (@fView c…))`, which is a
lookup in a rule head and so a shape egglog's own typechecker refuses. egglog does that job
with `set-if-empty-<View>!`, registered as a *primitive* — which is how it stays on the
right side of its own rule. `Spec/Encode.lean` records it; fixing it is M11 work.
-/

mutual

/-- No application inside `e` reads a row: every function it names is a constructor. -/
def Expr.noLookup : Expr → Signature → Bool
  | .lit _, _ => true
  | .var _, _ => true
  | .app f args, sig =>
      (match sig.mergeOf f with
       | .union => true
       | _ => false) && Expr.noLookupList args sig

/-- `Expr.noLookup` over an argument list. -/
def Expr.noLookupList : List Expr → Signature → Bool
  | [], _ => true
  | e :: es, sig => Expr.noLookup e sig && Expr.noLookupList es sig

end

/-- An action, in every expression position egglog's check walks. -/
def Action.noLookup : Action → Signature → Bool
  | .expr e, sig => e.noLookup sig
  | .letBind _ e, sig => e.noLookup sig
  | .union e₁ e₂, sig => e₁.noLookup sig && e₂.noLookup sig
  | .set _ args out, sig => Expr.noLookupList args sig && Expr.noLookupList out sig

/-- Every action in the list. No threading: no action changes the signature. -/
def Actions.noLookup (as : List Action) (sig : Signature) : Bool :=
  as.all (Action.noLookup · sig)

/-- A `:merge` body and its result columns. `.union` and `.noMerge` have no body. -/
def MergeSpec.noLookup : MergeSpec → Signature → Bool
  | .union, _ => true
  | .noMerge, _ => true
  | .merge body res, sig => Actions.noLookup body sig && res.all (Expr.noLookup · sig)

/-- A query fact. `.values` is the read, so only its *operands* are checked; `.expr` and
`.eq` are evaluated, so they must name constructors throughout. -/
def Pattern.noLookup : Pattern → Signature → Bool
  | .expr e, sig => e.noLookup sig
  | .eq e₁ e₂, sig => e₁.noLookup sig && e₂.noLookup sig
  | .values vs _ as, sig => Expr.noLookupList vs sig && Expr.noLookupList as sig

/-- A rule's query and head. The head half is exactly
`check_no_function_lookups_in_actions`; the query half is this model's, and says a read is
an atom rather than something nested inside an expression egglog would flatten. -/
def Rule.noLookup (r : Rule) (sig : Signature) : Bool :=
  r.query.all (Pattern.noLookup · sig) && Actions.noLookup r.actions sig

/-- A command. A declaration's merge body sees the signature the declaration installs, as
in `Cmd.arityOk`, so a body may `set` its own table — a write — while reading it is a
lookup like any other. -/
def Cmd.noLookup : Cmd → Signature → Bool
  | .action a, sig => a.noLookup sig
  | .rule r, sig => r.noLookup sig
  | .run, _ => true
  | .decl f d, sig => d.merge.noLookup ((Cmd.decl f d).sigBind sig)

/-- Each command against the signature the earlier ones leave, as `Program.arityOk`. -/
def Program.noLookup : Program → Signature → Bool
  | [], _ => true
  | c :: cs, sig => c.noLookup sig && Program.noLookup cs (c.sigBind sig)

/-- `Program.noLookup` as a proposition, to sit beside `Program.SetLegal`. -/
def Program.NoLookup (p : Program) (sig : Signature) : Prop := p.noLookup sig = true

/-- The read check from the empty signature: every read is a `Pattern.values` atom. The
tuple to carry is `WellScoped p ∧ p.SetLegal sig ∧ WellArity p ∧ ReadsAreAtoms p`. -/
def ReadsAreAtoms (p : Program) : Prop := Program.NoLookup p (fun _ => none)

end Egglog
