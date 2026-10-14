import EgglogSemantics.Impl.Check
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Spec.Scope

/-!
# Emitting egglog source

Renders a `Program` as a `.egg` file so that the same program can be run by the Rust
implementation and the results compared by `DiffTest.lean`. The oracle
is `(print-size)`, which prints one row count per function — the same quantity
`FDatabase.rowCount` computes and `egglog/tests/files.rs` snapshots.

Two mismatches to keep in mind when generating programs.

The model is untyped, so the emitter invents a single sort `Math` and declares every
constructor it sees at the arity it is used with. A program that uses one name at two
arities is not expressible in egglog and must not be generated.

`Term.lit` is the same sort as an application here, while egglog's `i64` is a distinct
primitive sort — `1` and `(Num 1)` are interchangeable for us and not for egglog. Literals
are therefore emitted as-is and generated programs should avoid them, using nullary
constructors instead; the fragment loses nothing by it.
-/

namespace Egglog

/-! ### Rendering -/

mutual

/-- Render an expression with the chosen surface spelling of its variables. -/
def Expr.toEggWith (name : Var → String) : Expr → String
  | .lit (.int n) => toString n
  | .var v => name v
  | .app f args => "(" ++ f ++ Expr.toEggArgsWith name args ++ ")"
  | .min a b => "(min " ++ a.toEggWith name ++ " " ++ b.toEggWith name ++ ")"

/-- `Expr.toEggWith` over an argument list, each preceded by a space. -/
def Expr.toEggArgsWith (name : Var → String) : List Expr → String
  | [] => ""
  | e :: es => " " ++ e.toEggWith name ++ Expr.toEggArgsWith name es

end

/-- An expression as egglog source, preserving variable names. -/
def Expr.toEgg (e : Expr) : String := e.toEggWith id

/-- One expression per value column, written as egglog's tuple form `(values e₀ e₁ …)`
when there is more than one and bare when there is exactly one. Complete atoms store
these columns after their keys; the emitter translates them to Rust egglog syntax. -/
def Expr.valuesToEggWith (name : Var → String) : List Expr → String
  | [e] => e.toEggWith name
  | res => "(values " ++ String.intercalate " " (res.map (Expr.toEggWith name)) ++ ")"

@[inherit_doc Expr.valuesToEggWith]
def Expr.valuesToEgg (es : List Expr) : String := Expr.valuesToEggWith id es

/-- A query fact. A complete table atom is emitted using Rust egglog's lookup syntax,
whose surface form depends on the output width: `(= v (f a…))` at one value column and `(= (values v…) (f a…))` at more, since
`values` is not a function name and egglog answers "Unbound function values" if the tuple
form is used on a one-column function. -/
def Pattern.toEgg (sig : Signature) : Pattern → String
  | .expr e => match e.entry sig with
    | none => e.toEgg
    | some (f, keys, vals) =>
        "(= " ++ Expr.valuesToEgg vals ++ " " ++ (Expr.app f keys).toEgg ++ ")"
  | .eq e₁ e₂ => "(= " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"

def Action.toEggWith (sig : Signature) (name : Var → String) : Action → String
  | .expr e => match e.entry sig with
    | none => e.toEggWith name
    | some (f, keys, vals) =>
        "(set " ++ (Expr.app f keys).toEggWith name ++ " " ++
          Expr.valuesToEggWith name vals ++ ")"
  | .union e₁ e₂ => "(union " ++ e₁.toEggWith name ++ " " ++ e₂.toEggWith name ++ ")"

def Action.toEgg (sig : Signature) (a : Action) : String := a.toEggWith sig id

/-- `:ruleset` is emitted only for a named ruleset: egglog's unnamed one is what a rule with
no `:ruleset` joins, so the empty name renders as nothing and the existing cases are
unchanged. -/
def Rule.toEgg (sig : Signature) (r : Rule) : String :=
  "(rule (" ++ String.intercalate " " (r.query.map (Pattern.toEgg sig)) ++ ") ("
    ++ String.intercalate " " (r.actions.map (Action.toEgg sig)) ++ ")"
    ++ (if r.ruleset = "" then "" else " :ruleset " ++ r.ruleset) ++ ")"

/-- egglog's implicit parameter spellings; these conventions stay in the syntax adapter. -/
def mergeParamsToEgg (side : String) (width : Nat) : List Var :=
  if width == 1 then [side] else (List.range width).map fun i => side ++ toString i

/-- Map explicitly bound parameters to egglog's scalar or tuple parameter spellings. -/
def mergeNameToEgg (oldVars newVars : List Var) (v : Var) : String :=
  let names := oldVars.zip (mergeParamsToEgg "old" oldVars.length) ++
    newVars.zip (mergeParamsToEgg "new" newVars.length)
  ((names.find? fun p => p.1 == v).map Prod.snd).getD v

/-- A merge specification as egglog source. The block form places actions and result
as siblings; a bodyless merge emits only its result. Renaming occurs only on output. -/
def MergeSpec.toEgg (sig : Signature) : MergeSpec → String
  | .merge oldVars newVars body res =>
    let name := mergeNameToEgg oldVars newVars
    if body.isEmpty then " :merge " ++ Expr.valuesToEggWith name res
    else " :merge (" ++ String.intercalate " " (body.map (Action.toEggWith sig name)) ++ " "
      ++ Expr.valuesToEggWith name res ++ ")"

/-- A `:merge` function's declaration.

**Sorts finally bite** (M9): egglog typechecks a `(function …)`, so a merge function
needs a real output sort. Keys are the one eq-sort `Math`; the output is `i64`, as
`tests/interval.egg` and `tests/merge-during-rebuild.egg` do. An eq-sorted output would
dodge the base sort, but then the leader choice has to render as egglog's `ordering-min`,
and `Term.blt` is *structural* where that is by insertion order, so the two would pick
different representatives. Row counts are per key
class and would survive that; nothing else would. Keeping keys eq-sorted also keeps
`Term.lit` out of constructor arguments, so this file's standing literal mismatch stays out
of the way.

A multi-column output is a parenthesized sort list, `(i64 i64)`, as
`egglog/tests/tuple-output.egg` writes it. egglog accepts `(i64)` for one column too,
but the bare form is what every existing case renders and is left alone. -/
def FnDecl.toEgg (sig : Signature) (f : FnName) (d : FnDecl) (m : MergeSpec) : String :=
  -- A generated table's outputs are ids or proofs, which the untyped model shows as `Math`.
  let sort := if "@".isPrefixOf f then "Math" else "i64"
  let out := match d.outArity with
    | 1 => sort
    | _ => "(" ++ String.intercalate " " (List.replicate d.outArity sort) ++ ")"
  "(function " ++ f ++ " (" ++ String.intercalate " " (List.replicate d.arity "Math")
    ++ ") " ++ out ++ m.toEgg sig ++ ")"

/-- A command as egglog source. A run of the *unnamed* ruleset is `(run 1)`, which is what
egglog's bare form means (`egglog/src/ast/parse.rs:834-864`); a named one carries its name.
A constructor declaration is a `constructor` command and a `:merge` declaration a
`function` command. -/
def Cmd.toEgg (sig : Signature) : Cmd → String
  | .action a => a.toEgg sig
  | .rule r => r.toEgg sig
  | .run R => if R = "" then "(run 1)" else "(run " ++ R ++ " 1)"
  | .saturate R => "(run-schedule (saturate " ++ (if R = "" then "(run)" else R) ++ "))"
  | .decl f d => match d.merge with
    | none => "(constructor " ++ f ++ " (" ++ String.intercalate " " (List.replicate d.arity "Math")
        ++ ") Math)"
    | some m => FnDecl.toEgg ((Cmd.decl f d).sigBind sig) f d m
  | .check q => "(check" ++ String.join (q.map fun p => " " ++ p.toEgg sig) ++ ")"

/-! ### Collecting the signature

Every constructor has to be declared before egglog runs the program, so the arities are
read off the program's uses rather than from `Signature`. `Program.ctorDecls` turns them
into the declarations the model evaluates against and `Cmd.toEgg` renders, so the two
descriptions of a program's constructors cannot drift.

A **declared `:merge` function** has its own `function` command, and `Program.ctorArities`
filters it. `min` is syntax rather than a name, so it never reaches the declarations; it
renders as egglog's `min`, which agrees with `Term.blt` on the `i64` value columns every
emitted merge function has.
-/

mutual

def Expr.fnArities : Expr → List (FnName × Nat)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args.length) :: Expr.fnAritiesL args
  | .min a b => a.fnArities ++ b.fnArities

def Expr.fnAritiesL : List Expr → List (FnName × Nat)
  | [] => []
  | e :: es => e.fnArities ++ Expr.fnAritiesL es

end

def Pattern.fnArities : Pattern → List (FnName × Nat)
  | .expr e => e.fnArities
  | .eq e₁ e₂ => e₁.fnArities ++ e₂.fnArities

def Action.fnArities : Action → List (FnName × Nat)
  | .expr e => e.fnArities
  | .union e₁ e₂ => e₁.fnArities ++ e₂.fnArities

/-- The names a merge specification applies. A `:merge` body is an expression position like
any other, so a constructor mentioned *only* there — `(set (Log (A)) old)` — still has to
be declared, and the function it `set`s still has to be a name the emitter knows. -/
def MergeSpec.fnArities : MergeSpec → List (FnName × Nat)
  | .merge _ _ body res => body.flatMap Action.fnArities ++ Expr.fnAritiesL res

def Cmd.fnArities : Cmd → List (FnName × Nat)
  | .action a => a.fnArities
  | .rule r => (r.query.flatMap Pattern.fnArities) ++ (r.actions.flatMap Action.fnArities)
  | .run _ => []
  | .saturate _ => []
  | .decl f d => (f, d.entryWidth) :: (d.merge.map MergeSpec.fnArities).getD []
  | .check q => q.flatMap Pattern.fnArities

/-- Every function the program uses, with its arity, deduplicated. -/
def Program.fnArities (p : Program) : List (FnName × Nat) :=
  (p.flatMap Cmd.fnArities).dedup

/-- The names the program declares as merge functions. These are `function` commands, not
constructors. -/
def Program.mergeNames (p : Program) : List FnName :=
  p.filterMap fun c => match c with
    | .decl f d => if d.merge.isSome then some f else none
    | _ => none

/-- The constructors: everything used that is not a declared `:merge` function. -/
def Program.ctorArities (p : Program) : List (FnName × Nat) :=
  p.fnArities.filter fun fa => fa.1 ∉ p.mergeNames

/-- Every name the program declares, whatever it declares it as. -/
def Program.declaredNames (p : Program) : List FnName :=
  p.filterMap fun c => match c with
    | .decl f _ => some f
    | _ => none

/-- A `(constructor …)` for every constructor the program applies and does not declare.

**Declaration is required** (`Signature.IsCtor`), so a program that applies a name nobody
declared gets stuck in `Expr.eval` and `execM` returns `none`. Generated programs apply
constructors without declaring them, so the declarations are read off the *uses*; the
declared program is what the model evaluates and what `Cmd.toEgg` renders, so the two
sides agree. -/
def Program.ctorDecls (p : Program) : Program :=
  (p.ctorArities.filter fun fa => fa.1 ∉ p.declaredNames).map fun fa =>
    .decl fa.1 { arity := fa.2, outArity := 1, merge := none }

/-- The program with its constructors declared up front. What the difftest actually runs
and emits. -/
def Program.declared (p : Program) : Program := p.ctorDecls ++ p

/-! ### Which arities egglog will accept

Two halves, because the model declares only its `:merge` functions.

For a *declared* function, `Impl/Check.lean`'s `Cmd.arityOk` is the check — this only
walks the program threading `Cmd.sigBind` and renders the commands that fail.

For an *undeclared* one there is no declaration to check against, and the constraint comes
from this file instead: `ctorDecls` invents a declaration per `(name, arity)` pair, so a
name used at two arities emits two `constructor` commands and egglog answers "Function
already bound {name}". -/

def Program.arityErrorsFrom : Program → Signature → List String
  | [], _ => []
  | c :: cs, sig =>
      (if c.arityOk sig then [] else [c.toEgg sig]) ++ Program.arityErrorsFrom cs (c.sigBind sig)

/-- The commands whose column counts egglog's typechecker would reject, rendered. Empty is
the only acceptable value for a case the difftest emits. -/
def Program.arityErrors (p : Program) : List String :=
  p.arityErrorsFrom (fun _ => none)

/-! ### Where a program may read

`Impl/Check.lean`'s "Reading in an action": no expression may apply a non-constructor,
because that is a *lookup*, and the only read is the query atom `Pattern.values`. Walked the
same way `arityErrorsFrom` walks the arity check, so the difftest and the specification
share one definition. -/

def Program.illegalReadsFrom : Program → Signature → List String
  | [], _ => []
  | c :: cs, sig =>
      (if c.noLookup sig then [] else [c.toEgg sig])
        ++ Program.illegalReadsFrom cs (c.sigBind sig)

/-- The commands containing a read that is not a `Pattern.values` atom, rendered. Empty is
the only acceptable value for a case the difftest emits. egglog rejects this in a rule head
only; the other positions are ours, and `Spec/Scope.lean` says why. -/
def Program.illegalReads (p : Program) : List String :=
  p.illegalReadsFrom (fun _ => none)

/-- The names the program uses at more than one key arity. `fnArities` is deduplicated on
the *pair*, so such a name is exactly one occurring twice in it. -/
def Program.arityConflicts (p : Program) : List FnName :=
  ((p.fnArities.map Prod.fst).filter fun f =>
      1 < (p.fnArities.filter fun fa => fa.1 == f).length).dedup

/-- Every function `(print-size)` reports, in a stable order. Deduplicated by *name*:
`fnArities` keys on the pair, so a name used at two arities would appear twice — which
egglog cannot express anyway, but which would silently double a line here. -/
def Program.fnNames (p : Program) : List FnName := (p.fnArities.map Prod.fst).dedup

/-! ### The file -/

/-- The single sort the untyped model needs. Constructors are declared by their commands,
so the program must be `declared`. -/
def Program.eggHeader (_ : Program) : String := "(sort Math)"

/-- A `(ruleset <name>)` for every named ruleset the program mentions. egglog requires the
declaration before a rule may join one or a schedule may run one; the unnamed ruleset is
declared already, so a program that uses only that one emits nothing here. -/
def Program.rulesetDecls (p : Program) : List String :=
  ((p.filterMap fun c => match c with
    | .rule r => some r.ruleset
    | .run R => some R
    | .saturate R => some R
    | _ => none).filter (· ≠ "")).dedup.map fun R => "(ruleset " ++ R ++ ")"

/-- Render commands against the signatures they execute under. -/
def Program.commandsToEgg : Program → Signature → List String
  | [], _ => []
  | c :: cs, sig => c.toEgg sig :: Program.commandsToEgg cs (c.sigBind sig)

/-- The program as egglog source: the sort, the ruleset declarations, and the commands. -/
def Program.render (p : Program) : String :=
  String.intercalate "\n"
    (p.eggHeader :: p.rulesetDecls ++ (p.commandsToEgg (fun _ => none)).filter (· ≠ ""))
    ++ "\n"

/-- The program as a complete `.egg` file, ending in the `(print-size)` that the
comparison reads. -/
def Program.toEgg (p : Program) : String := p.render ++ "(print-size)\n"

/-- The row counts the interpreter predicts, one `name count` line per constructor, for
diffing against egglog's `(print-size)`. `STUCK` if the program does not run, which for a
well-scoped program with no failing lookup and no diverging merge it always does.

This is `Impl/Merge.lean`'s **M9** interpreter, not `Impl/Interp.lean`'s `exec`. `exec`
evaluates with `Expr.eval` and never runs a merge phase, so while it was what this read,
`mergeOne`, `mergeRound`, `execActions`, `patternHolds`'s row scan and the whole
`:merge` implementation had **no** differential coverage — the suite's pass count said
nothing about them. The two agree on the constructor fragment (see `execM`), so the 70
constructor cases are unaffected. -/
def Program.expectedSizes (p : Program) : String :=
  match execM p with
  | none => "STUCK\n"
  | some d =>
    String.intercalate "\n" (p.fnNames.map fun f => f ++ " " ++ toString (d.keyRowCount f))
      ++ "\n"

end Egglog
