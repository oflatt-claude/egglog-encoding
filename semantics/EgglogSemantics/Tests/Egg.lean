import EgglogSemantics.Impl.Interp

/-!
# Emitting egglog source

Renders a `Program` as a `.egg` file so that the same program can be run by the Rust
implementation and the results compared (`PLAN.md`, "Differential testing"). The oracle
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

/-- An expression as egglog source. -/
def Expr.toEgg : Expr → String
  | .lit (.int n) => toString n
  | .var v => v
  | .app f args => "(" ++ f ++ Expr.toEggArgs args ++ ")"

/-- `Expr.toEgg` over an argument list, each preceded by a space. -/
def Expr.toEggArgs : List Expr → String
  | [] => ""
  | e :: es => " " ++ e.toEgg ++ Expr.toEggArgs es

end

def Pattern.toEgg : Pattern → String
  | .expr e => e.toEgg
  | .eq e₁ e₂ => "(= " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"

def Action.toEgg : Action → String
  | .expr e => e.toEgg
  | .letBind v e => "(let " ++ v ++ " " ++ e.toEgg ++ ")"
  | .union e₁ e₂ => "(union " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"

def Rule.toEgg (r : Rule) : String :=
  "(rule (" ++ String.intercalate " " (r.query.map Pattern.toEgg) ++ ") ("
    ++ String.intercalate " " (r.actions.map Action.toEgg) ++ "))"

/-- A command as egglog source. `Cmd.run` is one round, so it emits `(run 1)`.
Declarations produce nothing here — they are folded into the `datatype` header. -/
def Cmd.toEgg : Cmd → String
  | .action a => a.toEgg
  | .rule r => r.toEgg
  | .run => "(run 1)"
  | .decl _ _ => ""

/-! ### Collecting the signature

The header has to declare every constructor, so the arities are read off the program's
uses rather than from `Signature` — generated programs need not declare anything. -/

mutual

def Expr.fnArities : Expr → List (FnName × Nat)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args.length) :: Expr.fnAritiesL args

def Expr.fnAritiesL : List Expr → List (FnName × Nat)
  | [] => []
  | e :: es => e.fnArities ++ Expr.fnAritiesL es

end

def Pattern.fnArities : Pattern → List (FnName × Nat)
  | .expr e => e.fnArities
  | .eq e₁ e₂ => e₁.fnArities ++ e₂.fnArities

def Action.fnArities : Action → List (FnName × Nat)
  | .expr e => e.fnArities
  | .letBind _ e => e.fnArities
  | .union e₁ e₂ => e₁.fnArities ++ e₂.fnArities

def Cmd.fnArities : Cmd → List (FnName × Nat)
  | .action a => a.fnArities
  | .rule r => (r.query.flatMap Pattern.fnArities) ++ (r.actions.flatMap Action.fnArities)
  | .run => []
  | .decl f d => [(f, d.arity)]

/-- Every constructor the program uses, with its arity, deduplicated. -/
def Program.fnArities (p : Program) : List (FnName × Nat) :=
  (p.flatMap Cmd.fnArities).dedup

/-- The constructor names, in the order the header declares them. -/
def Program.fnNames (p : Program) : List FnName := p.fnArities.map Prod.fst

/-! ### The file -/

/-- The single-sort `datatype` declaration the untyped model needs. -/
def Program.eggHeader (p : Program) : String :=
  "(datatype Math " ++ String.intercalate " "
    (p.fnArities.map fun fa =>
      "(" ++ fa.1 ++ String.join (List.replicate fa.2 " Math") ++ ")") ++ ")"

/-- The program as a complete `.egg` file, ending in the `(print-size)` that the
comparison reads. -/
def Program.toEgg (p : Program) : String :=
  String.intercalate "\n"
    (p.eggHeader :: (p.map Cmd.toEgg).filter (· ≠ "") ++ ["(print-size)", ""])

/-- The row counts the interpreter predicts, one `name count` line per constructor, for
diffing against egglog's `(print-size)`. `STUCK` if the program does not run, which for a
well-scoped program it always does. -/
def Program.expectedSizes (p : Program) : String :=
  match exec p with
  | none => "STUCK\n"
  | some d =>
    String.intercalate "\n" (p.fnNames.map fun f => f ++ " " ++ toString (d.rowCount f))
      ++ "\n"

end Egglog
