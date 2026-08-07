import EgglogSemantics.Impl.Merge
import EgglogSemantics.Tests.Egg

/-!
# Emitting egglog source for M9 programs

`Tests/Egg.lean` renders a constructor-only `Program`; this renders an `MProgram`, so
that `:merge` programs can be run by the Rust implementation and compared. The oracle is
the same `(print-size)`.

**Sorts finally bite.** egglog typechecks a `(function …)` declaration, so a merge
function needs a real output sort. The fragment picks `i64`, the way `tests/interval.egg`
and `tests/merge-during-rebuild.egg` do:

```text
(datatype Math (A) (B) (X) (Y))
(function Dist (Math Math) i64 :merge (min old new))
```

An eq-sorted merge output would dodge the base sort, but then `ordering-min` has to
render — and this model's `Term.blt` is *structural* where egglog's `ordering-min` is by
insertion order, so the two would choose different representatives. Row counts are per
key class and would survive that, but nothing else would. `i64` is the safer half.

Keys stay eq-sorted (`Math`), so `Term.lit` appears only as a merge function's *value*,
never as a constructor argument — which keeps `Egg.lean`'s standing literal mismatch
(`Term.lit` shares a sort with applications here, `i64` is separate in egglog) out of
the way.
-/

namespace Egglog
/-- A row action as egglog source. -/
def RowAction.toEgg : RowAction → String
  | .expr e => e.toEgg
  | .letBind v e => "(let " ++ v ++ " " ++ e.toEgg ++ ")"
  | .union e₁ e₂ => "(union " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"
  | .set f args out =>
      "(set (" ++ f ++ Expr.toEggArgs args ++ ") " ++ out.toEgg ++ ")"

def MRule.toEgg (r : MRule) : String :=
  "(rule (" ++ String.intercalate " " (r.query.map Pattern.toEgg) ++ ") ("
    ++ String.intercalate " " (r.actions.map RowAction.toEgg) ++ "))"

/-- A merge specification as egglog source. A `.merge` with an empty action block is the
expression form `:merge e`; with actions it is the block form. `.union` is a constructor
and never reaches here; `.noMerge` is `:no-merge`. -/
def MergeSpec.toEgg : MergeSpec → String
  | .union => ""
  | .noMerge => " :no-merge"
  | .merge [] [e] => " :merge " ++ e.toEgg
  | .merge body res =>
      " :merge ((" ++ String.intercalate " " (body.map RowAction.toEgg) ++ ") (values "
        ++ String.intercalate " " (res.map Expr.toEgg) ++ "))"

/-- A `:merge` function's declaration. Keys are `Math`; the output is `i64`. -/
def FnDecl.toEgg (f : FnName) (d : FnDecl) : String :=
  "(function " ++ f ++ " (" ++ String.intercalate " " (List.replicate d.arity "Math")
    ++ ") i64" ++ d.merge.toEgg ++ ")"

/-- A command as egglog source. A declaration renders here rather than in the header,
unlike a constructor's. -/
def MCmd.toEgg : MCmd → String
  | .action a => a.toEgg
  | .rule r => r.toEgg
  | .run => "(run 1)"
  | .decl f d => FnDecl.toEgg f d

/-! ### Collecting the signature

Constructors go in the one `datatype`; declared `:merge` functions get their own
`function` command and must be kept *out* of it. -/
def RowAction.fnArities : RowAction → List (FnName × Nat)
  | .expr e => e.fnArities
  | .letBind _ e => e.fnArities
  | .union e₁ e₂ => e₁.fnArities ++ e₂.fnArities
  | .set f args out => (f, args.length) :: Expr.fnAritiesL args ++ out.fnArities

def MCmd.fnArities : MCmd → List (FnName × Nat)
  | .action a => a.fnArities
  | .rule r => (r.query.flatMap Pattern.fnArities)
      ++ (r.actions.flatMap RowAction.fnArities)
  | .run => []
  | .decl f d => [(f, d.arity)]

/-- The names a program declares with a `:merge`. -/
def MProgram.mergeNames (p : MProgram) : List FnName :=
  p.filterMap fun c => match c with
    | .decl f _ => some f
    | _ => none

/-- Every name the program uses with its arity, deduplicated. -/
def MProgram.fnArities (p : MProgram) : List (FnName × Nat) :=
  (p.flatMap MCmd.fnArities).dedup

/-- The constructors: everything used that is not a declared `:merge` function. -/
def MProgram.ctorArities (p : MProgram) : List (FnName × Nat) :=
  p.fnArities.filter fun fa => fa.1 ∉ p.mergeNames

/-- Every function `(print-size)` will report, in a stable order. Deduplicated by
*name*: `fnArities` keys on the pair, so a name used at two arities would appear twice —
which egglog cannot express anyway, but which would silently double a line here. -/
def MProgram.fnNames (p : MProgram) : List FnName := (p.fnArities.map Prod.fst).dedup

/-! ### The file -/
def MProgram.eggHeader (p : MProgram) : String :=
  "(datatype Math " ++ String.intercalate " "
    (p.ctorArities.map fun fa =>
      "(" ++ fa.1 ++ String.join (List.replicate fa.2 " Math") ++ ")") ++ ")"

/-- The program as a complete `.egg` file. -/
def MProgram.toEgg (p : MProgram) : String :=
  String.intercalate "\n"
    (p.eggHeader :: (p.map MCmd.toEgg).filter (· ≠ "") ++ ["(print-size)", ""])

/-- The row counts the interpreter predicts, one `name count` line per function. -/
def MProgram.expectedSizes (p : MProgram) : String :=
  match execM p with
  | none => "STUCK\n"
  | some d =>
    String.intercalate "\n" (p.fnNames.map fun f => f ++ " " ++ toString (d.rowCount f))
      ++ "\n"

end Egglog
