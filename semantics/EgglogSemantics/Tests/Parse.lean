import EgglogSemantics.Tests.Egg

/-!
# Parsing egglog source

The inverse of `Program.toEgg`: reads the fragment the emitter writes, so programs can be
kept as `.egg` files and hand-written in egglog's own syntax. Sorts are read for arity
only, since the model is untyped. `(sort …)`, `(ruleset …)` and `(print-size)` carry no
command.
-/

namespace Egglog

inductive Sexp where
  | atom (s : String)
  | str (s : String)
  | list (xs : List Sexp)
  deriving Repr, BEq, Inhabited

namespace Sexp

private inductive Token where
  | open_ | close | atom (s : String) | str (s : String)
  deriving Repr, Inhabited

private def delimiter (c : Char) : Bool := c.isWhitespace || c == '(' || c == ')' || c == ';'

private partial def tokenize (cs : List Char) (acc : Array Token) : Except String (Array Token) :=
  match cs with
  | [] => .ok acc
  | ';' :: rest => tokenize (rest.dropWhile (· != '\n')) acc
  | '(' :: rest => tokenize rest (acc.push .open_)
  | ')' :: rest => tokenize rest (acc.push .close)
  | '"' :: rest =>
    let body := rest.takeWhile (· != '"')
    match rest.drop body.length with
    | '"' :: rest => tokenize rest (acc.push (.str (String.ofList body)))
    | _ => .error "unterminated string"
  | c :: rest =>
    if c.isWhitespace then tokenize rest acc else
      let word := c :: rest.takeWhile (!delimiter ·)
      tokenize (rest.drop (word.length - 1)) (acc.push (.atom (String.ofList word)))

private partial def parseOne (ts : List Token) : Except String (Sexp × List Token) :=
  match ts with
  | [] => .error "unexpected end of input"
  | .close :: _ => .error "unexpected `)`"
  | .atom s :: rest => .ok (.atom s, rest)
  | .str s :: rest => .ok (.str s, rest)
  | .open_ :: rest => do
    let (xs, rest) ← parseMany rest #[]
    pure (.list xs.toList, rest)
where
  parseMany (ts : List Token) (acc : Array Sexp) : Except String (Array Sexp × List Token) :=
    match ts with
    | [] => .error "missing `)`"
    | .close :: rest => .ok (acc, rest)
    | ts => do
      let (x, rest) ← parseOne ts
      parseMany rest (acc.push x)

/-- Every top-level S-expression of `src`. -/
def parseAll (src : String) : Except String (List Sexp) := do
  let ts ← tokenize src.toList #[]
  let rec go (ts : List Token) (acc : Array Sexp) (fuel : Nat) : Except String (List Sexp) :=
    match fuel, ts with
    | _, [] => .ok acc.toList
    | 0, _ => .error "input too long"
    | fuel + 1, ts => do
      let (x, rest) ← parseOne ts
      go rest (acc.push x) fuel
  go ts.toList #[] ts.size

end Sexp

namespace Parse

open Sexp

def expr : Sexp → Except String Expr
  | .atom s => .ok (match s.toInt? with | some n => .lit (.int n) | none => .var s)
  | .str s => .error s!"unexpected string \"{s}\""
  | .list [.atom "min", a, b] => do pure (.min (← expr a) (← expr b))
  | .list (.atom f :: args) => do pure (.app f (← args.mapM expr))
  | .list _ => .error "an application starts with a name"

/-- One expression per value column: `(values e…)` or a single expression. -/
def values : Sexp → Except String (List Expr)
  | .list (.atom "values" :: es) => es.mapM expr
  | s => do pure [← expr s]

/-- `(f k…)` for a declared merge function `f` with its key columns. -/
def entry (sig : Signature) : Sexp → Option (FnName × FnDecl × List Sexp)
  | .list (.atom f :: ks) => do
    let d ← sig f
    if d.merge.isSome && ks.length == d.arity then some (f, d, ks) else none
  | _ => none

def entryExpr (f : FnName) (d : FnDecl) (ks : List Sexp) (vs : Sexp) :
    Except String Expr := do
  let keys ← ks.mapM expr
  let vals ← values vs
  if vals.length != d.outArity then
    .error s!"{f} has {d.outArity} value columns, not {vals.length}"
  else pure (.app f (keys ++ vals))

/-- A query fact. `(= v (f k…))` reads an entry of a merge function; otherwise `=` is an
equality between value expressions. -/
def pattern (sig : Signature) : Sexp → Except String Pattern
  | .list [.atom "=", a, b] =>
    match entry sig b with
    | some (f, d, ks) => do pure (.expr (← entryExpr f d ks a))
    | none => do pure (.eq (← expr a) (← expr b))
  | s => do pure (.expr (← expr s))

def action (sig : Signature) : Sexp → Except String Action
  | .list [.atom "union", a, b] => do pure (.union (← expr a) (← expr b))
  | .list [.atom "set", target, v] =>
    match entry sig target with
    | some (f, d, ks) => do pure (.expr (← entryExpr f d ks v))
    | none => .error "set of something that is not a merge function entry"
  | s => do pure (.expr (← expr s))

/-- Keyword options such as `:ruleset R`, as (keyword, argument) pairs; a keyword with no
argument pairs with `none`. -/
def options : List Sexp → Except String (List (String × Option Sexp))
  | [] => .ok []
  | .atom k :: .atom v :: rest =>
    if !k.startsWith ":" then .error s!"unexpected {k}"
    else if v.startsWith ":" then do pure ((k, none) :: (← options (.atom v :: rest)))
    else do pure ((k, some (.atom v)) :: (← options rest))
  | .atom k :: v :: rest =>
    if k.startsWith ":" then do pure ((k, some v) :: (← options rest))
    else .error s!"unexpected {k}"
  | [.atom k] => if k.startsWith ":" then .ok [(k, none)] else .error s!"unexpected {k}"
  | s :: _ => .error s!"unexpected {repr s}"

def mergeSpec (sig : Signature) (width : Nat) : Sexp → Except String MergeSpec
  | .list (first :: rest) =>
    match first with
    | .list _ => do
      let body := first :: rest
      let some res := body.getLast? | .error "empty merge block"
      let actions ← (body.dropLast).mapM (action sig)
      pure (.merge (mergeParamsToEgg "old" width) (mergeParamsToEgg "new" width)
        actions (← values res))
    | _ => do
      pure (.merge (mergeParamsToEgg "old" width) (mergeParamsToEgg "new" width)
        [] (← values (.list (first :: rest))))
  | s => do
    pure (.merge (mergeParamsToEgg "old" width) (mergeParamsToEgg "new" width) [] (← values s))

def columns : Sexp → Nat
  | .list xs => xs.length
  | _ => 1

def decl (sig : Signature) (f : FnName) (ins : Sexp) (out : Sexp) (opts : List Sexp)
    (isCtor : Bool) : Except String FnDecl := do
  let .list sorts := ins | .error s!"{f}: input sorts are a list"
  let opts ← options opts
  if isCtor then
    if opts.any (fun o => o.1 != ":cost" && o.1 != ":unextractable") then
      .error s!"{f}: unsupported constructor option"
    else pure ⟨sorts.length, 1, none, none⟩
  else
    let merge ← match opts.find? (·.1 == ":merge") with
      | some (_, some m) => mergeSpec sig (columns out) m
      | _ => .error s!"{f}: a function needs `:merge`"
    pure ⟨sorts.length, columns out, some merge, none⟩

def rule (sig : Signature) (query actions : Sexp) (opts : List Sexp) :
    Except String Rule := do
  let .list qs := query | .error "a rule's query is a list"
  let .list as := actions | .error "a rule's actions are a list"
  let opts ← options opts
  let ruleset ← match opts.find? (·.1 == ":ruleset") with
    | some (_, some (.atom r)) => pure r
    | some _ => .error "`:ruleset` takes a name"
    | none => pure ""
  pure ⟨← qs.mapM (pattern sig), ← as.mapM (action sig), ruleset⟩

def runTarget : Sexp → Except String RulesetName
  | .atom r => .ok r
  | .list [.atom "run"] => .ok ""
  | .list [.atom "run", .atom r] => .ok r
  | _ => .error "unsupported schedule"

/-- The commands of one top-level form, under the signature so far. -/
def command (sig : Signature) : Sexp → Except String (List Cmd)
  | .list (.atom "sort" :: _) | .list (.atom "ruleset" :: _) | .list [.atom "print-size"] =>
    .ok []
  | .list (.atom "constructor" :: .atom f :: ins :: out :: opts) => do
    pure [.decl f (← decl sig f ins out opts true)]
  | .list (.atom "function" :: .atom f :: ins :: out :: opts) => do
    pure [.decl f (← decl sig f ins out opts false)]
  | .list (.atom "rule" :: query :: actions :: opts) => do
    pure [.rule (← rule sig query actions opts)]
  | .list [.atom "run", .atom n] =>
    match n.toNat? with
    | some n => .ok (List.replicate n (.run ""))
    | none => .ok [.run n]
  | .list [.atom "run", .atom r, .atom n] =>
    match n.toNat? with
    | some n => .ok (List.replicate n (.run r))
    | none => .error "`run` takes a ruleset and a count"
  | .list [.atom "run-schedule", .list [.atom "saturate", target]] => do
    pure [.saturate (← runTarget target)]
  | .list (.atom "datatype" :: _) => .error "`datatype` is not supported; use `constructor`"
  | s@(.list (.atom head :: _)) =>
    if head.startsWith ":" then .error s!"unsupported command {head}"
    else do pure [.action (← action sig s)]
  | s => .error s!"unsupported command {repr s}"

end Parse

/-- Parse a program from egglog source. -/
def Program.ofEgg (src : String) : Except String Program := do
  let forms ← Sexp.parseAll src
  let (_, cmds) ← forms.foldlM (fun (state : Signature × Array Cmd) form => do
    let cmds ← Parse.command state.1 form
    pure (cmds.foldl (fun sig c => c.sigBind sig) state.1, state.2 ++ cmds.toArray))
    ((fun _ => none), #[])
  pure cmds.toList

end Egglog

namespace Egglog.Parse.Tests

set_option linter.hashCommand false

/-- Parsing rendered source gives it back. -/
private def roundTrip (src : String) : Bool :=
  match Program.ofEgg src with
  | .ok p => p.render == src
  | .error _ => false

#guard roundTrip "(sort Math)\n(ruleset R)\n(constructor A () Math)\n(constructor F (Math) Math)\n\
  (F (A))\n(rule ((F x)) ((union (F x) x)) :ruleset R)\n(run-schedule (saturate R))\n(run 1)\n"
#guard roundTrip "(sort Math)\n(constructor A () Math)\n(function Log (Math) i64 :merge new)\n\
  (function Dist (Math) i64 :merge ((set (Log (A)) old) (min old new)))\n\
  (set (Dist (A)) 3)\n(rule ((= v (Dist x))) ((set (Dist x) (max v -2))))\n(run 1)\n"
#guard roundTrip "(sort Math)\n(constructor K () Math)\n\
  (function Bounds (Math) (i64 i64) :merge (values (min old0 new0) (min old1 new1)))\n\
  (set (Bounds (K)) (values 3 7))\n"
#guard (Program.ofEgg "(datatype Math (A))").isOk == false
#guard (Program.ofEgg "(constructor A () Math").isOk == false
#guard (Program.ofEgg "; a comment\n(sort Math) (constructor A () Math) (A)").isOk

end Egglog.Parse.Tests
