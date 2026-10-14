import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.Names

/-!
# Congruence compilation

This pass implements explicit union-find, rebuilding, and query flattening for the
constructor source fragment. Its only auxiliary tables are `@UF(key, parent)` and
`@fView(children…, id)`. There are no proof declarations, proof columns, or proof
expressions. Structural constructor terms serve as ids.

Query flattening is left-to-right postorder: visit every child before emitting its
parent's view atom. An equality visits its left side, then its right side, then emits
an equality of the resulting ids. Later resugaring can traverse the original query in
this same order; no separate flattening tree is needed.

`compile` retains rule origins alongside the commands. `encode` projects the executable
program. Origins do not affect execution; they distinguish source rule firings from
path compression, e-class propagation, and child re-keying during later resugaring.
-/

namespace Egglog.Congruence

/-- Generated maintenance rules, including the position a child rule rewrites. -/
inductive RebuildOrigin where
  | compress
  | eclass (constructor : FnName)
  | child (constructor : FnName) (index : Nat)
  deriving DecidableEq, Repr

/-- A source rule is identified by its command index in the original program. -/
inductive RuleOrigin where
  | source (commandIndex : Nat)
  | rebuild (kind : RebuildOrigin)
  deriving DecidableEq, Repr

/-- The tag travels with its command, including copies in source saturation rulesets. -/
structure Command where
  command : Cmd
  ruleOrigin : Option RuleOrigin := none

/-- The two kinds of generated function table; source constructors retain their names. -/
inductive TableRole where
  | unionFind
  | view (constructor : FnName)
  deriving DecidableEq, Repr

/-- Resolve generated table names against the original program. -/
def tableRole (P : Program) (f : FnName) : Option TableRole :=
  if f = ufName then some .unionFind else
    (P.ctors.find? fun fk => viewName fk.1 == f).map fun fk => .view fk.1

/-- A collision retains the smaller id and links both ids to it; for the smaller one that
is a self-loop, which is not a union-find edge. With one output column, `mergeEnv`
supplies the ordinary `old` and `new` bindings. -/
def mergeBody : List Action :=
  [.expr (.app ufName [.var "old", .min (.var "old") (.var "new")]),
   .expr (.app ufName [.var "new", .min (.var "old") (.var "new")])]

/-- The sole output column of both generated function tables. -/
def mergeResult : List Expr := [.min (.var "old") (.var "new")]

/-- A generated function with one id column. All output columns determine change. -/
def tableDecl (arity : Nat) : FnDecl :=
  { arity, outArity := 1, merge := some (.merge mergeBody mergeResult) }

/-- Structural ids use the source constructor and its original arity. -/
def ctorDecl (arity : Nat) : FnDecl := { arity, outArity := 1, merge := none }

mutual

/-- Flatten one expression, returning its id, ordered atoms, and next fresh variable. -/
def encodeQueryExpr : Expr → Nat → Expr × Query × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .min a b, n => (.min a b, [], n)
  | .app f args, n =>
      match encodeQueryArgs args n with
      | (es, ps, next) =>
          (.var (freshVar next),
            ps ++ [.expr (.app (viewName f) (es ++ [.var (freshVar next)]))], next + 1)

/-- Visit arguments from left to right. Repeated subexpressions keep distinct positions. -/
def encodeQueryArgs : List Expr → Nat → List Expr × Query × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeQueryExpr e n with
      | (e', ps, next) =>
          match encodeQueryArgs es next with
          | (es', qs, last) => (e' :: es', ps ++ qs, last)

end

/-- Equality joins the ids produced by the two ordered traversals. -/
def encodePattern : Pattern → Nat → Query × Nat
  | .expr e, n => ((encodeQueryExpr e n).2.1, (encodeQueryExpr e n).2.2)
  | .eq lhs rhs, n =>
      match encodeQueryExpr lhs n with
      | (l, ps, next) =>
          match encodeQueryExpr rhs next with
          | (r, qs, last) => (ps ++ qs ++ [.eq l r], last)

/-- Preserve source conjunct order. -/
def encodeQuery : Query → Nat → Query × Nat
  | [], n => ([], n)
  | p :: ps, n =>
      match encodePattern p n with
      | (qs, next) =>
          match encodeQuery ps next with
          | (rest, last) => (qs ++ rest, last)

mutual

/-- Build children before their parent. The original expression itself is the structural
id, so no temporary variable or table lookup is needed in a head. -/
def encodeBuild : Expr → List Action
  | .lit _ | .var _ => []
  | .min a b => encodeBuild a ++ encodeBuild b
  | .app f args =>
      encodeBuildArgs args ++ [.expr (.app (viewName f) (args ++ [.app f args]))]

/-- Build argument occurrences in the same left-to-right order as query flattening. -/
def encodeBuildArgs : List Expr → List Action
  | [] => []
  | e :: es => encodeBuild e ++ encodeBuildArgs es

end

/-- A source union links both ids to the smaller one. -/
def encodeAction : Action → List Action
  | .expr e => encodeBuild e
  | .union a b => encodeBuild a ++ encodeBuild b ++
      [.expr (.app ufName [a, .min a b]), .expr (.app ufName [b, .min a b])]

/-- No justification argument is needed for compiling a head. -/
def encodeActions (as : List Action) : List Action := as.flatMap encodeAction

/-- Variable supplies are local to a rule; source names cannot use the `@` namespace. -/
def encodeRule (r : Rule) : Rule :=
  { query := (encodeQuery r.query 0).1, actions := encodeActions r.actions,
    ruleset := r.ruleset }

/-- Compress two explicit parent edges into one. -/
def pathCompressRule : Rule :=
  { query := [.expr (.app ufName [.var "@a", .var "@b"]),
              .expr (.app ufName [.var "@b", .var "@c"])],
    actions := [.expr (.app ufName [.var "@a", .var "@c"])],
    ruleset := rebuildRuleset }

/-- The key variables of a generated view rule. -/
def rebuildVars (arity : Nat) : List Expr :=
  (List.range arity).map fun i => .var ("@c" ++ toString i)

/-- Propagate a changed output id through a view. -/
def eclassRule (f : FnName) (arity : Nat) : Rule :=
  let cs := rebuildVars arity
  { query := [.expr (.app (viewName f) (cs ++ [.var "@e"])),
              .expr (.app ufName [.var "@e", .var "@x"])],
    actions := [.expr (.app (viewName f) (cs ++ [.var "@x"]))],
    ruleset := rebuildRuleset }

/-- Re-key one child column. Old entry terms remain recorded by the interpreter. -/
def childRule (f : FnName) (arity index : Nat) : Rule :=
  let cs := rebuildVars arity
  { query := [.expr (.app (viewName f) (cs ++ [.var "@e"])),
              .expr (.app ufName [.var ("@c" ++ toString index), .var "@x"])],
    actions := [.expr (.app (viewName f) (cs.set index (.var "@x") ++ [.var "@e"]))],
    ruleset := rebuildRuleset }

/-- Keep a rule and its origin together. -/
def taggedRule (r : Rule) (origin : RuleOrigin) : Command :=
  ⟨.rule r, some origin⟩

/-- One output rule and one rule per key column, in that order. -/
def rebuildRules (f : FnName) (arity : Nat) : List Command :=
  taggedRule (eclassRule f arity) (.rebuild (.eclass f)) ::
    (List.range arity).map fun i => taggedRule (childRule f arity i) (.rebuild (.child f i))

/-- Maintenance rules in the dedicated rebuild ruleset. -/
def maintenanceRules (P : Program) : List Command :=
  taggedRule pathCompressRule (.rebuild .compress) ::
    P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-- A copy in another ruleset retains exactly the same origin. -/
def inRuleset (R : RulesetName) (c : Command) : Command :=
  match c.command with
  | .rule r => { c with command := .rule { r with ruleset := R } }
  | _ => c

/-- Maintenance also participates in every source saturation round. -/
def allMaintenanceRules (P : Program) : List Command :=
  maintenanceRules P ++ P.saturateRulesets.flatMap fun R =>
    (maintenanceRules P).map (inRuleset R)

/-- Declare only union-find, views, and structural constructors. Construction history
needs no separate table: the view write already records its constructor id as a subterm. -/
def encodePrelude (P : Program) : List Command :=
  ⟨.decl ufName (tableDecl 1), none⟩ ::
    (P.ctors.flatMap fun fk =>
      [⟨.decl fk.1 (ctorDecl fk.2), none⟩,
       ⟨.decl (viewName fk.1) (tableDecl fk.2), none⟩]) ++ allMaintenanceRules P

/-- Rebuild after every source action or run. Source declarations are emitted once by
 the prelude; a rule's tag points back to its exact position in the original program. -/
def encodeCmd (index : Nat) : Cmd → List Command
  | .decl _ _ => []
  | .action a => (encodeAction a).map (fun a' => ⟨.action a', none⟩) ++
      [⟨.saturate rebuildRuleset, none⟩]
  | .rule r => [taggedRule (encodeRule r) (.source index)]
  | .run R => [⟨.run R, none⟩, ⟨.saturate rebuildRuleset, none⟩]
  | .saturate R => [⟨.saturate R, none⟩, ⟨.saturate rebuildRuleset, none⟩]

/-- Keep command indices stable even when declarations disappear or actions expand. -/
def encodeCmds : Program → Nat → List Command
  | [], _ => []
  | c :: cs, index => encodeCmd index c ++ encodeCmds cs (index + 1)

/-- The congruence pass with origins for later proof resugaring. -/
def compile (P : Program) : List Command := encodePrelude P ++ encodeCmds P 0

/-- The executable program, independent of all proof instrumentation. -/
def encode (P : Program) : Program := (compile P).map Command.command

end Egglog.Congruence
