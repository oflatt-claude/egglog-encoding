import EgglogSemantics.Provenance.Checker

namespace Egglog.Provenance

def namePrefix : String := "@prov:"
def globalName (i : Nat) : FnName := namePrefix ++ "global:" ++ toString i
def ruleName (i j : Nat) : FnName := namePrefix ++ "rule:" ++ toString i ++ ":" ++ toString j
def bodyName (f : FnName) (j : Nat) : FnName := namePrefix ++ "body:" ++ f ++ ":" ++ toString j
def resultName (f : FnName) : FnName := namePrefix ++ "result:" ++ f
def subtermName : FnName := namePrefix ++ "subterm"
def proofVar (i : Nat) : Var := namePrefix ++ "p" ++ toString i

def ctor (n : Nat) : FnDecl := ⟨n, 1, none, none⟩

def leaf : Expr → Bool
  | .lit _ => true
  | .var v => !namePrefix.isPrefixOf v
  | _ => false

def sameLeaf : Expr → Expr → Bool
  | .lit a, .lit b => a == b
  | .var a, .var b => a == b
  | _, _ => false

mutual

def valueExprOk (sig : Signature) (vars : List Var) : Expr → Bool
  | .lit _ => true
  | .var v => vars.contains v && !namePrefix.isPrefixOf v
  | .app f args =>
      !namePrefix.isPrefixOf f && valueExprsOk sig vars args &&
        (sig f).any fun d => d.merge.isNone && args.length == d.arity
  | .min a b => valueExprOk sig vars a && valueExprOk sig vars b

def valueExprsOk (sig : Signature) (vars : List Var) : List Expr → Bool
  | [] => true
  | e :: es => valueExprOk sig vars e && valueExprsOk sig vars es

end

def tableActionOk (sig : Signature) (vars : List Var) : Action → Bool
  | .expr (.app f cols) => (sig f).any fun d =>
      d.merge.isSome && cols.length == d.entryWidth && valueExprsOk sig vars cols
  | _ => false

/-- Find a table premise that establishes a leaf's existence. -/
def witness (q : Query) (e : Expr) : Option Nat :=
  (q.zipIdx.find? fun pi => match pi.1 with
    | .expr (.app _ cols) => cols.any (sameLeaf e)
    | _ => false).map Prod.snd

def queryOk (sig : Signature) (q : Query) : Bool := q.all fun p => match p with
  | .expr (.app f cols) => (sig f).any fun d =>
      d.merge.isSome && cols.length == d.entryWidth && cols.all leaf
  | .eq a b => leaf a && leaf b && ((witness q a).isSome || (witness q b).isSome)
  | _ => false

def mergeVars (n : Nat) : List Var :=
  if n == 1 then ["old", "new"] else
    (List.range n).flatMap fun i => ["old" ++ toString i, "new" ++ toString i]

def programOk (P : Program) (sig : Signature) : Bool := P.all fun c => match c with
  | .decl f d => !namePrefix.isPrefixOf f && match d.merge with
    | none => true
    | some .noMerge => false
    | some (.merge body res) =>
        body.all (tableActionOk sig (mergeVars d.outArity)) &&
          res.length == d.outArity && valueExprsOk sig (mergeVars d.outArity) res
  | .action a => tableActionOk sig [] a
  | .rule r => queryOk sig r.query &&
      r.query.vars.all (fun v => (witness r.query (.var v)).isSome) &&
      r.actions.all (tableActionOk sig r.query.vars)
  | _ => true

def encodePattern (i : Nat) : Pattern → Pattern
  | .expr (.app f cols) => .expr (.app f (cols ++ [.var (proofVar i)]))
  | p => p

def premiseExpr (q : Query) (i : Nat) (p : Pattern) : Option Expr := match p with
  | .expr _ => some (.var (proofVar i))
  | .eq a b => do
      let j ← witness q a <|> witness q b
      some (.app subtermName [a, .var (proofVar j)])

def encodeAction (pf : Expr) : Action → Action
  | .expr (.app f cols) => .expr (.app f (cols ++ [pf]))
  | a => a

def encodeRule (i : Nat) (r : Rule) : Option Rule := do
  let ps ← r.query.zipIdx.mapM fun pi => premiseExpr r.query pi.2 pi.1
  let payload := r.query.vars.map Expr.var ++ ps
  some { r with
    query := r.query.zipIdx.map fun pi => encodePattern pi.2 pi.1
    actions := r.actions.zipIdx.map fun aj =>
      encodeAction (.app (ruleName i aj.2) payload) aj.1 }

mutual

def renameExpr (rename : Var → Var) : Expr → Expr
  | .lit l => .lit l
  | .var v => .var (rename v)
  | .app f args => .app f (renameExprs rename args)
  | .min a b => .min (renameExpr rename a) (renameExpr rename b)

def renameExprs (rename : Var → Var) : List Expr → List Expr
  | [] => []
  | e :: es => renameExpr rename e :: renameExprs rename es

end

def renameAction (rename : Var → Var) : Action → Action
  | .expr e => .expr (renameExpr rename e)
  | .union a b => .union (renameExpr rename a) (renameExpr rename b)

def renameMerge (n : Nat) (v : Var) : Var :=
  if n == 1 && (v == "old" || v == "new") then v ++ "0" else v

def mergeProof (n : Nat) (side : String) : Expr :=
  .var (if n == 0 then side else side ++ toString n)

def encodeDecl (f : FnName) (d : FnDecl) : FnDecl :=
  match d.merge with
  | some (.merge body res) =>
    let old := mergeProof d.outArity "old"
    let new := mergeProof d.outArity "new"
    let rename := renameMerge d.outArity
    let res' := renameExprs rename res
    let pf := .app (resultName f) [old, new]
    { d with
      outArity := d.outArity + 1
      identityVals := some (min ((d.unchangedWidth body).getD d.outArity) d.outArity)
      merge := some (.merge
        (body.zipIdx.map fun aj =>
          encodeAction (.app (bodyName f aj.2) [old, new]) (renameAction rename aj.1))
        (res' ++ [pf])) }
  | _ => d

def proofDecls (P : Program) : Program :=
  .decl subtermName (ctor 2) :: P.zipIdx.flatMap fun ci => match ci.1 with
    | .decl f d => match d.merge with
      | some (.merge body _) => .decl (resultName f) (ctor 2) ::
          body.zipIdx.map fun aj => .decl (bodyName f aj.2) (ctor 2)
      | _ => []
    | .action _ => [.decl (globalName ci.2) (ctor 0)]
    | .rule r => r.actions.zipIdx.map fun aj =>
        .decl (ruleName ci.2 aj.2) (ctor (r.query.vars.length + r.query.length))
    | _ => []

def encodeCmd (i : Nat) : Cmd → Option Cmd
  | .decl f d => some (.decl f (encodeDecl f d))
  | .action a => some (.action (encodeAction (.app (globalName i) []) a))
  | .rule r => (encodeRule i r).map Cmd.rule
  | c => some c

/-- Instrument flat table programs, including every congruence-compiled program in
the current source fragment. Equality witnesses come from their table premises. -/
def encode (P : Program) : Option Program := do
  let C ← SourceProof.contextOf P
  if !programOk P C.sig then none else do
    let body ← P.zipIdx.mapM fun ci => encodeCmd ci.2 ci.1
    some (proofDecls P ++ body)

end Egglog.Provenance
