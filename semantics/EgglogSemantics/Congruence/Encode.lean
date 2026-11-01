import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.Names
import Architect

/-!
# Congruence compilation

This pass implements an explicit union-find for the constructor source fragment using
rules only. Its one auxiliary table is the relation `@UF(key, parent)`, whose rows are
never nested; there are no proof columns and no proof expressions. Source terms serve as
their own ids: building `f(ā)` asserts the self-loop `@UF(f(ā), f(ā))`, and the term exists
in the target as that row's key.

The union-find changes only through rules. A maintenance rule matches a stale edge,
subsumes it, and writes its replacement; its disequality guard makes it fire only where the
replacement differs from the row, so no rule subsumes a row that it writes, and a self-loop
is never re-derived from itself. A collision of two parents keeps the smaller id, subsumes
the other edge, and links the larger id under the smaller. Congruence is one rule per
constructor: two applications whose children have the same parents link the larger of
their roots under the smaller. A subsumed row stays in its table, as in egglog, but no
query matches it again; a stale edge is never needed again, since leaders only move down
the term order.

A query matches the terms themselves and joins the union-find in between. Flattening is
left-to-right postorder: visit every child before emitting its parent's atoms. An
application becomes the application over fresh child variables, one edge from each child
variable to the child's id, and one edge from the application to a fresh root, which is
its id; a value is its own id. An equality visits its left side, then its right side,
then equates the resulting ids. Later resugaring traverses the original query in this same
order; no separate flattening tree is needed.

The paper displays the pass as inference rules; they are the `@[blueprint]` statements of
the definitions below, so the paper and the compiler change together.

A source run becomes the run of the compiled rules followed by a saturation of the
maintenance rules, and sequences and saturations compile structurally, so every pass of a
compiled saturation is one source pass with a complete rebuild after each of its runs, as
in egglog's instrumented schedules. `compile` also returns one origin per compiled rule, in
the order of `Program.rules`; `encode` is the program alone. Origins do not affect
execution; they distinguish source rule firings from path compression, collisions and
congruence during later resugaring.

The view tables of the previous encoding, one row per application keyed by the parents of
its children, materialize the joins these queries perform; the paper presents them as an
optimization of this encoding.
-/

namespace Egglog.Congruence

/-- Generated maintenance rules. -/
inductive RebuildOrigin where
  | compress
  | collide
  | congruence (constructor : FnName)
  deriving DecidableEq, Repr

/-- A source rule is identified by its position in `Program.rules` of the original program. -/
inductive RuleOrigin where
  | source (ruleIndex : Nat)
  | rebuild (kind : RebuildOrigin)
  deriving DecidableEq, Repr

/-- The compiled program with one origin per rule, in the order of `Program.rules`. -/
structure Compiled where
  program : Program
  origins : List RuleOrigin

/-- A union-find row. -/
def ufRow (key parent : Expr) : Expr := .app ufName [key, parent]

/-- Subsume a union-find row. -/
def subsumeUf (key parent : Expr) : Action := .subsume ufName [key, parent]

mutual

/-- `e ⇝ Q; x`: flatten one expression into its id and its ordered atoms. A value is its own
id and needs no atom. An application becomes the application over fresh child variables,
one edge from each child variable to the child's id, and one edge from the application to
a fresh root, which is its id. A pattern written as a bare `e` is the paper's shorthand for
`e = e` and compiles to `Q` alone. -/
@[blueprint "def:compile-query"
  (statement := /--
  \begin{mathpar}
  \ir{Value}{v\in\mathit{Var}\cup\mathit{Lit}}{v\leadsto\top;\ v}
  \and
  \ir{App}{e_i\leadsto Q_i;\ x_i\ (\forall i)\\ a_1,\ldots,a_n,y\text{ fresh}}
    {f(e_1,\ldots,e_n)\leadsto Q_1\land\cdots\land Q_n\land f(a_1,\ldots,a_n)
      \land\textstyle\bigwedge_i\mathtt{UF}(a_i,x_i)\land\mathtt{UF}(f(a_1,\ldots,a_n),y);\ y}
  \and
  \ir{Compare}{e_1\leadsto Q_1;\ x_1\\e_2\leadsto Q_2;\ x_2}
    {(e_1\bowtie e_2)\leadsto Q_1\land Q_2\land x_1\bowtie x_2}
  \and
  \ir{Query}{p_i\leadsto Q_i\ (\forall i)}{p_1\land\cdots\land p_n\leadsto Q_1\land\cdots\land Q_n}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def encodeQueryExpr : Expr → Nat → Expr × Query × Nat
  | .app f args, n =>
      match encodeQueryArgs args n with
      | (xs, ps, next) =>
          let as := (List.range args.length).map fun i => Expr.var (freshVar (next + i))
          let y := Expr.var (freshVar (next + args.length))
          (y,
            ps ++ .expr (.app f as) :: (as.zip xs).map (fun ax => .expr (ufRow ax.1 ax.2))
              ++ [.expr (ufRow (.app f as) y)],
            next + args.length + 1)
  | e, n => (e, [], n)

/-- Visit arguments from left to right. Repeated subexpressions keep distinct positions. -/
def encodeQueryArgs : List Expr → Nat → List Expr × Query × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeQueryExpr e n with
      | (x, ps, next) =>
          match encodeQueryArgs es next with
          | (xs, qs, last) => (x :: xs, ps ++ qs, last)

end

/-- A pattern that is an expression needs no id. Equality and disequality compare the ids
produced by the two ordered traversals. -/
def encodePattern : Pattern → Nat → Query × Nat
  | .expr e, n => ((encodeQueryExpr e n).2.1, (encodeQueryExpr e n).2.2)
  | .eq lhs rhs, n =>
      match encodeQueryExpr lhs n with
      | (l, ps, next) =>
          match encodeQueryExpr rhs next with
          | (r, qs, last) => (ps ++ qs ++ [.eq l r], last)
  | .ne lhs rhs, n =>
      match encodeQueryExpr lhs n with
      | (l, ps, next) =>
          match encodeQueryExpr rhs next with
          | (r, qs, last) => (ps ++ qs ++ [.ne l r], last)

/-- Preserve source conjunct order. -/
def encodeQuery : Query → Nat → Query × Nat
  | [], n => ([], n)
  | p :: ps, n =>
      match encodePattern p n with
      | (qs, next) =>
          match encodeQuery ps next with
          | (rest, last) => (qs ++ rest, last)

mutual

/-- Build children before their parent, and give every value a UF self-loop. A self-loop
for a value that already has a parent is stale and path compression removes it. -/
def encodeBuild : Expr → List Action
  | e@(.lit _) | e@(.var _) => [.expr (ufRow e e)]
  | .min a b => encodeBuild a ++ encodeBuild b
  | .app f args => encodeBuildArgs args ++ [.expr (ufRow (.app f args) (.app f args))]

/-- Build argument occurrences in the same left-to-right order as query flattening. -/
def encodeBuildArgs : List Expr → List Action
  | [] => []
  | e :: es => encodeBuild e ++ encodeBuildArgs es

end

/-- A source union links both ids to the smaller one; for the smaller one that is a
self-loop. A bare action `e` is the paper's shorthand for `union(e, e)`, whose extra edge
is the self-loop `exist(e)` already holds. Source subsumes are outside the fragment and
compile to nothing. -/
@[blueprint "def:compile-head"
  (statement := /--
  \[
  \operatorname{exist}(e)\triangleq\{\mathtt{UF}(e',e')\mid e'\text{ a subexpression of }e\}
  \]
  \begin{mathpar}
  \ir{Union}{ }{\kw{union}(e_1,e_2)\leadsto\operatorname{exist}(e_1)\cup\operatorname{exist}(e_2)
    \cup\{\mathtt{UF}(e_1,\min(e_1,e_2)),\ \mathtt{UF}(e_2,\min(e_1,e_2))\}}
  \and
  \ir{Head}{h_i\leadsto H_i\ (\forall i)}{\{h_1,\ldots,h_n\}\leadsto H_1\cup\cdots\cup H_n}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def encodeAction : Action → List Action
  | .expr e => encodeBuild e
  | .union a b => encodeBuild a ++ encodeBuild b ++
      [.expr (ufRow a (.min a b)), .expr (ufRow b (.min a b))]
  | .subsume _ _ => []

/-- No justification argument is needed for compiling a head. -/
def encodeActions (as : List Action) : List Action := as.flatMap encodeAction

/-- Variable supplies are local to a rule; source names cannot use the `@` namespace.
Query variables are bound to parents through union-find edges, which are roots once
rebuilding has completed, so the head needs no leader lookup. -/
def encodeRule (r : Rule) : Rule :=
  { query := (encodeQuery r.query 0).1, actions := encodeActions r.actions }

/-- Replace a parent edge by the edge to the parent's own parent. With `@a = @b` this
removes the stale self-loop of a value that acquired a parent. -/
def pathCompressRule : Rule :=
  { query := [.expr (ufRow (.var "@a") (.var "@b")),
              .expr (ufRow (.var "@b") (.var "@c")),
              .ne (.var "@b") (.var "@c")],
    actions := [subsumeUf (.var "@a") (.var "@b"),
                .expr (ufRow (.var "@a") (.var "@c"))] }

/-- Two parents of one key: keep the smaller, subsume the other edge, and link the larger
parent under the smaller. -/
def ufCollideRule : Rule :=
  { query := [.expr (ufRow (.var "@a") (.var "@b")),
              .expr (ufRow (.var "@a") (.var "@c")),
              .eq (.var "@b") (.min (.var "@b") (.var "@c")),
              .ne (.var "@b") (.var "@c")],
    actions := [subsumeUf (.var "@a") (.var "@c"),
                .expr (ufRow (.var "@c") (.var "@b"))] }

/-- `arity` generated variables with a common stem. -/
def congruenceVars (stem : String) (arity : Nat) : List Expr :=
  (List.range arity).map fun i => .var ("@" ++ stem ++ toString i)

/-- Two applications of `f` whose children have the same parents: link the larger of their
roots under the smaller. This is where congruence becomes an equation. -/
def congruenceRule (f : FnName) (arity : Nat) : Rule :=
  let as := congruenceVars "a" arity
  let bs := congruenceVars "b" arity
  let rs := congruenceVars "r" arity
  { query := [.expr (.app f as), .expr (.app f bs)] ++
      ((as.zip bs).zip rs).flatMap (fun abr =>
        [.expr (ufRow abr.1.1 abr.2), .expr (ufRow abr.1.2 abr.2)]) ++
      [.expr (ufRow (.app f as) (.var "@y")), .expr (ufRow (.app f bs) (.var "@z")),
       .eq (.var "@y") (.min (.var "@y") (.var "@z")), .ne (.var "@y") (.var "@z")],
    actions := [.expr (ufRow (.var "@z") (.var "@y"))] }

/-- The congruence rule of a constructor. A nullary constructor has one application and
needs none. -/
def rebuildRules (f : FnName) (arity : Nat) : List (Rule × RuleOrigin) :=
  if arity = 0 then [] else [(congruenceRule f arity, .rebuild (.congruence f))]

/-- The maintenance rules, with their origins. -/
@[blueprint "def:maintenance"
  (statement := /--
  \[
  M_P\triangleq\{\textsc{Compress},\ \textsc{Collide}\}\cup\{\textsc{Cong}_f\mid f\text{ applied in }P\}
  \]
  \[
  \begin{aligned}
  \textsc{Compress}&:\ \mathtt{UF}(a,b)\land\mathtt{UF}(b,c)\land b\ne c
    \Rightarrow\kw{subsume}(\mathtt{UF}(a,b)),\ \mathtt{UF}(a,c)\\
  \textsc{Collide}&:\ \mathtt{UF}(a,b)\land\mathtt{UF}(a,c)\land b=\min(b,c)\land b\ne c
    \Rightarrow\kw{subsume}(\mathtt{UF}(a,c)),\ \mathtt{UF}(c,b)\\
  \textsc{Cong}_f&:\ f(a_1,\ldots,a_n)\land f(b_1,\ldots,b_n)
    \land\textstyle\bigwedge_i\bigl(\mathtt{UF}(a_i,r_i)\land\mathtt{UF}(b_i,r_i)\bigr)\\
  &\quad\land\ \mathtt{UF}(f(a_1,\ldots,a_n),y)\land\mathtt{UF}(f(b_1,\ldots,b_n),z)
    \land y=\min(y,z)\land y\ne z\Rightarrow\mathtt{UF}(z,y)
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def maintenanceRules (P : Program) : List (Rule × RuleOrigin) :=
  (pathCompressRule, .rebuild .compress) :: (ufCollideRule, .rebuild .collide) ::
    P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-- The compiled rules of a source command's rules, numbered from `index` in
`Program.rules` of the source. -/
def encodeRules (index : Nat) (rs : List Rule) : List (Rule × RuleOrigin) :=
  rs.zipIdx.map fun ri => (encodeRule ri.1, .source (index + ri.2))

/-- The maintenance saturation, with its origins. -/
def rebuild (P : Program) : Schedule × List RuleOrigin :=
  let m := maintenanceRules P
  (.saturate (.run (m.map Prod.fst)), m.map Prod.snd)

/-- Compile a schedule, numbering source rules from `index` in `Program.rules`. Every run
is followed by a rebuild, so a compiled saturation's body ends at a rebuild fixpoint and
each of its passes is one source pass. -/
@[blueprint "def:compile-schedule"
  (statement := /--
  \begin{mathpar}
  \ir{Rule}{Q\leadsto Q'\\H\leadsto H'}{(Q\Rightarrow H)\leadsto(Q'\Rightarrow H')}
  \and
  \ir{Run}{r_i\leadsto r_i'\ (\forall i)}
    {\kw{run}\ \{r_1,\ldots,r_n\}\leadsto\kw{run}\ \{r_1',\ldots,r_n'\};\ \kw{saturate}\ (\kw{run}\ M_P)}
  \and
  \ir{Saturate}{S\leadsto S'}{\kw{saturate}\ S\leadsto\kw{saturate}\ S'}
  \and
  \ir{Seq}{S_1\leadsto S_1'\\S_2\leadsto S_2'}{S_1;S_2\leadsto S_1';S_2'}
  \and
  \ir{Program}{S\leadsto S'\\Q\leadsto Q'}{(S;\ \kw{check}\ Q)\leadsto(S';\ \kw{check}\ Q')}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def encodeSchedule (P : Program) : Schedule → Nat → Schedule × List RuleOrigin × Nat
  | .run rs, index =>
      let compiled := encodeRules index rs
      let (m, mo) := rebuild P
      (.seq (.run (compiled.map Prod.fst)) m, compiled.map Prod.snd ++ mo, index + rs.length)
  | .saturate S, index =>
      let (S', os, next) := encodeSchedule P S index
      (.saturate S', os, next)
  | .seq S₁ S₂, index =>
      let (T₁, o₁, next) := encodeSchedule P S₁ index
      let (T₂, o₂, last) := encodeSchedule P S₂ next
      (.seq T₁ T₂, o₁ ++ o₂, last)

/-- The congruence pass with origins for later proof resugaring. -/
def compile (P : Program) : Compiled :=
  let (S, os, _) := encodeSchedule P P.schedule 0
  { program := { schedule := S, check := (encodeQuery P.check 0).1 }, origins := os }

/-- The executable program, independent of all proof instrumentation. -/
def encode (P : Program) : Program := (compile P).program

end Egglog.Congruence
