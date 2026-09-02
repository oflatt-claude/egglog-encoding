import EgglogSemantics.Proofs.Step

/-!
# The proof encoding, as a program transformation

M11. `encode : Program → Program` rewrites a source program so that built-in
congruence disappears and every equality is an entry some rule wrote. Designed in
`egglog/src/proofs/proof_encoding.md` and implemented in `egglog/src/proofs/`.

**Parked.** The encoder below is all that survives: the theorems it was written for are
deleted, and `ENCODING.md` records what they said and the two defects that sank them.

The fragment is `PLAN.md`'s: **constructors only, no containers, no delete/subsume,
no schedules**. `Program.EncodeDomain` states it.

## What the encoding does

Three tables per source constructor `f`, plus one union-find for the (single) sort:

| target table | shape | role |
| --- | --- | --- |
| `@UF` | `(t) ↦ (parent, proof)` | `t`'s parent, identity on miss |
| `@fView` | `(children) ↦ (eclass, proof)` | the functional dependency; `:merge` *is* congruence |
| `@fTerm` | `(children, id) ↦ ()` | every application ever built; write-only |

`@UF` and `@fView` share one `:merge` body — keep the smaller side and `set` the
larger's `@UF` edge to it — so a view collision on congruent children unions the two
e-classes and no congruence rule is needed. Both are `.merge` functions, so the encoded
program has **no** constructor table at all: it asserts no equation but the reflexive one
`addTerm` records, so `Cong` on the target is the identity relation on the terms it holds
and congruence there is entirely simulated.

**Every equality the encoding records carries its proof**, in the second value column of
the row that records it. "Proof terms" below is the vocabulary and the reading.

## One deviation forced by the modelled language

**No disequality.** `Pattern` has no `!=`, so the `(!= b c)` guards on path compression
and on the rebuild rule are dropped, and a re-firing re-`set`s a row the table already
holds. `viewDecl` and `ufDecl` declare `identityVals := some 1`, which keeps a row that
differs only in its proof column from counting as a change; that is what stops the
re-firing from becoming a fresh collision.

**One flat rebuild ruleset.** The maintenance rules join `rebuildRuleset` and every encoded
run is followed by `Cmd.saturate rebuildRuleset`. egglog nests three rulesets in a
`run-schedule`; one flat ruleset run to a fixpoint is exactly as strong, since a fixpoint of
a union of rulesets is a fixpoint of each. `Rebuilt` is that command's postcondition
(`saturateReach_rebuilt`), and it is satisfiable: `Spec/Step.lean`'s `MergeConflict` reads
`identityVals`, so the proof column is outside the change test on the specification side too
and a self-collision at `@UF` or a view is not a step. `ENCODING.md`, finding 3, was that it
*was not*, before that repair; `Encoding/Correspond.lean`'s `satProgram_programStep` is the
satisfiability that replaced the refutation.

## Fresh ids

`get-fresh!` has no counterpart in the source semantics, and it cannot be added to the
target *configuration* either: `Database` is fixed, and no `Expr` in the fragment can
depend on a counter. Freshness is instead **structural** — the id minted for `f` over
already-canonical children `cs` is the term `.app f cs`, a skolem id. This is what a
Datalog encoding of `get-fresh!` always does, and it is what the term relation's
`f(children, id)` entry records anyway.

Two consequences, both recorded in `CHECKER.md`:

* Source terms and target ids inhabit one type, so the simulation theorem can compare
  them directly instead of carrying a source-to-target correspondence relation.
* egglog mints a *new* id per construction and lets the view merge dedup them; here the
  second construction of one shape reuses the id, so the merge does not fire. The
  induced equivalence is the same; the entry counts are not.

The id supply that remains is over *variable names*, `@v0`, `@v1`, …, threaded through
`encode` at encode time — egglog's `@pv0`, `@pv1`, ….
-/

namespace Egglog
/-! ### Names -/
/-- The union-find table. The modelled language has one eq-sort, so where egglog emits
`@UF_<Sort>` per sort there is one table here. -/
def ufName : FnName := "@UF"

/-- The ruleset the maintenance rules join, and the one every emitted `Cmd.saturate` runs.

**One flat ruleset, one `saturate`.** egglog's rebuild schedule nests three
(`egglog/src/proofs/proof_encoding.rs:1928-1943`); this is exactly as strong, because a
fixpoint of the union of rulesets is a fixpoint of each, and `Cmd.saturate` runs to a
fixpoint. -/
def rebuildRuleset : RulesetName := "@rebuild"

/-- `f`'s view: the functional dependency `children ↦ (eclass, proof)`. All queries read
it. -/
def viewName (f : FnName) : FnName := "@" ++ f ++ "View"

/-- `f`'s term relation. egglog names it `f`; here `f` is needed as the skolem-id
constructor, so the relation is renamed. Nothing reads it — it exists because proof
extraction does, and because "nothing is ever removed from it" is what lets a proof
mention a term after it leaves the e-graph. -/
def termName (f : FnName) : FnName := "@" ++ f ++ "Term"

/-- The `n`th generated variable. -/
def freshVar (n : Nat) : Var := "@v" ++ toString n

/-! ### The four bundled choices, spelled out

egglog's `ordering-min`, `ordering-max`, `proof-of-min` and `proof-of-max` are one `if`
over one `ordering-gt` each. The names below are egglog's, so the encoder still reads the
way egglog spells it; what they expand to is what the model has to say about them, and
because `ordering-gt` is **strict** a tie takes the `else` branch — visibly, in the term. -/

/-- `(ordering-gt x y)`: egglog's value ordering, `y < x`. -/
def gtE (x y : Expr) : Expr := .app "ordering-gt" [x, y]

/-- `(if c a b)`: strict three-way selection. -/
def ifE (c a b : Expr) : Expr := .app "if" [c, a, b]

/-- `(ordering-max x y)`, egglog's tie-break: `x` when `x > y`, else `y`. -/
def maxE (x y : Expr) : Expr := ifE (gtE x y) x y

/-- `(ordering-min x y)`: `y` when `x > y`, else `x`. -/
def minE (x y : Expr) : Expr := ifE (gtE x y) y x

/-! ### Proof terms

A proof is an **ordinary term**: an application of a declared constructor, built by
`Expr.eval` like every other term the encoding writes.

**A proof term does not carry its proposition** — the row it sits in does. `@UF(t) ↦ (p,
pf)` is `pf : t = p`, and `@fView(c…) ↦ (e, pf)` is `pf : f(c…) = e`; both read key-to-value,
where egglog's view runs the other way (`proof_encoding.md`, "Union-find"). This is a real
simplification over egglog, whose proof nodes carry propositions, and it is available
because the proof is stored *in the table*.

Five heads, which is the subset `CHECKER.md` measured on the constructor-only fragment:

| head | arity | reading |
| --- | --- | --- |
| `@Fiat` | 0 | asserted by a top-level action, or reflexive |
| `@Sym` | 1 | the row's equality reversed |
| `@Trans` | 2 | the two rows' equalities composed |
| `@Congr_k` | k | congruence at a `k`-ary constructor, one proof per child |
| `@Rule_i` | n | source rule `i` fired on `n` premises |

`@Sym`, `@Trans` and `@Congr` are one-to-one with `Cong`'s constructors. Two of the five
are **families indexed at the name**, because the modelled language fixes one arity per
name — a name used at two arities is `Program.arityConflicts`, egglog's "Function already
bound" — and congruence is needed at every source arity. egglog indexes `@Rule_<k>` and
`@Packed_<k>` for the same reason.

`Lit` needs nothing here: a rule's name is *in* its constructor's name rather than in a
`.str` argument, and no proof node carries a literal. Nor is a `.unit` wanted any more —
the term relation carries no output column at all. -/
/-- A proof constructor of arity `k`. Declared, because `Expr.eval` has no rule for an
undeclared name, and a **constructor** rather than egglog's `(… → Unit :no-merge)` relation:
that shape exists to keep two structurally equal proofs from being merged into one, and
with structural freshness a proof node simply *is* its own term. -/
def proofDecl (k : Nat) : FnDecl := { arity := k, outArity := 1, merge := none }

/-- `@Fiat`'s name. -/
def fiatName : FnName := "@Fiat"

/-- `@Sym`'s name. -/
def symName : FnName := "@Sym"

/-- `@Trans`'s name. -/
def transName : FnName := "@Trans"

/-- `(@Fiat)`. -/
def fiatE : Expr := .app fiatName []

/-- `(@Sym p)`. -/
def symE (p : Expr) : Expr := .app symName [p]

/-- `(@Trans p q)`. -/
def transE (p q : Expr) : Expr := .app transName [p, q]

/-- The congruence head at a `k`-ary constructor. -/
def congrName (k : Nat) : FnName := "@Congr_" ++ toString k

/-- `(@Congr_k p₁ … p_k)`, one proof per child. -/
def congrE (ps : List Expr) : Expr := .app (congrName ps.length) ps

/-- The proof head for the `i`th source rule. -/
def ruleName (i : Nat) : FnName := "@Rule_" ++ toString i

/-- `(@Rule_i p₁ … p_n)`, one proof per premise. -/
def ruleE (i : Nat) (ps : List Expr) : Expr := .app (ruleName i) ps

/-! ### Declarations

The `:merge` body shared by `@UF` and every view: keep the smaller side, and `set` the
larger side's union-find edge to it. With two value columns `mergeEnv` binds `old0`/`new0`
for the e-class and `old1`/`new1` for its proof, which is egglog's naming. -/
/-- egglog's `lo_pf`, `(proof-of-min old0 old1 new0 new1)`: the proof paired with the
smaller e-class — `old1` when `new0 > old0`, else `new1`, so a tie keeps `new1`. -/
def loPfE : Expr :=
  ifE (gtE (.var "new0") (.var "old0")) (.var "old1") (.var "new1")

/-- egglog's `hi_pf`, `(proof-of-max old0 old1 new0 new1)`: the proof paired with the larger
e-class — `old1` when `old0 > new0`, else `new1`, so a tie keeps `new1` here too. -/
def hiPfE : Expr :=
  ifE (gtE (.var "old0") (.var "new0")) (.var "old1") (.var "new1")

/-! **The four expansions, evaluated.** `Proofs/Merge.lean`'s `Prim.ifGt_*` prove the
agreement in general; these run the actual expressions in the environment `mergeEnv` builds,
at both strict orders and at a tie. `(A)` is below `(B)` in `Term.blt`, `(P)` is `old1` and
`(Q)` is `new1`, and the signature declares nothing because every head here is a primitive.

Read the tie off the third column: both proof selectors take `(Q)`, the *second* proof, as
egglog's do — `ordering-gt` is strict, so a tie is `false` and the `else` branch wins. -/
private def choiceA : Term := .app "A" []
private def choiceB : Term := .app "B" []
private def choiceP : Term := .app "P" []
private def choiceQ : Term := .app "Q" []

/-- The three orders `Term.blt` distinguishes, as `(old0, new0)` pairs: below, above, tie. -/
private def choiceOrders : List (Term × Term) :=
  [(choiceA, choiceB), (choiceB, choiceA), (choiceA, choiceA)]

/-- One expansion at each of the three orders. -/
private def choiceRun (e : Expr) : List (Option Term) :=
  choiceOrders.map fun o =>
    e.eval (fun _ => none)
      [("old0", o.1), ("old1", choiceP), ("new0", o.2), ("new1", choiceQ)]

section
set_option linter.hashCommand false

-- `ordering-min old0 new0` was `if blt old0 new0 then old0 else new0`.
#guard choiceRun (minE (.var "old0") (.var "new0")) == [choiceA, choiceA, choiceA].map some
-- `ordering-max old0 new0` was `if blt old0 new0 then new0 else old0`.
#guard choiceRun (maxE (.var "old0") (.var "new0")) == [choiceB, choiceB, choiceA].map some
-- `proof-of-min old0 old1 new0 new1` was `if blt old0 new0 then old1 else new1`.
#guard choiceRun loPfE == [choiceP, choiceQ, choiceQ].map some
-- `proof-of-max old0 old1 new0 new1` was `if blt new0 old0 then old1 else new1`.
#guard choiceRun hiPfE == [choiceQ, choiceP, choiceQ].map some

end

/-- The body both `:merge`s run: the larger e-class gets a union-find edge to the smaller,
proved by `@Trans (@Sym hi_pf) lo_pf` — `mx = key` joined to `key = mn`. -/
def mergeBody : List Action :=
  [.set ufName [maxE (.var "old0") (.var "new0")]
    [minE (.var "old0") (.var "new0"), transE (symE hiPfE) loPfE]]

/-- The values both `:merge`s settle on: the smaller e-class, and the proof paired with it
— egglog's `lo_pf` (`ordered_union_merge`, `proof_encoding.rs:634-660`).

Both tables carry a proof whose **left** side is the key term: `@UF(t) ↦ (p, pf)` is
`pf : t = p` and `@fView(c…) ↦ (e, pf)` is `pf : f(c…) = e`. So `lo_pf` already proves what
the surviving row claims, and one composition serves both tables — egglog needs a second
skeleton for its views only because theirs runs the other way.

`identityVals := some 1` on both declarations is what lets the rebuild terminate: the proof
column sits outside the change test, so a collision that moves only the proof resolves to
the resident row. -/
def mergeResult : List Expr := [minE (.var "old0") (.var "new0"), loPfE]

/-- `(function @UF (S) (S @Proof) :merge …)`. A term with no entry is its own
representative, so the lookup is identity on miss — which the model expresses by there
simply being no `@UF(t, p, pf)` term to read. -/
def ufDecl : FnDecl :=
  { arity := 1, outArity := 2, merge := some (.merge mergeBody mergeResult),
    identityVals := some 1 }

/-- `(function @fView (S…) (S @Proof) :merge …)` for a constructor of arity `k`. Two
entries colliding on one key are congruent, and the merge resolves that by unioning
them. -/
def viewDecl (k : Nat) : FnDecl :=
  { arity := k, outArity := 2, merge := some (.merge mergeBody mergeResult),
    identityVals := some 1 }

/-- `(relation @fTerm (S… S))`. Keyed on children *and* id, so distinct constructions
never collide.

**No output column** (`outArity 0`), which is what a relation is. A unit column would put a
literal in the database that no source program built, and `difftest correspond` reports
exactly that as an invented equality — `ViewRepr` classes every literal, and a literal the
target holds and the source does not is in the sweep's term universe. The correspondence is
exact only while the encoding contributes none. -/
def termDecl (k : Nat) : FnDecl :=
  { arity := k + 1, outArity := 0, merge := some .noMerge }

/-- `(constructor f (S…) S)`: the source name, kept as the **skolem-id** constructor.

Declaration is required, so this is a command the prelude has to emit — `.app f es` is
what `encodeBuild` mints an id with, and `Expr.eval` has no rule for an undeclared name.
egglog uses the source name for the *term relation* instead; `termName` is the rename that
frees it. -/
def skolemDecl (k : Nat) : FnDecl :=
  { arity := k, outArity := 1, merge := none }

/-! ### The constructors a program mentions

Read off the syntax rather than off the signature: the source is in the constructor
fragment, so a name's *arity* is only ever visible in its uses, and the prelude needs one
table triple — and one skolem declaration — per name however the source came by it. -/
mutual

/-- The `(name, arity)` pairs an expression applies. -/
def Expr.ctors : Expr → List (FnName × Nat)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args.length) :: Expr.ctorsList args

/-- `Expr.ctors` over an argument list. -/
def Expr.ctorsList : List Expr → List (FnName × Nat)
  | [] => []
  | e :: es => e.ctors ++ Expr.ctorsList es

end

/-- `Expr.ctors` over a pattern. -/
def Pattern.ctors : Pattern → List (FnName × Nat)
  | .expr e => e.ctors
  | .eq e₁ e₂ => e₁.ctors ++ e₂.ctors
  | .values vs _ as => Expr.ctorsList vs ++ Expr.ctorsList as

/-- `Expr.ctors` over an action. A `set`'s own function counts: it names a view. -/
def Action.ctors : Action → List (FnName × Nat)
  | .expr e => e.ctors
  | .letBind _ e => e.ctors
  | .union e₁ e₂ => e₁.ctors ++ e₂.ctors
  | .set f args out => (f, args.length) :: (Expr.ctorsList args ++ Expr.ctorsList out)

/-- `Expr.ctors` over a command. A declaration counts even if nothing applies it. -/
def Cmd.ctors : Cmd → List (FnName × Nat)
  | .action a => a.ctors
  | .rule r => (r.query.flatMap Pattern.ctors) ++ (r.actions.flatMap Action.ctors)
  | .run _ => []
  | .saturate _ => []
  | .decl f d => [(f, d.arity)]

/-- Every function the program mentions, deduplicated. One table triple is emitted per
entry. -/
def Program.ctors (P : Program) : List (FnName × Nat) := (P.flatMap Cmd.ctors).dedup

/-! ### Queries

A source pattern becomes one view read per subterm, joined on e-class variables — the
`check` expansion of `proof_encoding.md`, "Queries". The reads bind ids, so the outer
`(= e₁ e₂)` of a source equality pattern becomes id equality, which is egglog's own
`(= e3 e6)` and is why the rebuild has to have canonicalized the entries first. -/
mutual

/-- Flatten `e` into view reads. Returns the expression naming `e`'s e-class, the reads,
and the next variable number.

A view read is a `Pattern.values` atom, which is what egglog lowers `(= e (@fView c…))` to
and the only form the model admits: `Expr.eval` does not read, so a non-constructor
application is not an expression here. It binds **both** value columns — a read that fixed
the proof column to anything but a fresh variable would match only the rows carrying that
proof — so each read consumes two generated variables, an e-class and a premise proof. -/
def encodeQueryExpr : Expr → Nat → Expr × List Pattern × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .app f args, n =>
      match encodeQueryArgs args n with
      | (es, ps, n₁) =>
          (.var (freshVar n₁),
           ps ++ [.values [.var (freshVar n₁), .var (freshVar (n₁ + 1))] (viewName f) es],
           n₁ + 2)

/-- `encodeQueryExpr` over an argument list. -/
def encodeQueryArgs : List Expr → Nat → List Expr × List Pattern × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeQueryExpr e n with
      | (e', ps, n₁) =>
          match encodeQueryArgs es n₁ with
          | (es', ps', n₂) => (e' :: es', ps ++ ps', n₂)

end

/-- Encode one source pattern. `.expr e` is "`e` is present", which the reads already
say; `.eq` adds the id equality. -/
def encodePattern : Pattern → Nat → List Pattern × Nat
  | .values vs f as, n => ([.values vs f as], n)
  | .expr e, n => match encodeQueryExpr e n with | (_, ps, n₁) => (ps, n₁)
  | .eq e₁ e₂, n =>
      match encodeQueryExpr e₁ n with
      | (x₁, ps₁, n₁) =>
          match encodeQueryExpr e₂ n₁ with
          | (x₂, ps₂, n₂) => (ps₁ ++ ps₂ ++ [.eq x₁ x₂], n₂)

/-- `encodePattern` over a query. -/
def encodeQuery : Query → Nat → Query × Nat
  | [], n => ([], n)
  | p :: ps, n =>
      match encodePattern p n with
      | (qs, n₁) => match encodeQuery ps n₁ with | (qs', n₂) => (qs ++ qs', n₂)

/-- The premise proofs an encoded query binds: the second value column of every view read,
in query order. This is `@Rule_i`'s argument list, and its length is `@Rule_i`'s arity.

Read back off the emitted query rather than threaded out of `encodeQueryExpr`, which is
sound because a two-column read atom in an encoded query is one this file wrote: under
`Program.EncodeDomain` the source has no `Pattern.values` at all. -/
def queryProofs (q : Query) : List Expr :=
  q.filterMap fun p => match p with
    | .values [_, pf] _ _ => some pf
    | _ => none

/-- `@Rule_i`'s arity: how many premises rule `r`'s encoded query reads. Independent of the
variable supply the encoding is at, so the prelude's declaration and the head's application
agree. -/
def ruleProofArity (r : Rule) : Nat := (queryProofs (encodeQuery r.query 0).1).length

/-! ### Building a term

`proof_encoding.md`, "Building a term": mint an id, write the term-relation entry, intern
the application into its view, and read back the view's e-class. A parent is built over
its children's canonical ids, which is what keeps views canonical.

egglog interns with `set-if-empty-<View>!`, which returns the *existing* e-class when
the shape was already there and **discards** the id it just minted. There is no such
action here, so the encoding `set`s and then reads the view back. The difference is one
extra union: where egglog drops the minted id, the plain `set` collides with the
existing entry and the view's `:merge` unions the two. Both terms denote the same
application, so the equalities are the same and only the entry count differs.

**The read-back is a shape egglog rejects, and this is the reason `set-if-empty` exists.**
`(let x (@fView c…))` in a rule head is a lookup, and
`check_no_function_lookups_in_actions` refuses one: "Value lookup of non-constructor
function function in rule is disallowed". egglog gets around it by registering
`set-if-empty-<View>!` as a **primitive** (`src/proofs/proof_fresh.rs`), and
`expr_has_function_lookup` flags only `ResolvedCall::Func`. So `encode` as written emits
rule heads the real system would refuse, and `Impl/Check.lean`'s `Program.noLookup` is the
transcribed check that rejects them. The fix is the same one egglog made — a `Prim`-style
get-or-insert, which is a write and not a read — and it is M11 work, so it is recorded
here rather than done. Nothing downstream depends on the read-back stepping — the
theorems that would have are deleted (`ENCODING.md`). -/
mutual

/-- Build `e` in the target. Returns the expression naming `e`'s e-class, the actions
that create it, and the next variable number.

**The skolem is the answer; nothing is read back.** `.app f es` names the class as well as
any member does, because equality on the target is what `@UF` records and every reader
goes through `UFLeader`. egglog reads its view back to return the *canonical* member — an
optimization, and the reason it needs `set-if-empty` as a primitive, since
`(let x (@fView c…))` is a lookup its own
`check_no_function_lookups_in_actions` refuses. Skipping it costs the rebuild more
re-keying and buys a head with no read in it at all.

**The view entry's proof is `@Fiat`**, whatever context the build is in: with a structural
id the entry a construction writes is `f(c…) = f(c…)`, and reflexivity is what `@Fiat`
proves when its two sides coincide. Only an equality between *distinct* terms — a `union`
head — needs the firing's own justification. -/
def encodeBuild : Expr → Nat → Expr × List Action × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .app f args, n =>
      match encodeBuildArgs args n with
      | (es, as, n₁) =>
          (.app f es,
           as ++ [.set (termName f) (es ++ [.app f es]) [],
                  .set (viewName f) es [.app f es, fiatE]],
           n₁)

/-- `encodeBuild` over an argument list. -/
def encodeBuildArgs : List Expr → Nat → List Expr × List Action × Nat
  | [], n => ([], [], n)
  | e :: es, n =>
      match encodeBuild e n with
      | (e', as, n₁) =>
          match encodeBuildArgs es n₁ with
          | (es', as', n₂) => (e' :: es', as ++ as', n₂)

end

/-! ### Heads

A `union` becomes one `@UF` edge from the larger endpoint to the smaller. egglog's
construct-into optimization — building a freshly constructed operand directly into the
other operand's e-class, dropping the union — is deliberately **not** modelled: its
stated effect is "exactly the edge the explicit union would have produced"
(`proof_encoding.md`, "Union in a rule"), so it changes which entries are written and not
which equalities hold. -/
/-- Encode one head action, under the justification `pf` for the equalities it asserts:
`@Fiat` at top level, and the firing's `@Rule_i` inside a rule.

The two writes that need it are `union` and `set`, which are the two that can relate
distinct terms. A build needs nothing from the context (`encodeBuild`). Direction does not:
a `union` contributes its pair *both ways* to the propositions of the action it comes from,
so the edge is justified whichever endpoint `ordering-max` picks. -/
def encodeAction (pf : Expr) : Action → Nat → List Action × Nat
  | .expr e, n => match encodeBuild e n with | (_, as, n₁) => (as, n₁)
  | .letBind v e, n =>
      match encodeBuild e n with | (x, as, n₁) => (as ++ [.letBind v x], n₁)
  | .union e₁ e₂, n =>
      match encodeBuild e₁ n with
      | (x₁, as₁, n₁) =>
          match encodeBuild e₂ n₁ with
          | (x₂, as₂, n₂) =>
              (as₁ ++ as₂ ++ [.set ufName [maxE x₁ x₂] [minE x₁ x₂, pf]], n₂)
  | .set f args out, n =>
      match encodeBuildArgs args n with
      | (es, as, n₁) =>
          match encodeBuildArgs out n₁ with
          | (xs, as', n₂) => (as ++ as' ++ [.set (viewName f) es (xs ++ [pf])], n₂)

/-- `encodeAction` over an action list, all under one justification. -/
def encodeActions (pf : Expr) : List Action → Nat → List Action × Nat
  | [], n => ([], n)
  | a :: as, n =>
      match encodeAction pf a n with
      | (bs, n₁) => match encodeActions pf as n₁ with | (bs', n₂) => (bs ++ bs', n₂)

/-- Encode the `i`th rule: view reads for the body, builds and `@UF` edges for the head,
and `(@Rule_i p…)` over the premises' proofs as the head's justification.

The premise proofs are exactly the proof variables the query's view reads bind, so the
justification is assembled out of what the match already delivers and the head reads
nothing. -/
def encodeRule (i : Nat) (r : Rule) (n : Nat) : Rule × Nat :=
  match encodeQuery r.query n with
  | (q, n₁) =>
      match encodeActions (ruleE i (queryProofs q)) r.actions n₁ with
      | (as, n₂) => ({ query := q, actions := as, ruleset := r.ruleset }, n₂)

/-! ### Maintenance

`proof_encoding.md`, "Rebuilding". Two families, both ordinary rules. -/
/-- Path compression, `a → b → c` to `a → c`, the new edge proved by composing the two it
walked. egglog guards it with `(!= b c)`; without disequality the unguarded rule
additionally re-`set`s edges it already holds, whose proof column the merge then settles.

This is the one site that writes a bare `@Trans`, which is what `--proofs` on a
constructor-only program emits too (`CHECKER.md`, "The minimal subset"). -/
def pathCompressRule : Rule :=
  { query := [.values [.var "@b", .var "@p"] ufName [.var "@a"],
              .values [.var "@c", .var "@q"] ufName [.var "@b"]],
    actions := [.set ufName [.var "@a"] [.var "@c", transE (.var "@p") (.var "@q")]],
    ruleset := rebuildRuleset }

/-- `@c0 … @c(k-1)`, a rebuild rule's column variables. -/
def rebuildVars (k : Nat) : List Expr :=
  (List.range k).map fun i => .var ("@c" ++ toString i)

/-- The child proofs of a congruence step that moves column `i` of a `k`-ary constructor:
the `@UF` edge's proof there, and reflexivity — `@Fiat` at equal sides — everywhere else.
egglog spells the same thing `@UF_<Sort>_canon_proof`, "reflexive for a column that did not
move". -/
def congrChildren (k i : Nat) : List Expr :=
  (List.range k).map fun j => if j = i then .var "@q" else fiatE

/-- The rebuild rules for a constructor of arity `k`: one per child column, moving that
column to its union-find leader, and one for the e-class column.

egglog emits **one** rule per eq-sort occurring in the view, not one per column: its
body joins a `@UF` delta against the rebuild index, and its action re-canonicalizes
every column at once through `@UF_<Sort>_canon` (identity on miss) before deleting the
stale entry. Neither piece is available here — there is no index, no `delete`, and no
identity-on-miss read, since "no entry" is not a matchable fact. Neither is needed for
the equalities: entries are never removed in this model, so a half-rewritten entry is an
extra entry rather than a lost one, and `Database.Out` reads any of them. What egglog
buys with the one-firing form is entry count.

**Each re-keyed entry carries the proof of what it now claims.** With `@p : f(c…) = @e` and
`@q` the `@UF` edge's proof, moving the e-class composes on the left, `(@Trans @p @q) :
f(c…) = @x`; moving column `i` composes a congruence step on the right, `(@Trans (@Sym
(@Congr_k … @q …)) @p) : f(c… @x …) = @e`. That the e-class step is a `@Trans` and not a
`@Congr` child is egglog's split too — "an e-class can equal one of its own children's
terms". -/
def rebuildRules (f : FnName) (k : Nat) : List Rule :=
  let cs := rebuildVars k
  let view : Pattern := .values [.var "@e", .var "@p"] (viewName f) cs
  let eclassRule : Rule :=
    { query := [view, .values [.var "@x", .var "@q"] ufName [.var "@e"]],
      actions := [.set (viewName f) cs [.var "@x", transE (.var "@p") (.var "@q")]],
      ruleset := rebuildRuleset }
  eclassRule :: (List.range k).map fun i =>
    { query := [view, .values [.var "@x", .var "@q"] ufName [.var ("@c" ++ toString i)]],
      actions := [.set (viewName f) (cs.set i (.var "@x"))
        [.var "@e", transE (symE (congrE (congrChildren k i))) (.var "@p")]],
      ruleset := rebuildRuleset }

/-- Every maintenance rule the encoding of `P` emits. `Rebuilt` is stated over it. -/
def maintenanceRules (P : Program) : List Rule :=
  pathCompressRule :: P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-! ### The transformation -/
/-- The source rules, in the order `encodeCmds` numbers them. -/
def Program.srcRules (P : Program) : List Rule :=
  P.filterMap fun c => match c with | .rule r => some r | _ => none

/-- The arities congruence is needed at: one `@Congr_k` per source constructor arity, and
none at 0 — a nullary constructor has no child column for a rebuild rule to move. -/
def congrArities (P : Program) : List Nat := (P.ctors.map Prod.snd).dedup.filter (· ≠ 0)

/-- `(constructor @Rule_i (@Proof…) @Proof)` per source rule, at the arity that rule's
encoded query reads. -/
def ruleProofDecls : List Rule → Nat → Program
  | [], _ => []
  | r :: rs, i => .decl (ruleName i) (proofDecl (ruleProofArity r)) :: ruleProofDecls rs (i + 1)

/-- The proof vocabulary: three fixed heads and the two arity-indexed families.

**First in the prelude**, because a declaration's `:merge` body and a rule's head are
checked and evaluated against the signature standing when they are read, and both apply
these. -/
def proofDecls (P : Program) : Program :=
  [.decl fiatName (proofDecl 0), .decl symName (proofDecl 1), .decl transName (proofDecl 2)] ++
    (congrArities P).map (fun k => .decl (congrName k) (proofDecl k)) ++
    ruleProofDecls P.srcRules 0

/-- The declarations and maintenance rules, emitted once at the top. -/
def encodePrelude (P : Program) : Program :=
  proofDecls P ++ .decl ufName ufDecl ::
    (P.ctors.flatMap fun fk =>
      [.decl fk.1 (skolemDecl fk.2), .decl (viewName fk.1) (viewDecl fk.2),
       .decl (termName fk.1) (termDecl fk.2)]) ++
    (maintenanceRules P).map .rule

/-- Encode one command. A source declaration is dropped: the prelude has already declared
its function as the skolem-id constructor and emitted its table triple, and re-emitting it
would be a redeclaration (`Cmd.DeclFresh`).

**Every command that writes is followed by a rebuild**, which is where egglog puts it —
after each one except a function, rule or sort declaration
(`egglog/src/proofs/proof_encoding.rs:1655-1662`). A top-level action writes, so a `union`
there creates congruence the views must be re-keyed for; without the rebuild it propagates
only to the columns the union names directly, and `Wrapper(Add One Two)`,
`Wrapper(Add Two One)`, `union One Two` leaves `Wrapper` as two classes where the source
has one. A declaration writes nothing and a rule only registers itself.

Two supplies are threaded: `n` numbers generated variables, and `i` numbers the rules, so
that the `@Rule_i` a head names is the one the prelude declared for it. -/
def encodeCmd : Cmd → Nat → Nat → Program × Nat × Nat
  | .action a, n, i =>
      match encodeAction fiatE a n with
      | (as, n₁) => (as.map .action ++ [.saturate rebuildRuleset], n₁, i)
  | .rule r, n, i => match encodeRule i r n with | (r', n₁) => ([.rule r'], n₁, i + 1)
  | .run R, n, i => ([.run R, .saturate rebuildRuleset], n, i)
  | .saturate R, n, i => ([.saturate R, .saturate rebuildRuleset], n, i)
  | .decl _ _, n, i => ([], n, i)

/-- `encodeCmd` over a program. -/
def encodeCmds : Program → Nat → Nat → Program × Nat × Nat
  | [], n, i => ([], n, i)
  | c :: cs, n, i =>
      match encodeCmd c n i with
      | (p, n₁, i₁) => match encodeCmds cs n₁ i₁ with | (p', n₂, i₂) => (p ++ p', n₂, i₂)

/-- **The encoding.** -/
def encode (P : Program) : Program := encodePrelude P ++ (encodeCmds P 0 0).1

/-! ### The encoded program asserts no equation

`Proofs/Merge.lean`'s two `Recorded` transports need `Database.Diag` or
`Signature.OrderingFree`, and `execM_contained` is proved under `Program.UnionFree`. That is
the arm `encode` lands in: a source `union` becomes `.set @UF [ordering-max …] [ordering-min
…, pf]`, so no `Action.union` survives, while `ordering-max` inside a rule action is exactly
what an ordering-free hypothesis forbids. `Proofs/Counterexamples.lean`'s
`transport_recorded_false` is what the hypothesis costs when neither arm is available.

The shape equations below hold by `rfl` — each `encode*` function destructures a tuple its
recursive call returns, and projection is definitional. -/

theorem Actions.unionFree_of_mem {as : List Action} (h : ∀ a ∈ as, a.UnionFree) :
    Actions.UnionFree as := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

theorem Program.unionFree_of_mem {p : Program} (h : ∀ c ∈ p, Cmd.UnionFree c) :
    Program.UnionFree p := by
  induction p with
  | nil => trivial
  | cons c cs ih => exact ⟨h c (by simp), ih fun d hd => h d (by simp [hd])⟩

/-- A declaration with no `:merge` runs nothing. -/
theorem unionFree_decl_none {f : FnName} {d : FnDecl} (h : d.merge = none) :
    Cmd.UnionFree (.decl f d) := by
  change d.UnionFree
  intro ms hms
  rw [h] at hms
  exact absurd hms (by simp)

/-- A declaration whose `:merge` body is `mergeBody`, which is one `set`. -/
theorem unionFree_decl_merge {f : FnName} {d : FnDecl} {res : List Expr}
    (h : d.merge = some (.merge mergeBody res)) : Cmd.UnionFree (.decl f d) := by
  change d.UnionFree
  intro ms hms
  rw [h] at hms
  obtain rfl := Option.some.inj hms
  exact ⟨trivial, trivial⟩

/-- A `:no-merge` declaration runs nothing either. -/
theorem unionFree_decl_noMerge {f : FnName} {d : FnDecl} (h : d.merge = some .noMerge) :
    Cmd.UnionFree (.decl f d) := by
  change d.UnionFree
  intro ms hms
  rw [h] at hms
  obtain rfl := Option.some.inj hms
  trivial

theorem encodeBuild_app_actions (f : FnName) (args : List Expr) (n : Nat) :
    (encodeBuild (.app f args) n).2.1
      = (encodeBuildArgs args n).2.1 ++
        [.set (termName f)
            ((encodeBuildArgs args n).1 ++ [.app f (encodeBuildArgs args n).1]) [],
         .set (viewName f) (encodeBuildArgs args n).1
            [.app f (encodeBuildArgs args n).1, fiatE]] := rfl

theorem encodeBuildArgs_cons_actions (e : Expr) (es : List Expr) (n : Nat) :
    (encodeBuildArgs (e :: es) n).2.1
      = (encodeBuild e n).2.1 ++ (encodeBuildArgs es (encodeBuild e n).2.2).2.1 := rfl

/-! ### The naming expression is the source expression

`encodeBuild` returns `.app f es` where `es` are the arguments' own naming expressions, and a
leaf unchanged — so by induction the expression it hands back is the one it was given, and the
counter it hands back is the one it was given too. "The skolem is the answer" is *this*: a head
build reads nothing and renames nothing, so the entry it writes is keyed on the source
argument expressions and valued at the source expression. What makes the two evaluate to the
same term is that the target declares every source constructor as its skolem
(`skolemDecl`), which is a fact about the two signatures and not about the encoder.
-/

mutual

/-- **A build's naming expression is the expression itself.** -/
theorem encodeBuild_fst : ∀ (e : Expr) (n : Nat), (encodeBuild e n).1 = e
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .app f args, n => by
      change Expr.app f (encodeBuildArgs args n).1 = _
      rw [encodeBuildArgs_fst]

@[inherit_doc encodeBuild_fst]
theorem encodeBuildArgs_fst : ∀ (es : List Expr) (n : Nat), (encodeBuildArgs es n).1 = es
  | [], _ => rfl
  | e :: es, n => by
      change (encodeBuild e n).1 :: (encodeBuildArgs es (encodeBuild e n).2.2).1 = _
      rw [encodeBuild_fst, encodeBuildArgs_fst]

end

mutual

/-- **A build consumes no fresh variables.** It emits `set`s over expressions it already has,
so the counter passes through; only `encodeQuery` advances it. -/
theorem encodeBuild_snd_snd : ∀ (e : Expr) (n : Nat), (encodeBuild e n).2.2 = n
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .app _ args, n => by
      change (encodeBuildArgs args n).2.2 = _
      rw [encodeBuildArgs_snd_snd]

@[inherit_doc encodeBuild_snd_snd]
theorem encodeBuildArgs_snd_snd : ∀ (es : List Expr) (n : Nat), (encodeBuildArgs es n).2.2 = n
  | [], _ => rfl
  | e :: es, n => by
      change (encodeBuildArgs es (encodeBuild e n).2.2).2.2 = _
      rw [encodeBuildArgs_snd_snd, encodeBuild_snd_snd]

end

/-- **A build's entry is keyed on the source argument expressions and valued at the source
expression.** `encodeBuild_app_actions` with `encodeBuildArgs_fst` applied, which is the form
a read-back consumes. -/
theorem encodeBuild_app_actions_eq (f : FnName) (args : List Expr) (n : Nat) :
    (encodeBuild (.app f args) n).2.1
      = (encodeBuildArgs args n).2.1 ++
        [.set (termName f) (args ++ [.app f args]) [],
         .set (viewName f) args [.app f args, fiatE]] := by
  rw [encodeBuild_app_actions, encodeBuildArgs_fst]

mutual

/-- A build emits `set`s and nothing else. -/
theorem encodeBuild_unionFree : ∀ (e : Expr) (n : Nat),
    ∀ a ∈ (encodeBuild e n).2.1, a.UnionFree
  | .lit _, _ => by simp [encodeBuild]
  | .var _, _ => by simp [encodeBuild]
  | .app f args, n => by
      intro a ha
      rw [encodeBuild_app_actions] at ha
      rcases List.mem_append.mp ha with h | h
      · exact encodeBuildArgs_unionFree args n a h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> trivial

@[inherit_doc encodeBuild_unionFree]
theorem encodeBuildArgs_unionFree : ∀ (es : List Expr) (n : Nat),
    ∀ a ∈ (encodeBuildArgs es n).2.1, a.UnionFree
  | [], _ => by simp [encodeBuildArgs]
  | e :: es, n => by
      intro a ha
      rw [encodeBuildArgs_cons_actions] at ha
      rcases List.mem_append.mp ha with h | h
      · exact encodeBuild_unionFree e n a h
      · exact encodeBuildArgs_unionFree es _ a h

end

theorem encodeAction_expr_actions (pf : Expr) (e : Expr) (n : Nat) :
    (encodeAction pf (.expr e) n).1 = (encodeBuild e n).2.1 := rfl

theorem encodeAction_letBind_actions (pf : Expr) (v : Var) (e : Expr) (n : Nat) :
    (encodeAction pf (.letBind v e) n).1
      = (encodeBuild e n).2.1 ++ [.letBind v (encodeBuild e n).1] := rfl

theorem encodeAction_union_actions (pf : Expr) (e₁ e₂ : Expr) (n : Nat) :
    (encodeAction pf (.union e₁ e₂) n).1
      = (encodeBuild e₁ n).2.1 ++ (encodeBuild e₂ (encodeBuild e₁ n).2.2).2.1 ++
        [.set ufName [maxE (encodeBuild e₁ n).1 (encodeBuild e₂ (encodeBuild e₁ n).2.2).1]
          [minE (encodeBuild e₁ n).1 (encodeBuild e₂ (encodeBuild e₁ n).2.2).1, pf]] := rfl

theorem encodeAction_set_actions (pf : Expr) (f : FnName) (args out : List Expr) (n : Nat) :
    (encodeAction pf (.set f args out) n).1
      = (encodeBuildArgs args n).2.1 ++
        (encodeBuildArgs out (encodeBuildArgs args n).2.2).2.1 ++
        [.set (viewName f) (encodeBuildArgs args n).1
          ((encodeBuildArgs out (encodeBuildArgs args n).2.2).1 ++ [pf])] := rfl

theorem encodeActions_cons_actions (pf : Expr) (a : Action) (as : List Action) (n : Nat) :
    (encodeActions pf (a :: as) n).1
      = (encodeAction pf a n).1 ++ (encodeActions pf as (encodeAction pf a n).2).1 := rfl

/-- **A source `union` becomes a `set`.** This is the case the whole statement rests on. -/
theorem encodeAction_unionFree (pf : Expr) : ∀ (a : Action) (n : Nat),
    ∀ b ∈ (encodeAction pf a n).1, b.UnionFree := by
  rintro (e | ⟨v, e⟩ | ⟨e₁, e₂⟩ | ⟨f, args, out⟩) n b hb
  · exact encodeBuild_unionFree e n b (encodeAction_expr_actions .. ▸ hb)
  · rw [encodeAction_letBind_actions] at hb
    rcases List.mem_append.mp hb with h | h
    · exact encodeBuild_unionFree e n b h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl; trivial
  · rw [encodeAction_union_actions] at hb
    rcases List.mem_append.mp hb with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact encodeBuild_unionFree e₁ n b h'
      · exact encodeBuild_unionFree e₂ _ b h'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl; trivial
  · rw [encodeAction_set_actions] at hb
    rcases List.mem_append.mp hb with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact encodeBuildArgs_unionFree args n b h'
      · exact encodeBuildArgs_unionFree out _ b h'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl; trivial

@[inherit_doc encodeAction_unionFree]
theorem encodeActions_unionFree (pf : Expr) : ∀ (as : List Action) (n : Nat),
    ∀ b ∈ (encodeActions pf as n).1, b.UnionFree
  | [], _ => by simp [encodeActions]
  | a :: as, n => by
      intro b hb
      rw [encodeActions_cons_actions] at hb
      rcases List.mem_append.mp hb with h | h
      · exact encodeAction_unionFree pf a n b h
      · exact encodeActions_unionFree pf as _ b h

/-- Every maintenance rule's head is one `set`. -/
theorem rebuildRules_unionFree (f : FnName) (k : Nat) :
    ∀ r ∈ rebuildRules f k, Actions.UnionFree r.actions := by
  intro r hr
  simp only [rebuildRules, List.mem_cons, List.mem_map, List.mem_range] at hr
  rcases hr with rfl | ⟨i, -, rfl⟩ <;> exact ⟨trivial, trivial⟩

@[inherit_doc rebuildRules_unionFree]
theorem maintenanceRules_unionFree (P : Program) :
    ∀ r ∈ maintenanceRules P, Actions.UnionFree r.actions := by
  intro r hr
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hr
  rcases hr with rfl | ⟨fk, -, hmem⟩
  · exact ⟨trivial, trivial⟩
  · exact rebuildRules_unionFree fk.1 fk.2 r hmem

theorem ruleProofDecls_unionFree : ∀ (rs : List Rule) (i : Nat),
    ∀ c ∈ ruleProofDecls rs i, Cmd.UnionFree c
  | [], _ => by simp [ruleProofDecls]
  | r :: rs, i => by
      intro c hc
      rw [ruleProofDecls] at hc
      rcases List.mem_cons.mp hc with rfl | h
      · exact unionFree_decl_none rfl
      · exact ruleProofDecls_unionFree rs (i + 1) c h

/-- The prelude is declarations and maintenance rules, and every one of them is union-free:
the proof and skolem heads are constructors, `@UF` and the views share `mergeBody`, the term
relations are `:no-merge`. -/
theorem encodePrelude_unionFree (P : Program) : ∀ c ∈ encodePrelude P, Cmd.UnionFree c := by
  intro c hc
  simp only [encodePrelude, proofDecls, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_flatMap, List.not_mem_nil, or_false] at hc
  rcases hc with ((((rfl | rfl | rfl) | ⟨k, -, rfl⟩) | h) | rfl | ⟨fk, -, (rfl | rfl | rfl)⟩) |
      ⟨r, hr, rfl⟩
  · exact unionFree_decl_none rfl
  · exact unionFree_decl_none rfl
  · exact unionFree_decl_none rfl
  · exact unionFree_decl_none rfl
  · exact ruleProofDecls_unionFree _ 0 c h
  · exact unionFree_decl_merge rfl
  · exact unionFree_decl_none rfl
  · exact unionFree_decl_merge rfl
  · exact unionFree_decl_noMerge rfl
  · exact maintenanceRules_unionFree P r hr

theorem encodeRule_actions (i : Nat) (r : Rule) (n : Nat) :
    (encodeRule i r n).1.actions
      = (encodeActions (ruleE i (queryProofs (encodeQuery r.query n).1)) r.actions
          (encodeQuery r.query n).2).1 := rfl

theorem encodeCmd_action_fst (a : Action) (n i : Nat) :
    (encodeCmd (.action a) n i).1
      = (encodeAction fiatE a n).1.map .action ++ [.saturate rebuildRuleset] := rfl

theorem encodeCmd_rule_fst (r : Rule) (n i : Nat) :
    (encodeCmd (.rule r) n i).1 = [.rule (encodeRule i r n).1] := rfl

theorem encodeCmds_cons_fst (c : Cmd) (cs : Program) (n i : Nat) :
    (encodeCmds (c :: cs) n i).1
      = (encodeCmd c n i).1 ++
        (encodeCmds cs (encodeCmd c n i).2.1 (encodeCmd c n i).2.2).1 := rfl

/-- Every command the encoding of one source command emits is union-free. -/
theorem encodeCmd_unionFree (c : Cmd) (n i : Nat) :
    ∀ d ∈ (encodeCmd c n i).1, Cmd.UnionFree d := by
  cases c with
  | action a =>
    intro d hd
    rw [encodeCmd_action_fst] at hd
    rcases List.mem_append.mp hd with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      exact encodeAction_unionFree fiatE a n b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl; trivial
  | rule r =>
    intro d hd
    rw [encodeCmd_rule_fst] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl
    change Actions.UnionFree (encodeRule i r n).1.actions
    rw [encodeRule_actions]
    exact Actions.unionFree_of_mem (encodeActions_unionFree _ r.actions _)
  | run R =>
    intro d hd
    simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> trivial
  | saturate R =>
    intro d hd
    simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> trivial
  | decl f dd => intro d hd; simp [encodeCmd] at hd

@[inherit_doc encodeCmd_unionFree]
theorem encodeCmds_unionFree : ∀ (P : Program) (n i : Nat),
    ∀ d ∈ (encodeCmds P n i).1, Cmd.UnionFree d
  | [], _, _ => by simp [encodeCmds]
  | c :: cs, n, i => by
      intro d hd
      rw [encodeCmds_cons_fst] at hd
      rcases List.mem_append.mp hd with h | h
      · exact encodeCmd_unionFree c n i d h
      · exact encodeCmds_unionFree cs _ _ d h

/-- **`encode`'s output is union-free**, for every source program. -/
theorem encode_unionFree (P : Program) : Program.UnionFree (encode P) := by
  refine Program.unionFree_of_mem fun c hc => ?_
  rw [encode] at hc
  rcases List.mem_append.mp hc with h | h
  · exact encodePrelude_unionFree P c h
  · exact encodeCmds_unionFree P 0 0 c h

/-! ### The source programs `encode` is defined for

`PLAN.md`'s fragment. `MERGE.md`, "Restrictions on `encode`'s domain", records the one
restriction that is permanent rather than a gap: egglog refuses to encode a function
with a `:merge` action block. -/
/-- No `set` action. `Action.set` is what a `:merge` function and an encoded rule head
need; the constructor fragment has neither. **Not a domain clause**: under
`EncodeDomain.ctorsOnly` a `set` could only name a constructor or an undeclared function,
which is exactly what `Spec/Scope.lean`'s `Action.SetLegal` refuses. So the domain states
`Program.SetLegal` and `Program.setLegal_iff_noSet` records that the two are one
condition. -/
def Action.NoSet : Action → Prop
  | .set _ _ _ => False
  | _ => True

/-- No entry atom. `Pattern.values` reads an entry of a non-constructor function, which
the constructor fragment has none of — so like `Action.NoSet` this is a fragment
restriction rather than a limitation, and it is why `encodePattern` leaves the case alone
instead of encoding it. The encoding's *own* queries are all entry atoms; this constrains
the source, and `EncodeDomain.queryEncodable` is where it is asked. -/
def Pattern.NoValues : Pattern → Prop
  | .values _ _ _ => False
  | _ => True

/-- `Action.NoSet` at every action a command runs. -/
def Cmd.NoSet : Cmd → Prop
  | .action a => a.NoSet
  | .rule r => ∀ a ∈ r.actions, a.NoSet
  | _ => True

/-- The signature a constructor declaration installs declares constructors only. -/
theorem Signature.allConstructors_sigBind {sig : Signature} (hsig : sig.AllConstructors)
    {c : Cmd} (hc : c.CtorDecl) : (c.sigBind sig).AllConstructors := by
  cases c with
  | decl f d =>
      intro g
      by_cases h : g = f
      · subst h
        rw [Cmd.sigBind, Signature.mergeOf, Function.update_self]
        exact hc
      · rw [Cmd.sigBind, Signature.mergeOf, Function.update_of_ne h]
        exact hsig g
  | _ => exact hsig

/-- `Action.SetLegal` at a state that declares constructors only **is** `Action.NoSet`: a
`set` head has to be a `:merge` or `:no-merge` function, and there are none. -/
theorem Cmd.setLegal_iff_noSet {sig : Signature} (hsig : sig.AllConstructors) (c : Cmd) :
    c.SetLegal sig ↔ c.NoSet := by
  have hact : ∀ a : Action, a.SetLegal sig ↔ a.NoSet := by
    intro a
    cases a <;> simp [Action.SetLegal, Action.NoSet, hsig _]
  have hacts : ∀ as : List Action, Actions.SetLegal as sig ↔ ∀ a ∈ as, a.NoSet := by
    intro as
    induction as with
    | nil => simp
    | cons a as ih => simp [hact a, ih]
  cases c <;> simp [Cmd.NoSet, hact, hacts]

/-- **`Spec/Scope.lean`'s `set` legality *is* the domain's "no `set` anywhere".** The
equivalence the `setLegal` clause is stated on: one direction is that a non-`set` action is
vacuously legal, the other that `Program.CtorDecls` leaves no merge function for a `set` to
name. -/
theorem Program.setLegal_iff_noSet : ∀ {P : Program} {sig : Signature}, sig.AllConstructors →
    P.CtorDecls → (Program.SetLegal P sig ↔ ∀ c ∈ P, c.NoSet)
  | [], _, _, _ => by simp
  | c :: cs, sig, hsig, hctor => by
      have hc : c.CtorDecl := hctor c (List.mem_cons_self ..)
      have htail : Program.CtorDecls cs := fun c' hc' => hctor c' (List.mem_cons_of_mem _ hc')
      rw [Program.SetLegal, Cmd.setLegal_iff_noSet hsig c,
        Program.setLegal_iff_noSet (Signature.allConstructors_sigBind hsig hc) htail]
      simp

/-- The variables a pattern mentions. -/
def Pattern.varsOf : Pattern → List Var := Pattern.vars

/-- The variables an action mentions, binders included. -/
def Action.vars : Action → List Var
  | .expr e => e.vars
  | .letBind v e => v :: e.vars
  | .union e₁ e₂ => e₁.vars ∪ e₂.vars
  | .set _ args out => Expr.varsList args ∪ Expr.varsList out

/-- `Action.vars` over a command. -/
def Cmd.vars : Cmd → List Var
  | .action a => a.vars
  | .rule r => r.query.vars ∪ (r.actions.flatMap Action.vars)
  | .run _ => []
  | .saturate _ => []
  | .decl _ _ => []

/-- Every variable the program mentions. -/
def Program.vars (P : Program) : List Var := (P.flatMap Cmd.vars).dedup

/-- The ruleset names a command mentions: the one a rule joins, and the one a run fires. -/
def Cmd.rulesets : Cmd → List RulesetName
  | .rule r => [r.ruleset]
  | .run R => [R]
  | .saturate R => [R]
  | .action _ => []
  | .decl _ _ => []

/-- Every ruleset name the program mentions. -/
def Program.rulesets (P : Program) : List RulesetName := (P.flatMap Cmd.rulesets).dedup

/-- **Every name the source text mentions**, of the three kinds the generated namespace has
to stay clear of: a function name, a variable, a ruleset. One list because one condition is
asked of all three (`EncodeDomain.noAt`). -/
def Program.names (P : Program) : List String :=
  P.ctors.map Prod.fst ++ P.vars ++ P.rulesets

/-! ### What the query flattening drops

`encodeQueryExpr` flattens an *application* and returns a leaf unchanged, so `encodePattern`
emits **no atom** for a source pattern whose expression is a bare literal or a bare variable.
Both are conditions on the source program's **text**, decidable, and both are folded into
`Program.EncodeDomain` below; `Encoding/Match.lean` is where each is consumed and where each
is refuted. -/
/-- **The pattern has a witness position.** `Matches` asks for a term the source *holds*
congruent to the instance, and a bare literal has none: the source may never have built it,
and `encodePattern` emits no atom that would say it did. -/
def Pattern.Grounded : Pattern → Prop
  | .expr e => ∀ l, e ≠ .lit l
  | .eq e₁ e₂ => (∀ l, e₁ ≠ .lit l) ∨ (∀ l, e₂ ≠ .lit l)
  | .values _ _ _ => True

mutual

/-- The variable occurs as an **argument of an application**: a key column of one of the view
reads `encodeQueryExpr` emits. -/
def Expr.ArgVar (v : Var) : Expr → Prop
  | .lit _ => False
  | .var _ => False
  | .app _ args => Expr.var v ∈ args ∨ Expr.ArgVarList v args

/-- `Expr.ArgVar` over an argument list. -/
def Expr.ArgVarList (v : Var) : List Expr → Prop
  | [] => False
  | e :: es => Expr.ArgVar v e ∨ Expr.ArgVarList v es

end

@[inherit_doc Expr.ArgVar]
def Pattern.ArgVar (v : Var) : Pattern → Prop
  | .expr e => Expr.ArgVar v e
  | .eq e₁ e₂ => Expr.ArgVar v e₁ ∨ Expr.ArgVar v e₂
  | .values vs _ as => Expr.ArgVarList v vs ∨ Expr.ArgVarList v as

/-- **Every variable the query mentions sits at a key column.** The condition under which the
source-side reading of a query variable exists: a variable at a key column is read back by
`Database.ViewsSound`, and one at no key column — a whole pattern, or a whole side of an
equality — is read back by nothing.

Stronger than `exists_sourceReading` strictly needs: a variable the source's own environment
binds is read back from `Database.GlobalsRead` instead, and needs no key column. Stated this
way because the weaker condition would have to ask which variables a top-level `let` binds,
and this one is a property of the query alone. -/
def Query.VarsKeyed (q : Query) : Prop := ∀ v ∈ Query.vars q, ∃ p ∈ q, Pattern.ArgVar v p

/-- **The queries the flattening handles.** `Pattern.Grounded` and `Pattern.NoValues` at
every pattern of a rule's query, and `Query.VarsKeyed` at the query. Vacuous at every other
command, which is the only place a query can occur. -/
def Cmd.QueryEncodable : Cmd → Prop
  | .rule r => (∀ p ∈ r.query, p.Grounded ∧ p.NoValues) ∧ Query.VarsKeyed r.query
  | _ => True

/-! ### The heads the source cannot run

A source rule head that gets **stuck** contributes nothing and its encoding's head writes
anyway. `RuleResults` asks `evalLocalActions` for a `some`, so a stuck block silently drops
the firing — where a stuck *top-level* action drops `ProgramStep` and makes the claim
vacuous, a stuck rule head leaves the source running and the target one entry ahead. Two
shapes do it, and each of the two clauses below excludes one:

* **A `union` on a literal.** `evalAction` refuses it — egglog's type checker does, and this
  untyped model cannot see it until the operands are values — while `encodeAction` emits
  `.set @UF [ordering-max …] […]`, which `execAction` never refuses. Only a **rule head**
  needs excluding, and either by having no `union` or by the program building no literal at
  all: a bare variable operand can be bound to a literal too, and it is bound to a term the
  source holds.
  `encode_corresponds_unions_literals` is the program, and it refutes the *conclusion*
  rather than only its residue: the bogus edge is what a rebuild column rule then re-keys a
  view entry along.
* **An application of a name nobody declared.** `Expr.eval` needs `Signature.IsCtor`, so the
  source head is stuck, while `encodePrelude` declares a skolem constructor for **every**
  name `Program.ctors` reads off the uses — declared or not. `execM_soundTerms_false` is that
  program.

Both are decidable conditions on the source program's text, so a witness discharges them by
`decide` and `difftest`'s census counts exactly them. Neither costs the corpus
anything: all seventy in-domain cases are literal-free and are run with their constructors
declared up front (`Program.declared`). -/

mutual

/-- No literal occurs in the expression. -/
def Expr.litFreeB : Expr → Bool
  | .lit _ => false
  | .var _ => true
  | .app _ args => Expr.litFreeListB args

/-- `Expr.litFreeB` over an argument list. -/
def Expr.litFreeListB : List Expr → Bool
  | [] => true
  | e :: es => Expr.litFreeB e && Expr.litFreeListB es

end

/-- No literal occurs in an expression the action **evaluates**. Patterns are not read: a
literal in a query builds nothing, and a variable is only ever bound to a term the source
holds. -/
def Action.litFreeB : Action → Bool
  | .expr e => e.litFreeB
  | .letBind _ e => e.litFreeB
  | .union e₁ e₂ => e₁.litFreeB && e₂.litFreeB
  | .set _ args out => Expr.litFreeListB args && Expr.litFreeListB out

/-- `Action.litFreeB` at every action a command runs. -/
def Cmd.litFreeB : Cmd → Bool
  | .action a => a.litFreeB
  | .rule r => r.actions.all Action.litFreeB
  | _ => true

/-- `Action.UnionFree`, computed. -/
def Action.unionFreeB : Action → Bool
  | .union _ _ => false
  | _ => true

theorem Action.unionFreeB_iff (a : Action) : a.unionFreeB = true ↔ a.UnionFree := by
  cases a <;> simp [Action.unionFreeB, Action.UnionFree]

theorem Actions.unionFreeB_iff : ∀ as : List Action,
    as.all Action.unionFreeB = true ↔ Actions.UnionFree as
  | [] => by simp
  | a :: as => by
      simp only [List.all_cons, Bool.and_eq_true, Actions.UnionFree, Action.unionFreeB_iff,
        Actions.unionFreeB_iff as]

/-- No **rule head** asserts a `union`. A top-level `union` needs no clause: on a literal it
sticks the source run outright, and `ProgramStep` then has no state for the correspondence to
be about — which is what `difftest`'s `litUnionCase` reports as `sourceStuck`. -/
def Cmd.ruleUnionFreeB : Cmd → Bool
  | .rule r => r.actions.all Action.unionFreeB
  | _ => true

@[inherit_doc Cmd.ruleUnionFreeB]
theorem Cmd.ruleUnionFreeB_iff (r : Rule) :
    (Cmd.rule r).ruleUnionFreeB = true ↔ r.UnionFree :=
  Actions.unionFreeB_iff r.actions

/-- `Spec/Scope.lean`'s `Action.Declared` at a rule's head, and nothing at any other
command: a stuck **top-level** action drops `ProgramStep` and makes the claim vacuous, so
only a head needs the condition. -/
def Cmd.HeadsDeclared : Cmd → Signature → Prop
  | .rule r, sig => Actions.Declared r.actions sig
  | _, _ => True

/-- **Every name a rule head applies is declared before the rule.** `Actions.Declared` at
the signature `Cmd.sigBind` has reached, so this is "declared *earlier in the program*" and
not merely "declared somewhere": a declaration after the run that fires the rule is not in
the signature the firing reads, and `Cmd.sigBind` is the only thing that grows it. A rule
cannot fire before its own `Cmd.rule`, so declared-before-the-rule is
declared-before-every-firing.

`Action.Declared` lets a **primitive** stand in for a declaration, since a `:merge` body is
where primitives are legal; `EncodeDomain.noPrim` closes that off for a source program, and a
rule head's names are among `Program.ctors`. -/
@[simp] def Program.HeadsDeclared : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.HeadsDeclared sig ∧ Program.HeadsDeclared cs (c.sigBind sig)

/-! Given `noPrim` this is equivalent to the `Bool` accumulator it replaced —
`Program.HeadsDeclared P (fun _ => none) ↔ headCtorsDeclaredB [] P` — for **every** program and
not only the corpus, checked out of tree and left there, since stating it in the build needs
that `Bool` back. In tree the evidence is `encodeDomainB_iff` and the census pins. -/

/-! #### Deciding the two checks the domain takes from `Spec/Scope.lean`

Both read a signature entry, and `FnDecl` carries no `DecidableEq`, so the instances go
through `Option.isSome`. With them a witness discharges either clause by `decide`, as it did
the `Bool` these replaced. -/

instance decidableNeNone {α : Type u} (o : Option α) : Decidable (o ≠ none) :=
  decidable_of_iff (o.isSome = true) (by cases o <;> simp)

instance Expr.decidableDeclared (e : Expr) (sig : Signature) : Decidable (e.Declared sig) :=
  inferInstanceAs (Decidable (∀ f ∈ e.fns, Prim.ofName f ≠ none ∨ sig f ≠ none))

instance Action.decidableDeclared : ∀ (a : Action) (sig : Signature),
    Decidable (a.Declared sig)
  | .expr e, sig => inferInstanceAs (Decidable (e.Declared sig))
  | .letBind _ e, sig => inferInstanceAs (Decidable (e.Declared sig))
  | .union e₁ e₂, sig => inferInstanceAs (Decidable (e₁.Declared sig ∧ e₂.Declared sig))
  | .set f args out, sig =>
      inferInstanceAs (Decidable (sig f ≠ none ∧ (∀ e ∈ args, e.Declared sig) ∧
        ∀ e ∈ out, e.Declared sig))

instance Actions.decidableDeclared : ∀ (as : List Action) (sig : Signature),
    Decidable (Actions.Declared as sig)
  | [], _ => .isTrue trivial
  | a :: as, sig =>
      @instDecidableAnd _ _ (Action.decidableDeclared a sig) (Actions.decidableDeclared as sig)

instance Cmd.decidableHeadsDeclared : ∀ (c : Cmd) (sig : Signature),
    Decidable (c.HeadsDeclared sig)
  | .rule r, sig => inferInstanceAs (Decidable (Actions.Declared r.actions sig))
  | .action _, _ => .isTrue trivial
  | .run _, _ => .isTrue trivial
  | .saturate _, _ => .isTrue trivial
  | .decl _ _, _ => .isTrue trivial

instance Program.decidableHeadsDeclared : ∀ (P : Program) (sig : Signature),
    Decidable (Program.HeadsDeclared P sig)
  | [], _ => .isTrue trivial
  | c :: cs, sig => @instDecidableAnd _ _ (Cmd.decidableHeadsDeclared c sig)
      (Program.decidableHeadsDeclared cs (c.sigBind sig))

instance Action.decidableSetLegal : ∀ (a : Action) (sig : Signature),
    Decidable (a.SetLegal sig)
  | .expr _, _ => .isTrue trivial
  | .letBind _ _, _ => .isTrue trivial
  | .union _ _, _ => .isTrue trivial
  | .set f _ _, sig => inferInstanceAs (Decidable (sig.mergeOf f ≠ none))

instance Actions.decidableSetLegal : ∀ (as : List Action) (sig : Signature),
    Decidable (Actions.SetLegal as sig)
  | [], _ => .isTrue trivial
  | a :: as, sig =>
      @instDecidableAnd _ _ (Action.decidableSetLegal a sig) (Actions.decidableSetLegal as sig)

instance Cmd.decidableSetLegal : ∀ (c : Cmd) (sig : Signature), Decidable (c.SetLegal sig)
  | .action a, sig => inferInstanceAs (Decidable (a.SetLegal sig))
  | .rule r, sig => inferInstanceAs (Decidable (Actions.SetLegal r.actions sig))
  | .run _, _ => .isTrue trivial
  | .saturate _, _ => .isTrue trivial
  | .decl _ _, _ => .isTrue trivial

instance Program.decidableSetLegal : ∀ (P : Program) (sig : Signature),
    Decidable (Program.SetLegal P sig)
  | [], _ => .isTrue trivial
  | c :: cs, sig => @instDecidableAnd _ _ (Cmd.decidableSetLegal c sig)
      (Program.decidableSetLegal cs (c.sigBind sig))

/-- **Legality plus the encoding-specific residue.** Three clauses are `Spec`'s own static
checks — `Program.CtorDecls`, `Program.SetLegal`, and `Action.Declared` threaded along
`Cmd.sigBind` — and four are conditions only the encoding needs: the generated namespace has
to be fresh, the query flattening has to be total, and a rule head has to be one the source
can run. -/
structure Program.EncodeDomain (P : Program) : Prop where
  /-- Every declared function is a constructor: `Spec/Syntax.lean`'s own
  `Program.CtorDecls`, which is what `exec_programStep` asks for. -/
  ctorsOnly : P.CtorDecls
  /-- No `set` writes a table. Stated as `Spec/Scope.lean`'s `Action.SetLegal` threaded along
  `Cmd.sigBind`, which under `ctorsOnly` is exactly "no `set` anywhere"
  (`Program.setLegal_iff_noSet`): a `set` head must be a `:merge` or `:no-merge` function and
  a constructor-only program declares none. `Action.set` is what a `:merge` function and an
  encoded rule head need, and the constructor fragment has neither. -/
  setLegal : Program.SetLegal P (fun _ => none)
  /-- No source function shadows a primitive, so every application builds. Not implied by
  `Program.Evaluable`, which says nothing of a **query** pattern's names; `P.ctors` reads
  them too. -/
  noPrim : ∀ fk ∈ P.ctors, Prim.ofName fk.1 = none
  /-- **No source name is in the generated namespace**, over all three kinds of name at once
  (`Program.names`), because one collision is one defect however the name is used.

  * A **function** name: the prelude's tables and skolems are `@`-prefixed.
  * A **variable**: the generated `@v0`, `@v1`, … are numbered from one supply for the whole
    program, so they collide with nothing but a source `@` name.
  * A **ruleset**: the maintenance rules join `rebuildRuleset`, which is `@rebuild`, and
    `encodeRule` keeps a source rule's own ruleset — so a source rule joining `@rebuild`
    would be fired by every `Cmd.saturate rebuildRuleset` the encoding emits, where the
    source fires it only under a run naming it. That is an equality in the target the source
    never derives, and it is a name that is neither a function nor a variable. -/
  noAt : ∀ n ∈ P.names, ¬ "@".isPrefixOf n
  /-- **Every source query is one the flattening handles.** `encodePattern` emits no atom for
  a source pattern whose expression is a bare leaf, so `.expr (.lit l)` becomes the *empty*
  constraint — which every target matches where the source pattern matches nothing
  (`encodeQuery_drops_literal_pattern`) — and `.expr (.var v)` leaves its variable bound by
  nothing, where the source rule's `ValidEnv` must bind it to a term the source holds.
  `Pattern.Grounded` excludes the first and `Query.VarsKeyed` the second, and
  `Pattern.NoValues` excludes the entry atom the fragment has no table for.
  A condition on the source text that no other clause implies —
  `Encoding/Match.lean`'s `litProgram` is the program it excludes, and
  `litProgram_not_encodeDomain` is that recorded — and it costs the corpus nothing: all
  seventy in-domain cases satisfy it. -/
  queryEncodable : ∀ c ∈ P, c.QueryEncodable
  /-- **No `union` is handed a literal.** Either the program asserts no `union` at all, or
  it builds no literal — and then no term it holds is one, so no operand can evaluate to
  one. `Spec/Scope.lean`'s `Action.UnionLegal` is the syntactic half of this, and the clause
  implies it at every rule head (`Program.EncodeDomain.unionLegal_of_mem`); the converse
  fails, since `UnionLegal` says nothing about a **variable** operand and a query binds one
  under a literal argument, so the clause has to read the whole program.
  `encode_corresponds_unions_literals` is the program this excludes, and it refutes
  `encode_corresponds_complete` rather than only its residue. -/
  noLitUnion : (∀ c ∈ P, c.ruleUnionFreeB = true) ∨ ∀ c ∈ P, c.litFreeB = true
  /-- **Every name a rule head applies is declared before the rule**, so the source's head
  builds wherever the encoded head does. `Spec/Scope.lean`'s `Actions.Declared` along
  `Cmd.sigBind`. `execM_soundTerms_false` is the program this excludes: `encodePrelude`
  declares a skolem for every applied name, declared or not. -/
  headsDeclared : Program.HeadsDeclared P (fun _ => none)

/-! #### The `union` legality the clause implies

`Spec/Scope.lean`'s `Action.UnionLegal` at a rule head, from either disjunct of
`noLitUnion`: with no `union` in a head there is nothing to check, and with no literal in the
program an operand is not one. -/

/-- An action that asserts no equation asserts none on a literal. -/
theorem Action.UnionLegal.of_unionFree {a : Action} (h : a.UnionFree) : a.UnionLegal := by
  cases a <;> first | trivial | exact absurd h id

/-- An action that evaluates no literal hands none to a `union`. -/
theorem Action.UnionLegal.of_litFreeB {a : Action} (h : a.litFreeB = true) : a.UnionLegal := by
  cases a with
  | union e₁ e₂ =>
      simp only [Action.litFreeB, Bool.and_eq_true] at h
      refine ⟨fun l hl => ?_, fun l hl => ?_⟩
      · rw [hl] at h; simp [Expr.litFreeB] at h
      · rw [hl] at h; simp [Expr.litFreeB] at h
  | expr _ => trivial
  | letBind _ _ => trivial
  | set _ _ _ => trivial

@[inherit_doc Action.UnionLegal.of_unionFree]
theorem Actions.UnionLegal.of_mem : ∀ {as : List Action}, (∀ a ∈ as, a.UnionLegal) →
    Actions.UnionLegal as
  | [], _ => trivial
  | _ :: as, hall =>
      ⟨hall _ (List.mem_cons_self ..),
        Actions.UnionLegal.of_mem fun b hb => hall b (List.mem_cons_of_mem _ hb)⟩

/-- **The domain's `noLitUnion` implies `union` legality at every rule head.** Not the
converse: `Action.UnionLegal` reads the operand expressions, and a *variable* operand bound to
a literal is what the clause's second disjunct is for. -/
theorem Program.EncodeDomain.unionLegal_of_mem {P : Program} (h : P.EncodeDomain) {r : Rule}
    (hr : Cmd.rule r ∈ P) : Actions.UnionLegal r.actions := by
  rcases h.noLitUnion with hfree | hlit
  · refine Actions.UnionLegal.of_mem fun a ha => Action.UnionLegal.of_unionFree ?_
    have hb := hfree _ hr
    simp only [Cmd.ruleUnionFreeB, List.all_eq_true] at hb
    exact (Action.unionFreeB_iff a).mp (hb a ha)
  · refine Actions.UnionLegal.of_mem fun a ha => Action.UnionLegal.of_litFreeB ?_
    have hb := hlit _ hr
    simp only [Cmd.litFreeB, List.all_eq_true] at hb
    exact hb a ha

/-! ### Reading the target

The three notions the deleted M11 theorems were stated over. None of them is `Cong`: the
encoded program's tables are `.merge` functions and it asserts no equation but the
reflexive one `addTerm` records, so `Cong` on the target is the identity relation on the
terms it holds. Equality on the target side is *only* what `@UF` and the views record.

Source-side equality is `Spec/Congruence.lean`'s `CongOn`, not `Cong`: the rebuild re-keys
a view entry to its children's leaders, so the encoded database ends up holding entries
about applications the source never built — `@AddView [1,1] ↦ Add[1,2]` after `(Add 1 2)`
and `(union 1 2)`. Those entries are still *true*, but only in that sense. `ENCODING.md`
records why `CongOn` is nevertheless too weak to state a theorem over unmodified. -/
/-- A union-find edge that moves. The `:merge` writes `@UF (ordering-max p p) ↦
(ordering-min p p, _)` on a self-collision, so reflexive self-loops are ordinary entries and
a leader is "no edge that moves" rather than "no entry".

Existential in the proof column: which justification an edge carries is not what being an
edge means. -/
def UFEdge (d : Database) (t p : Term) : Prop :=
  (∃ pf, d.Out ufName [t] [p, pf]) ∧ p ≠ t

/-- `l` is `t`'s representative: reachable along edges, and itself at the end of one.

A relation rather than a function because `Database.Out` reads *any* recorded output —
the model keeps the entries a merge displaces (`MERGE.md`, "Constraint (3): monotonicity"),
so a term can have several recorded parents, every one genuinely equal to it. -/
def UFLeader (d : Database) (t l : Term) : Prop :=
  Relation.ReflTransGen (UFEdge d) t l ∧ ∀ p, ¬ UFEdge d l p

mutual

/-- The e-class the encoded database gives a source term: one view read per subterm,
joined on ids. This is what `check` compiles to (`proof_encoding.md`, "Queries"), and it
is the source-to-target correspondence the simulation theorem needs.

A literal is its own id — it has no view, since only an application does — and **without a
premise**: a literal needs no justification in the encoding, so nothing about the *target* is
asked for it. Asking `Term.lit l ∈ d.terms` would be asking the target to hold a term the
encoding never emits an e-node for; `ViewRepr.eq_of_lit` is what keeps that from classing two
literals together. -/
inductive ViewRepr (d : Database) : Term → Term → Prop where
  | lit {l : Lit} : ViewRepr d (.lit l) (.lit l)
  | app {f : FnName} {as es : List Term} {e pf : Term} :
      ViewReprList d as es → d.Out (viewName f) es [e, pf] → ViewRepr d (.app f as) e

/-- `ViewRepr` over an argument list. -/
inductive ViewReprList (d : Database) : List Term → List Term → Prop where
  | nil : ViewReprList d [] []
  | cons {a e : Term} {as es : List Term} :
      ViewRepr d a e → ViewReprList d as es → ViewReprList d (a :: as) (e :: es)

end

/-- Two source terms are in one e-class of the encoded database: **one id is a `ViewRepr`
of both**.

Existential in the read because `ViewRepr` is, and because that is the direction both
halves of the simulation want — a match exists iff the equality holds.

**No union-find walk.** The reading through `UFLeader` — two ids with a common leader — is
the one egglog's `check` compiles, and it is *equivalent* at a rebuilt state: the e-class
rebuild rule re-`set`s a view entry at each `@UF` parent in turn and `terms` keeps both
versions, so a term's `ViewRepr` set is already closed under `UFEdge` and already contains
the leader. `difftest correspond`'s `via-uf` column measures the difference and it is 0 on
every case of the corpus and of the union-find probes, while dropping the rebuild makes it
71 pairs — so the walk is redundant *because of* `Rebuilt`, not intrinsically. The flat
reading is the one this file states a correspondence over, because it is the one the walk
adds nothing to and the smaller relation to prove things about. -/
def SameClass (d : Database) (a b : Term) : Prop :=
  ∃ e, ViewRepr d a e ∧ ViewRepr d b e

/-- `SameClass` is symmetric, in one step from the definition. -/
theorem SameClass.symm {d : Database} {a b : Term} (h : SameClass d a b) : SameClass d b a :=
  let ⟨e, ha, hb⟩ := h; ⟨e, hb, ha⟩

/-! #### What a literal's class can contain

Dropping the membership premise gives *every* literal an id, held or not. Two things have to
stay impossible, and both are one inversion: `ViewRepr` has exactly one clause whose
conclusion matches a literal, and it returns the literal itself. -/

/-- **A literal's only id is itself.** The `app` clause concludes at `Term.app`, so `lit` is
the only case, and it is not existential. -/
theorem ViewRepr.eq_of_lit {d : Database} {l : Lit} {e : Term}
    (h : ViewRepr d (.lit l) e) : e = .lit l := by
  cases h with | lit => rfl

/-- **Distinct literals are never in one class**: one id equal to both is `.lit l₁ = .lit l₂`. -/
theorem SameClass.eq_of_lit {d : Database} {l₁ l₂ : Lit}
    (h : SameClass d (.lit l₁) (.lit l₂)) : l₁ = l₂ := by
  obtain ⟨e, h₁, h₂⟩ := h
  exact Term.lit.inj ((h₁.eq_of_lit).symm.trans h₂.eq_of_lit)

/-- **A literal is in an application's class only through a view row whose e-class column is
that literal.** The `app` clause is the only one that concludes at an application, so its
entry has to carry the literal in the column an id is read from. `Correspond.lean`'s
`not_sameClass_lit_app` is that row ruled out at any target `ViewsSound` holds of. -/
theorem SameClass.out_of_lit_app {d : Database} {l : Lit} {f : FnName} {as : List Term}
    (h : SameClass d (.lit l) (.app f as)) :
    ∃ es pf, ViewReprList d as es ∧ d.Out (viewName f) es [.lit l, pf] := by
  obtain ⟨e, h₁, h₂⟩ := h
  obtain rfl : e = Term.lit l := h₁.eq_of_lit
  cases h₂ with | app hl ho => exact ⟨_, _, hl, ho⟩

/-- The rebuild schedule has run out: no maintenance rule adds anything, and no merge
step changes anything. It is the hypothesis the completeness half of simulation needs —
until the views are re-keyed to leaders, a collision that congruence would find has not yet
happened.

`ENCODING.md`, finding 1, was that no state `encode` ran to satisfied this, because
`Cmd.run` carried no ruleset and the number of rounds needed to re-key grows with term
depth. `encode` now emits `Cmd.saturate rebuildRuleset` after every run, and
`saturateReach_rebuilt` below is that repair: this is that command's *postcondition*.

**A second reason it was unsatisfiable, since removed.** The proof column landed after that
repair. `MergeSaturated`, the second conjunct, asks that no collision change anything, and
every entry collides with itself: `mergeBody` writes `@UF(v) ↦ (v, @Trans (@Sym pf) pf)` for
the colliding pair, a term one composition larger than the proof it started from, so a
`Rebuilt` state had to hold the whole tower and no state with finitely many terms does. What
closed it is `Spec/Step.lean`'s `MergeConflict`: a self-collision at a table declaring
`identityVals := some 1` moves no counted column, so it is not a `MergeStep` and there is no
tower. `Encoding/Correspond.lean`'s `refutationState_mergeSaturated` and
`satProgram_programStep` are the two readings of that. -/
def Rebuilt (P : Program) (d : Database) : Prop :=
  (∀ r ∈ maintenanceRules P, ∀ d' ∈ RuleResults d r, Database.Contained d' d) ∧
    MergeSaturated d

/-- **`Rebuilt` is `RunSaturated rebuildRuleset`.** The only bookkeeping is `hR`: the
rules of `d` in the rebuild ruleset are the maintenance rules `encode` emitted. -/
theorem rebuilt_iff_runSaturated {P : Program} {d : Database}
    (hR : ∀ r, (r ∈ d.rules ∧ r.ruleset = rebuildRuleset) ↔ r ∈ maintenanceRules P) :
    RunSaturated rebuildRuleset d ↔ Rebuilt P d := by
  rw [RunSaturated, runRules_eq_self_iff]
  exact and_congr_left' ⟨fun h r hr => h r ((hR r).mpr hr).1 ((hR r).mpr hr).2,
    fun h r hr hRr => h r ((hR r).mp ⟨hr, hRr⟩)⟩

/-- **And `Cmd.saturate rebuildRuleset` delivers it**, with no extra hypothesis. This is
what the ruleset bought: `Rebuilt` went from a condition nothing reachable satisfied to the
postcondition of a command the encoding emits. -/
theorem saturateReach_rebuilt {P : Program} {db d : Database}
    (hR : ∀ r, (r ∈ d.rules ∧ r.ruleset = rebuildRuleset) ↔ r ∈ maintenanceRules P)
    (h : SaturateReach rebuildRuleset db d) : Rebuilt P d :=
  (rebuilt_iff_runSaturated hR).mp h.2

/-- Read through `CmdStep`: whatever the encoded program's rebuild command steps to is
rebuilt. `cmdStep_saturate_iff` is what makes the trailing merge phase neutral here. -/
theorem cmdStep_rebuilt {P : Program} {db d : Database}
    (hR : ∀ r, (r ∈ d.rules ∧ r.ruleset = rebuildRuleset) ↔ r ∈ maintenanceRules P)
    (h : CmdStep db (.saturate rebuildRuleset) d) : Rebuilt P d :=
  saturateReach_rebuilt hR (cmdStep_saturate_iff.mp h)

end Egglog
