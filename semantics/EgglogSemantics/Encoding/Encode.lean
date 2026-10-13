import EgglogSemantics.Encoding.Source
import EgglogSemantics.Encoding.Names

/-!
# Legacy combined congruence and proof encoding

`Egglog.encode` is retained while its end-to-end correspondence proof is ported to
`Egglog.Congruence.encode`. Its data correspondence theorem remains valid, but its proof
annotations are not sound certificates: `encodeBuild` writes `@Fiat` for rule-created
terms, and the legacy checker can accept premises for terms that never existed.

The new congruence pass has no proof vocabulary or proof columns. Provenance and
resugaring will be separate passes; this encoder is not their implementation.
-/

namespace Egglog
/-! ### Proof terms

A proof is an **ordinary term**: an application of a declared constructor, built by
`Expr.eval` like every other term the encoding writes.

**A legacy proof term does not carry its proposition** — the row it sits in does. `@UF(t) ↦ (p,
pf)` is `pf : t = p`, and `@fView(c…) ↦ (e, pf)` is `pf : f(c…) = e`; both read key-to-value,
where egglog's view runs the other way (`proof_encoding.md`, "Union-find"). This loses
information needed when the proof becomes a rule premise. The replacement certificate
format must carry explicit claims and evidence of source-term existence.

Five justification kinds, interpreted by `Encoding/Checker.lean`:

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
  [.expr (.app ufName [maxE (.var "old0") (.var "new0"), minE (.var "old0") (.var "new0"), transE (symE hiPfE) loPfE])]

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

mutual

/-- Flatten `e` into view reads. Returns the expression naming `e`'s e-class, the reads,
and the next variable number.

A view read is a function-entry atoms atom, which is what egglog lowers `(= e (@fView c…))` to
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
           ps ++ [.expr (.app (viewName f) (es ++ [.var (freshVar n₁), .var (freshVar (n₁ + 1))]))],
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

/-! #### Where the flattened query's variables come from

Every variable an encoded query mentions is either one `freshVar` minted — and so
`@`-prefixed, which `FDatabase.NoAtEnv` keeps out of the environment — or one the source
query already had. That is what says the target's stored rule is the encoder's own output:
`FDatabase.execCmdM` resolves the globals then in scope into a rule it registers
(`Spec/Step.lean`'s `cmdEffect`, mirrored), and at an encoded rule there is nothing left to
resolve. -/


mutual

@[inherit_doc atPrefix_freshVar]
theorem mem_vars_encodeQueryExpr : ∀ (e : Expr) (n : Nat) {v : Var},
    v ∈ Query.vars (encodeQueryExpr e n).2.1 ∨ v ∈ (encodeQueryExpr e n).1.vars →
      "@".isPrefixOf v = true ∨ v ∈ e.vars
  | .lit _, n, v, h => by
      rcases h with h | h
      · exact absurd h (by rw [encodeQueryExpr]; simp [Query.vars])
      · exact absurd h (by rw [encodeQueryExpr]; simp [Expr.vars])
  | .var w, n, v, h => by
      rcases h with h | h
      · exact absurd h (by rw [encodeQueryExpr]; simp [Query.vars])
      · refine Or.inr ?_
        rw [encodeQueryExpr] at h
        exact h
  | .app f args, n, v, h => by
      rw [encodeQueryExpr] at h
      rcases h with h | h
      · rcases Query.mem_vars_append.mp h with h' | h'
        · exact mem_vars_encodeQueryArgs args n (Or.inl h')
        · have h'' : v ∈ Query.vars [Pattern.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++ [Expr.var (freshVar (encodeQueryArgs args n).2.2),
               Expr.var (freshVar ((encodeQueryArgs args n).2.2 + 1))]))] := h'
          rw [Query.vars, Query.vars, Pattern.vars] at h''
          rcases (by simpa [Expr.vars, Expr.varsList, or_comm] using h'' :
              (v = freshVar (encodeQueryArgs args n).2.2 ∨
                  v = freshVar ((encodeQueryArgs args n).2.2 + 1)) ∨
                v ∈ Expr.varsList (encodeQueryArgs args n).1) with hk | hk
          · rcases hk with rfl | rfl <;> exact Or.inl (atPrefix_freshVar _)
          · exact mem_vars_encodeQueryArgs args n (Or.inr hk)
      · obtain rfl : v = freshVar (encodeQueryArgs args n).2.2 := by
          simpa [Expr.vars] using h
        exact Or.inl (atPrefix_freshVar _)

@[inherit_doc atPrefix_freshVar]
theorem mem_vars_encodeQueryArgs : ∀ (es : List Expr) (n : Nat) {v : Var},
    v ∈ Query.vars (encodeQueryArgs es n).2.1 ∨ v ∈ Expr.varsList (encodeQueryArgs es n).1 →
      "@".isPrefixOf v = true ∨ v ∈ Expr.varsList es
  | [], n, v, h => by
      rcases h with h | h
      · exact absurd h (by rw [encodeQueryArgs]; simp [Query.vars])
      · exact absurd h (by rw [encodeQueryArgs]; simp [Expr.varsList])
  | e :: es, n, v, h => by
      have hsplit : (encodeQueryArgs (e :: es) n)
          = ((encodeQueryExpr e n).1 :: (encodeQueryArgs es (encodeQueryExpr e n).2.2).1,
             (encodeQueryExpr e n).2.1
               ++ (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.1,
             (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.2) := rfl
      rw [hsplit] at h
      have hor : ("@".isPrefixOf v = true ∨ v ∈ e.vars) ∨
          ("@".isPrefixOf v = true ∨ v ∈ Expr.varsList es) := by
        rcases h with h | h
        · rcases Query.mem_vars_append.mp h with h' | h'
          · exact Or.inl (mem_vars_encodeQueryExpr e n (Or.inl h'))
          · exact Or.inr (mem_vars_encodeQueryArgs es _ (Or.inl h'))
        · rw [Expr.varsList] at h
          rcases List.mem_union_iff.mp h with h' | h'
          · exact Or.inl (mem_vars_encodeQueryExpr e n (Or.inr h'))
          · exact Or.inr (mem_vars_encodeQueryArgs es _ (Or.inr h'))
      rw [Expr.varsList]
      rcases hor with h' | h'
      · exact h'.imp id fun hv => List.mem_union_iff.mpr (Or.inl hv)
      · exact h'.imp id fun hv => List.mem_union_iff.mpr (Or.inr hv)

end

@[inherit_doc atPrefix_freshVar]
theorem mem_vars_encodePattern : ∀ (p : Pattern) (n : Nat) {v : Var},
    v ∈ Query.vars (encodePattern p n).1 → "@".isPrefixOf v = true ∨ v ∈ p.vars
  | .expr e, n, v, h => mem_vars_encodeQueryExpr e n (Or.inl h)
  | .eq e₁ e₂, n, v, h => by
      rw [encodePattern] at h
      rcases Query.mem_vars_append.mp h with h' | h'
      · rcases Query.mem_vars_append.mp h' with h'' | h''
        · exact (mem_vars_encodeQueryExpr e₁ n (Or.inl h'')).imp id fun hv =>
            List.mem_union_iff.mpr (Or.inl hv)
        · exact (mem_vars_encodeQueryExpr e₂ _ (Or.inl h'')).imp id fun hv =>
            List.mem_union_iff.mpr (Or.inr hv)
      · have h'' : v ∈ Query.vars [Pattern.eq (encodeQueryExpr e₁ n).1
            (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1] := h'
        rw [Query.vars, Query.vars, Pattern.vars] at h''
        rcases (by simpa [Expr.vars, Expr.varsList, or_comm] using h'' :
            v ∈ (encodeQueryExpr e₁ n).1.vars ∨
              v ∈ (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1.vars) with hk | hk
        · exact (mem_vars_encodeQueryExpr e₁ n (Or.inr hk)).imp id fun hv =>
            List.mem_union_iff.mpr (Or.inl hv)
        · exact (mem_vars_encodeQueryExpr e₂ _ (Or.inr hk)).imp id fun hv =>
            List.mem_union_iff.mpr (Or.inr hv)

@[inherit_doc atPrefix_freshVar]
theorem mem_vars_encodeQuery : ∀ (q : Query) (n : Nat) {v : Var},
    v ∈ Query.vars (encodeQuery q n).1 → "@".isPrefixOf v = true ∨ v ∈ Query.vars q
  | [], n, v, h => absurd h (by rw [encodeQuery]; simp [Query.vars])
  | p :: ps, n, v, h => by
      have hsplit : (encodeQuery (p :: ps) n).1
          = (encodePattern p n).1 ++ (encodeQuery ps (encodePattern p n).2).1 := rfl
      rw [hsplit] at h
      rw [Query.vars]
      rcases Query.mem_vars_append.mp h with h' | h'
      · exact (mem_vars_encodePattern p n h').imp id fun hv =>
          List.mem_union_iff.mpr (Or.inl hv)
      · exact (mem_vars_encodeQuery ps _ h').imp id fun hv =>
          List.mem_union_iff.mpr (Or.inr hv)

/-- The premise proofs an encoded query binds: the second value column of every view read,
in query order. This is `@Rule_i`'s argument list, and its length is `@Rule_i`'s arity.

Read back off the emitted query rather than threaded out of `encodeQueryExpr`, which is
sound because a two-column read atom in an encoded query is one this file wrote: under
`Program.EncodeDomain` the source has no function-entry atoms at all. -/
def queryProofs (q : Query) : List Expr :=
  q.filterMap fun p => match p with
    | .expr (.app _ cols) => match cols.getLast? with
      | some (.var v) => some (.var v)
      | _ => none
    | _ => none

/-- `@Rule_i`'s arity: how many premises rule `r`'s encoded query reads. Independent of the
variable supply the encoding is at, so the prelude's declaration and the head's application
agree. -/
def ruleProofArity (r : Rule) : Nat := (queryProofs (encodeQuery r.query 0).1).length

/-! ### Building a term

`encodeBuild` writes a term-relation entry and a reflexive view entry for each application.
The structural term itself is the returned id; actions perform no view lookup. Rebuilding
propagates ids through the views when their children acquire different leaders. -/
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

**Known defect:** the view entry carries `@Fiat` even when a rule head built it.
Reflexivity does not establish source-term existence, so this is not a valid general
justification. The new congruence pass omits annotations entirely; the later provenance
pass must record the actual construction origin. -/
def encodeBuild : Expr → Nat → Expr × List Action × Nat
  | .lit l, n => (.lit l, [], n)
  | .var v, n => (.var v, [], n)
  | .app f args, n =>
      match encodeBuildArgs args n with
      | (es, as, n₁) =>
          (.app f es,
           as ++ [.expr (.app (termName f) (es ++ [.app f es])),
                  .expr (.app (viewName f) (es ++ [.app f es, fiatE]))],
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
  | .union e₁ e₂, n =>
      match encodeBuild e₁ n with
      | (x₁, as₁, n₁) =>
          match encodeBuild e₂ n₁ with
          | (x₂, as₂, n₂) =>
              (as₁ ++ as₂ ++ [.expr (.app ufName [maxE x₁ x₂, minE x₁ x₂, pf])], n₂)

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

The composed proof justifies the edge from `a` through `b` to `c`. -/
def pathCompressRule : Rule :=
  { query := [.expr (.app ufName [.var "@a", .var "@b", .var "@p"]),
              .expr (.app ufName [.var "@b", .var "@c", .var "@q"])],
    actions := [.expr (.app ufName [.var "@a", .var "@c", transE (.var "@p") (.var "@q")])],
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
  let view : Pattern := .expr (.app (viewName f) (cs ++ [.var "@e", .var "@p"]))
  let eclassRule : Rule :=
    { query := [view, .expr (.app ufName [.var "@e", .var "@x", .var "@q"])],
      actions := [.expr (.app (viewName f) (cs ++ [.var "@x", transE (.var "@p") (.var "@q")]))],
      ruleset := rebuildRuleset }
  eclassRule :: (List.range k).map fun i =>
    { query := [view, .expr (.app ufName [.var ("@c" ++ toString i), .var "@x", .var "@q"])],
      actions := [.expr (.app (viewName f) ((cs.set i (.var "@x")) ++ [.var "@e", transE (symE (congrE (congrChildren k i))) (.var "@p")]))],
      ruleset := rebuildRuleset }

/-- The maintenance rules as they join `rebuildRuleset`. `Rebuilt` is stated over it. -/
def maintenanceRules (P : Program) : List Rule :=
  pathCompressRule :: P.ctors.flatMap fun fk => rebuildRules fk.1 fk.2

/-- A rebuild rule's column variable is in the generated namespace. -/
theorem atPrefix_rebuildVar (i : Nat) : "@".isPrefixOf ("@c" ++ toString i) = true := by
  rw [String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@c").toList = ['@', 'c'] from by decide]
  exact ⟨'c' :: (toString i).toList, rfl⟩

@[inherit_doc atPrefix_rebuildVar]
theorem atPrefix_of_mem_varsList_rebuildVars {k : Nat} {v : Var}
    (h : v ∈ Expr.varsList (rebuildVars k)) : "@".isPrefixOf v = true := by
  obtain ⟨e, he, hv⟩ := Expr.mem_varsList h
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
  obtain rfl : v = "@c" ++ toString i := by simpa [Expr.vars] using hv
  exact atPrefix_rebuildVar i

/-- **A maintenance rule's query variables are all generated.** `@a`, `@b`, `@c`, `@e`, `@p`,
`@q`, `@x` and the `@c…` columns, and nothing else — which is what keeps a state's own
environment (`FDatabase.NoAtEnv`) out of one. -/
theorem atPrefix_of_mem_vars_maintenanceRules {P : Program} {m : Rule}
    (hm : m ∈ maintenanceRules P) : ∀ v ∈ Query.vars m.query, "@".isPrefixOf v = true := by
  rw [maintenanceRules, List.mem_cons] at hm
  rcases hm with rfl | hm
  · intro v hv
    have hv' : v = "@p" ∨ v = "@a" ∨ v = "@c" ∨ v = "@q" ∨ v = "@b" := by
      simpa [pathCompressRule, Query.vars, Pattern.vars, Expr.varsList, Expr.vars, or_left_comm, or_assoc, or_comm] using hv
    rcases hv' with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · obtain ⟨fk, -, hm'⟩ := List.mem_flatMap.mp hm
    have hq : ∃ X : Expr,
        (X = Expr.var "@e" ∨ ∃ i : Nat, X = Expr.var ("@c" ++ toString i)) ∧
        m.query = [.expr (.app (viewName fk.1) ((rebuildVars fk.2) ++ [.var "@e", .var "@p"])),
                   .expr (.app ufName [X, .var "@x", .var "@q"])] := by
      rw [rebuildRules, List.mem_cons] at hm'
      rcases hm' with rfl | hm''
      · exact ⟨.var "@e", Or.inl rfl, rfl⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hm''
        exact ⟨.var ("@c" ++ toString i), Or.inr ⟨i, rfl⟩, rfl⟩
    obtain ⟨X, hX, hqe⟩ := hq
    intro v hv
    rw [hqe] at hv
    have hv' : (v = "@e" ∨ v = "@p") ∨ v ∈ Expr.varsList (rebuildVars fk.2) ∨
        (v = "@x" ∨ v = "@q") ∨ v ∈ X.vars := by
      simpa [Query.vars, Pattern.vars, Expr.varsList, Expr.vars, or_left_comm, or_assoc, or_comm] using hv
    rcases hv' with (rfl | rfl) | hc | (rfl | rfl) | hx
    · decide +kernel
    · decide +kernel
    · exact atPrefix_of_mem_varsList_rebuildVars hc
    · decide +kernel
    · decide +kernel
    · rcases hX with rfl | ⟨i, rfl⟩
      · obtain rfl : v = "@e" := by simpa [Expr.vars] using hx
        decide +kernel
      · obtain rfl : v = "@c" ++ toString i := by simpa [Expr.vars] using hx
        exact atPrefix_rebuildVar i

/-- **Every maintenance rule the encoding of `P` emits**: the `rebuildRuleset` copy, plus one
copy joining each ruleset a source `Cmd.saturate` names.

**Why the copies.** egglog instruments a schedule node at a time, and its `Run` case is
`(seq <run> <rebuild>)` (`egglog/src/proofs/proof_encoding.rs:1969`) while its `Saturate`
case recurses *into* the loop body (`:1978-1980`), so `(run-schedule (saturate R))` becomes
`(saturate (seq (run R) <rebuild>))` — a rebuild after **every** iteration, not one after the
loop. `Cmd` has no schedule nesting, so the same thing is had by joining the maintenance
rules to `R` itself: a round of `R` then re-keys the views the previous round's `union`s
moved, and the fixpoint of the union of the two rulesets is a fixpoint of each. Without them
a source `Cmd.saturate` rebuilds once, after `R` has already run to its own fixpoint, and a
rule needing an equality a *later* round discovered never sees it — `sat-hit` is that
program, and it lost the source's `(Hit)`. -/
def allMaintenanceRules (P : Program) : List Rule :=
  maintenanceRules P ++
    P.saturateRulesets.flatMap fun R => (maintenanceRules P).map fun r => { r with ruleset := R }

@[inherit_doc atPrefix_of_mem_vars_maintenanceRules]
theorem atPrefix_of_mem_vars_allMaintenanceRules {P : Program} {m : Rule}
    (hm : m ∈ allMaintenanceRules P) : ∀ v ∈ Query.vars m.query, "@".isPrefixOf v = true := by
  rw [allMaintenanceRules] at hm
  rcases List.mem_append.mp hm with h | h
  · exact atPrefix_of_mem_vars_maintenanceRules h
  · obtain ⟨R, -, h'⟩ := List.mem_flatMap.mp h
    obtain ⟨m₀, hm₀, rfl⟩ := List.mem_map.mp h'
    exact fun v hv => atPrefix_of_mem_vars_maintenanceRules hm₀ v hv

/-- **And so a state's environment has nothing to resolve in one.** -/
theorem Rule.resolveGlobals_maintenance {P : Program} {m : Rule}
    (hm : m ∈ allMaintenanceRules P) {σ : Env} (hat : ∀ b ∈ σ, ¬ "@".isPrefixOf b.1) :
    m.resolveGlobals σ = m := by
  refine Rule.resolveGlobals_eq_self _ fun v hv => ?_
  refine Env.lookup_eq_none_iff.mpr fun hd => ?_
  obtain ⟨t, hb⟩ := Env.mem_dom_iff.mp hd
  exact hat (v, t) hb (atPrefix_of_mem_vars_allMaintenanceRules hm v hv)

/-! ### The transformation -/
/-- The arities congruence is needed at: one `@Congr_k` per source constructor arity, and
none at 0 — a nullary constructor has no child column for a rebuild rule to move. -/
def congrArities (P : Program) : List Nat := (P.ctors.map Prod.snd).dedup.filter (· ≠ 0)

/-- The `@Rule_i` declaration one command contributes: one at a rule, none anywhere else. -/
def Cmd.proofDeclOf (G : List (Var × Expr)) (i : Nat) : Cmd → Program
  | .rule r => [.decl (ruleName i) (proofDecl (ruleProofArity (r.substGlobals G)))]
  | _ => []

/-- The rule counter after a command, so `ruleProofDecls` numbers the rules exactly as
`encodeCmds` does. -/
def Cmd.ruleStep : Cmd → Nat → Nat
  | .rule _, i => i + 1
  | _, i => i

/-- `(constructor @Rule_i (@Proof…) @Proof)` per source rule, at the arity that rule's
encoded query reads.

Walks the **program** rather than `Program.srcRules`, because the arity is read off the query
*after* `Rule.substGlobals`, and the globals in scope only move along the program. -/
def ruleProofDecls (P : Program) : List (Var × Expr) → Program → Nat → Program
  | _, [], _ => []
  | G, c :: cs, i =>
      c.proofDeclOf G i ++ ruleProofDecls P G cs (c.ruleStep i)

/-- The proof vocabulary: three fixed heads and the two arity-indexed families.

**First in the prelude**, because a declaration's `:merge` body and a rule's head are
checked and evaluated against the signature standing when they are read, and both apply
these. -/
def proofDecls (P : Program) : Program :=
  [.decl fiatName (proofDecl 0), .decl symName (proofDecl 1), .decl transName (proofDecl 2)] ++
    (congrArities P).map (fun k => .decl (congrName k) (proofDecl k)) ++
    ruleProofDecls P [] P 0

/-- The declarations and maintenance rules, emitted once at the top. -/
def encodePrelude (P : Program) : Program :=
  proofDecls P ++ .decl ufName ufDecl ::
    (P.ctors.flatMap fun fk =>
      [.decl fk.1 (skolemDecl fk.2), .decl (viewName fk.1) (viewDecl fk.2),
       .decl (termName fk.1) (termDecl fk.2)]) ++
    (allMaintenanceRules P).map .rule

/-- Encode one command. A source declaration is dropped: the prelude has already declared
its function as the skolem-id constructor and emitted its table triple, and re-emitting it
would be a redeclaration (`Cmd.DeclFresh`).

**Every command that writes is followed by a rebuild**, which is where egglog puts it —
after each one except a function, rule or sort declaration
(`egglog/src/proofs/proof_encoding.rs:1655-1662`). A top-level action writes, so a `union`
there creates congruence the views must be re-keyed for; without the rebuild it propagates
only to the columns the union names directly, and `Wrapper(Add One Two)`,
`Wrapper(Add Two One)`, `union One Two` leaves `Wrapper` as two classes where the source
has one.

**A `Cmd.saturate` needs one between its rounds, and the block cannot give it.** The trailing
`Cmd.saturate rebuildRuleset` runs after `R` has already reached its own fixpoint, so a rule
of round `k + 1` would read round `k`'s rows un-re-keyed where the specification's round
`k + 1` sees round `k`'s unions through `Cong`. egglog rebuilds after **every** iteration —
`instrument_schedule`'s `Run` case is `(seq <run> <rebuild>)`
(`egglog/src/proofs/proof_encoding.rs:1969`) and its `Saturate` case recurses into the loop
body (`:1978-1980`), so `(run-schedule (saturate R))` becomes
`(saturate (seq (run R) <rebuild>))`. `allMaintenanceRules` is that here: the maintenance
rules join `R` too, so a round of `R` rebuilds before the next one searches.

A declaration writes nothing and a rule only registers itself.

Two supplies are threaded: `n` numbers generated variables, and `i` numbers the rules, so
that the `@Rule_i` a head names is the one the prelude declared for it. -/
def encodeCmd (G : List (Var × Expr)) : Cmd → Nat → Nat → Program × Nat × Nat
  | .action a, n, i =>
      match encodeAction fiatE a n with
      | (as, n₁) => (as.map .action ++ [.saturate rebuildRuleset], n₁, i)
  | .rule r, n, i =>
      match encodeRule i (r.substGlobals G) n with | (r', n₁) => ([.rule r'], n₁, i + 1)
  | .run R, n, i => ([.run R, .saturate rebuildRuleset], n, i)
  | .saturate R, n, i => ([.saturate R, .saturate rebuildRuleset], n, i)
  | .decl _ _, n, i => ([], n, i)

/-- `encodeCmd` over a program, threading generated-variable and rule counters. -/
def encodeCmds (P : Program) : List (Var × Expr) → Program → Nat → Nat → Program × Nat × Nat
  | _, [], n, i => ([], n, i)
  | G, c :: cs, n, i =>
      match encodeCmd G c n i with
      | (p, n₁, i₁) =>
          match encodeCmds P G cs n₁ i₁ with
          | (p', n₂, i₂) => (p ++ p', n₂, i₂)

/-- **The encoding.** -/
def encode (P : Program) : Program := encodePrelude P ++ (encodeCmds P [] P 0 0).1

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
        [.expr (.app (termName f) ((encodeBuildArgs args n).1 ++ [.app f (encodeBuildArgs args n).1])),
         .expr (.app (viewName f) ((encodeBuildArgs args n).1 ++ [.app f (encodeBuildArgs args n).1, fiatE]))] := rfl

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
        [.expr (.app (termName f) (args ++ [.app f args])),
         .expr (.app (viewName f) (args ++ [.app f args, fiatE]))] := by
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

theorem encodeAction_union_actions (pf : Expr) (e₁ e₂ : Expr) (n : Nat) :
    (encodeAction pf (.union e₁ e₂) n).1
      = (encodeBuild e₁ n).2.1 ++ (encodeBuild e₂ (encodeBuild e₁ n).2.2).2.1 ++
        [.expr (.app ufName [maxE (encodeBuild e₁ n).1 (encodeBuild e₂ (encodeBuild e₁ n).2.2).1, minE (encodeBuild e₁ n).1 (encodeBuild e₂ (encodeBuild e₁ n).2.2).1, pf])] := rfl

theorem encodeActions_cons_actions (pf : Expr) (a : Action) (as : List Action) (n : Nat) :
    (encodeActions pf (a :: as) n).1
      = (encodeAction pf a n).1 ++ (encodeActions pf as (encodeAction pf a n).2).1 := rfl

/-- **A source `union` becomes a `set`.** This is the case the whole statement rests on. -/
theorem encodeAction_unionFree (pf : Expr) : ∀ (a : Action) (n : Nat),
    ∀ b ∈ (encodeAction pf a n).1, b.UnionFree := by
  rintro (e | ⟨e₁, e₂⟩) n b hb
  · exact encodeBuild_unionFree e n b (encodeAction_expr_actions .. ▸ hb)
  · rw [encodeAction_union_actions] at hb
    rcases List.mem_append.mp hb with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact encodeBuild_unionFree e₁ n b h'
      · exact encodeBuild_unionFree e₂ _ b h'
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

/-! #### A copy is the rule it copies

`allMaintenanceRules` changes only `Rule.ruleset`, and every property a maintenance rule is
ever asked for reads `Rule.query` and `Rule.actions`. `mem_maintenanceRules_of_mem_all` is
what carries a copy back to the rule it copies, and `{ r with ruleset := rebuildRuleset }`
has `r`'s two other fields definitionally — so a lemma stated at `r ∈ maintenanceRules P`
applies to a copy with no rewriting. -/

/-- Every maintenance rule joins `rebuildRuleset`. -/
theorem maintenanceRules_ruleset (P : Program) :
    ∀ r ∈ maintenanceRules P, r.ruleset = rebuildRuleset := by
  intro r hr
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hr
  rcases hr with rfl | ⟨fk, -, hmem⟩
  · rfl
  · simp only [rebuildRules, List.mem_cons, List.mem_map, List.mem_range] at hmem
    rcases hmem with rfl | ⟨i, -, rfl⟩ <;> rfl

/-- **A rule the prelude emits is a maintenance rule, up to the ruleset it joins.** -/
theorem mem_maintenanceRules_of_mem_all {P : Program} {r : Rule}
    (h : r ∈ allMaintenanceRules P) :
    { r with ruleset := rebuildRuleset } ∈ maintenanceRules P := by
  rcases List.mem_append.mp h with h₁ | h₁
  · rwa [show ({ r with ruleset := rebuildRuleset } : Rule) = r by
      rw [← maintenanceRules_ruleset P r h₁]]
  · obtain ⟨R, -, h₂⟩ := List.mem_flatMap.mp h₁
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp h₂
    rwa [show ({ ({ r₀ with ruleset := R } : Rule) with ruleset := rebuildRuleset } : Rule) = r₀ by
      rw [← maintenanceRules_ruleset P r₀ hr₀]]

/-- The `rebuildRuleset` copies are among them. -/
theorem mem_allMaintenanceRules_of_mem {P : Program} {r : Rule}
    (h : r ∈ maintenanceRules P) : r ∈ allMaintenanceRules P :=
  List.mem_append.mpr (Or.inl h)

@[inherit_doc mem_maintenanceRules_of_mem_all]
theorem allMaintenanceRules_unionFree (P : Program) :
    ∀ r ∈ allMaintenanceRules P, Actions.UnionFree r.actions :=
  fun r hr => maintenanceRules_unionFree P { r with ruleset := rebuildRuleset }
    (mem_maintenanceRules_of_mem_all hr)

/-- A command's own contribution to the prelude is one `@Rule_i` declaration, or nothing. -/
theorem mem_proofDeclOf {G : List (Var × Expr)} {i : Nat} {c d : Cmd}
    (h : d ∈ c.proofDeclOf G i) :
    ∃ r, c = .rule r ∧ d = .decl (ruleName i) (proofDecl (ruleProofArity (r.substGlobals G))) := by
  cases c <;> simp only [Cmd.proofDeclOf, List.not_mem_nil, List.mem_cons, or_false] at h
  case rule r => exact ⟨r, rfl, h⟩

theorem ruleProofDecls_unionFree (P : Program) :
    ∀ (G : List (Var × Expr)) (p : Program) (i : Nat),
    ∀ c ∈ ruleProofDecls P G p i, Cmd.UnionFree c
  | _, [], _ => by simp [ruleProofDecls]
  | G, c :: cs, i => by
      intro d hd
      rw [ruleProofDecls] at hd
      rcases List.mem_append.mp hd with h | h
      · obtain ⟨r, -, rfl⟩ := mem_proofDeclOf h
        exact unionFree_decl_none rfl
      · exact ruleProofDecls_unionFree P _ cs _ d h

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
  · exact ruleProofDecls_unionFree _ _ _ 0 c h
  · exact unionFree_decl_merge rfl
  · exact unionFree_decl_none rfl
  · exact unionFree_decl_merge rfl
  · exact unionFree_decl_noMerge rfl
  · exact allMaintenanceRules_unionFree P r hr

theorem encodeRule_actions (i : Nat) (r : Rule) (n : Nat) :
    (encodeRule i r n).1.actions
      = (encodeActions (ruleE i (queryProofs (encodeQuery r.query n).1)) r.actions
          (encodeQuery r.query n).2).1 := rfl

theorem encodeCmd_action_fst (G : List (Var × Expr)) (a : Action) (n i : Nat) :
    (encodeCmd G (.action a) n i).1
      = (encodeAction fiatE a n).1.map .action ++ [.saturate rebuildRuleset] := rfl

theorem encodeCmd_rule_fst (G : List (Var × Expr)) (r : Rule) (n i : Nat) :
    (encodeCmd G (.rule r) n i).1 = [.rule (encodeRule i (r.substGlobals G) n).1] := rfl

theorem encodeCmds_cons_fst (P : Program) (G : List (Var × Expr)) (c : Cmd) (cs : Program)
    (n i : Nat) :
    (encodeCmds P G (c :: cs) n i).1
      = (encodeCmd G c n i).1 ++
        (encodeCmds P G cs (encodeCmd G c n i).2.1
          (encodeCmd G c n i).2.2).1 := rfl

/-- Every command the encoding of one source command emits is union-free. -/
theorem encodeCmd_unionFree (G : List (Var × Expr)) (c : Cmd) (n i : Nat) :
    ∀ d ∈ (encodeCmd G c n i).1, Cmd.UnionFree d := by
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
    change Actions.UnionFree (encodeRule i (r.substGlobals G) n).1.actions
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
theorem encodeCmds_unionFree (P : Program) :
    ∀ (G : List (Var × Expr)) (p : Program) (n i : Nat),
    ∀ d ∈ (encodeCmds P G p n i).1, Cmd.UnionFree d
  | _, [], _, _ => by simp [encodeCmds]
  | G, c :: cs, n, i => by
      intro d hd
      rw [encodeCmds_cons_fst] at hd
      rcases List.mem_append.mp hd with h | h
      · exact encodeCmd_unionFree G c n i d h
      · exact encodeCmds_unionFree P _ cs _ _ d h

/-- **`encode`'s output is union-free**, for every source program. -/
theorem encode_unionFree (P : Program) : Program.UnionFree (encode P) := by
  refine Program.unionFree_of_mem fun c hc => ?_
  rw [encode] at hc
  rcases List.mem_append.mp hc with h | h
  · exact encodePrelude_unionFree P c h
  · exact encodeCmds_unionFree P [] P 0 0 c h

/-- **There is nothing left to resolve in an encoded rule.** -/
theorem Rule.resolveGlobals_encodeRule {σ : Env} {G : List (Var × Expr)}
    (hcl : Expr.ClosedG G) (hat : ∀ b ∈ σ, ¬ "@".isPrefixOf b.1)
    (hcov : ∀ v, Expr.lookupG v G = none → Env.lookup v σ = none)
    (s : Rule) (i n : Nat) :
    ((encodeRule i (s.substGlobals G) n).1).resolveGlobals σ
      = (encodeRule i (s.substGlobals G) n).1 := by
  refine Rule.resolveGlobals_eq_self _ fun v hv => ?_
  have hv' : v ∈ Query.vars (encodeQuery (Query.substGlobals G s.query) n).1 := by
    rw [encodeRule] at hv; exact hv
  rcases mem_vars_encodeQuery _ n hv' with hat' | hsrc
  · refine Env.lookup_eq_none_iff.mpr fun hd => ?_
    obtain ⟨t, hb⟩ := Env.mem_dom_iff.mp hd
    exact hat (v, t) hb hat'
  · exact hcov v (Query.lookupG_eq_none_of_mem_vars_substGlobals hcl hsrc)

/-! ### Reading the target

The three notions the deleted M11 theorems were stated over. None of them is `Cong`: the
encoded program's tables are `.merge` functions and it asserts no equation but the
reflexive one `addTerm` records, so `Cong` on the target is the identity relation on the
terms it holds. Equality on the target side is *only* what `@UF` and the views record.

Rebuilding re-keys a view entry to its children's leaders, so the encoded database can
hold entries about applications the source never built. Such an entry does not establish
that both endpoints existed in the source. `encode_corresponds` therefore requires
membership in `src.terms` before comparing this reading with source `Cong`. -/
/-- A union-find edge that moves. The `:merge` writes `@UF (ordering-max p p) ↦
(ordering-min p p, _)` on a self-collision, so reflexive self-loops are ordinary entries and
a leader is "no edge that moves" rather than "no entry".

Existential in the proof column: which justification an edge carries is not what being an
edge means. -/
def UFEdge (d : Database) (t p : Term) : Prop :=
  (∃ pf, d.Out ufName [t] [p, pf]) ∧ p ≠ t

/-- `l` is `t`'s representative: reachable along edges, and itself at the end of one.

A relation rather than a function because `Database.Out` reads *any* recorded output —
the model keeps the entries a merge displaces (`MERGE.md`, "The executable row index"),
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
step changes anything. `encode` schedules `Cmd.saturate rebuildRuleset`, and
`saturateReach_rebuilt` derives this condition from its post-state.

`identityVals := some 1` prevents proof-only changes from making saturation impossible.
`Encoding/Correspond.lean`'s `satProgram_programStep` provides a reachable witness. -/
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
