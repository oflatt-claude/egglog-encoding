# M11, the proof encoding — parked

`Encoding/Encode.lean` defines the encoding. Its *original* theorems and their vacuity
witnesses are **deleted**; this file is what survives of them, and it exists so the design is
not re-attempted with the same defects.

**One statement is back, and it is stated where it can be measured.**
`Encoding/Complete.lean` has `encode_corresponds` — `Cong src a b ↔ SameClass tgt a b` —
over `Encoding/Correspond.lean`'s decision procedure `sameClassF`, the proof that the two agree
(`sameClassF_iff`, both directions, no `sorry`), and a compiled witness that its hypotheses
are jointly satisfiable at a state where both sides of the `iff` are non-trivial
(`encode_corresponds_witness`). `difftest correspond 64` sweeps exactly that relation over
the corpus and reports 70 of 70 agreeing, 0 LOST, 0 INVENTED, 0 `link-diff`. **One half of the
`iff` is proved outright** — `encode_corresponds_complete`, no `sorryAx` — and the theorem
carries `sorry` only through the *forward* half, in two named properties of the state the run
reached; they are two *mechanisms* rather than two clauses, because the clauses are derived
from one another.
The **action read-back** is proved (`holdsBuild_of_execProgramM`,
`viewRepr_self_of_execProgramM`) and so is the **induction over `encode P`'s commands** built
on it (`UnionsInv`, `unionsInv_execM`), which closes `execM_unionsJoined` and supplies the
totality `Database.ViewsCover` is derived from. Of the two left, one is that induction's own
open case (`unionsJoined_fire`: a source command that fires rules needs a target firing behind
the source's, and one step below that the premise row must be current in the *index*, not merely
an entry term) and one is the run-wide index argument itself (`execM_viewLeaderRows`: the
rebuild's e-class rule, its column rules and path compression).

**The completeness half is closed.** `Encoding/Complete.lean`'s `execM_soundTerms` — every term
the run adds, justified against the source — is proved, and `encode_corresponds_complete` with
it. The **merge phase** is `mergeSaturateF_soundTerms`, out of `mergeOneOriented_soundTerms`,
with the two facts it needed: `Signature.MergeShape` (only `@UF` and the views carry a `:merge`
body, and both carry `mergeBody`) and `eq_of_congrKeys` (against a diagonal closure, congruent
keys are equal keys). The fold over **rule firings**, the per-command induction and the head
obligation under it are `execRunRules_soundTerms`, `FDatabase.EncOk.stepCmds` and
`encodedHeadSound`. `encode_corresponds_complete_witness` is the closed statement at a pair
both sides really relate — `(F (A))` and `(F (B))` at `ncProgram`, two distinct source e-nodes.

**It took one further domain clause, and the clause is faithfulness rather than a narrowing.**
`encodeBuild` emits no action at all for a **leaf**, so a rule head that builds a bare variable
the query does not bind stops the *source* block at that action while the encoded block skips it
and runs the rest of the head — a third shape of stuck head beside the two
`Encoding/Encode.lean` names. `bare_build_invents_equality` is that at `bareProgram`: the source
relates `(A)` and `(B)` in no way and the encoded run puts them in one class, so
`encode_corresponds_complete` **itself** was false there, at a pair of source e-nodes.
`EncodeDomain.headsScoped` — `Program.HeadsScoped`, every variable a rule head reads is one its
own query binds — is the clause that excludes it, and
`bareProgram_encodeDomain_but_headsScoped` is every *other* clause holding of that program, so
the clause is the only thing standing between the domain and the refutation. egglog rejects
exactly this: `to_core_actions`, the lowering for actions, resolves a `GenericExpr::Var` only
when `ctx.binding` holds it or it is a global, and raises `TypeError::Unbound` otherwise
(`egglog/src/core.rs:663-670`) — a different error from `UnboundFunction`. The census is
unmoved: still 70 of 166 in domain, and `DiffTest.lean` pins that.
**Two clauses this factorisation used to run through are
refuted** and kept as records — `Database.ReadsSelf` (every source term is an id of itself) and
`Database.ViewsProduct` (a view entry at every id tuple the children form), both false at
`ncProgram`'s state because a source rule fires once per class *member* while the encoded rule
reads rows that sit at the union-find leader (`ncTgt_not_readsSelf`, `ncTgt_not_viewsProduct`,
and the same two with the encoded run as a hypothesis). What replaced them is what their
consumers actually spend: `Database.ViewsCover.shared`, one *shared* id tuple with an entry
keyed at it, and `Database.UnionsJoined`, the `@UF` edge between the endpoints' *ids* — both
holding at that same state (`ncTgt_shared_FB`, `ncTgt_unionsJoined`), with the rebuild's
edge-following moved into `Database.ViewLeader.ufClosed`. The first of the two is now *derived*
rather than assumed: the tuple it answers with is always the union-find leader's, so
`Database.ViewsCover.of_viewLeaderRows` gets it from a row-transport clause and totality, and
`ncTgt_viewsCover` runs that reduction at the very state the product form fails at. Two of
those clauses were once *false* at `.action (.expr (.lit 5))`, and the defect was
`ViewRepr`'s literal clause asking the target to hold the literal: egglog mints no e-node for
one. Without the premise the clause `Program.EncodeDomain.noBareBuild` added is gone, that
program is in the domain, and both statements hold there
(`litBuild_viewsCover`, `litBuild_unionsJoined`); the reading stays exact because a literal's
only id is itself (`ViewRepr.eq_of_lit`, `not_sameClass_lit_app`). Still 70 of 166 in domain.
Finding 3 below
is why its target is the interpreter's state and not `ProgramStep`'s — the vacuity is gone,
but the decision procedure still needs an `FDatabase` — and finding 4 is why the `iff` is
stated at `a ∈ src.terms` and `b ∈ src.terms`.

One thing has since moved in M11's favour, and it is the reason to restate rather than
abandon: the congruence obstruction that constrains the refinement chain on *source* programs
provably does not arise on encoded ones, and the hypothesis the chain was finally proved under
is one `encode` satisfies — "What survives", last three paragraphs.

The Lean is recoverable at commit `0836127`:

```
git show 0836127:semantics/EgglogSemantics/Encoding/Proofs.lean   # 13 statements, all sorry
git show 0836127:semantics/EgglogSemantics/Encoding/Rebuilt.lean  # the vacuity witnesses
```

They were deleted rather than carried through the `Spec/` simplification work: both are
row-shaped throughout — `Spec/` has no rows now, a function entry is a term — the
statements are known defective, and porting proofs of nothing is not worth the maintenance.

## Four findings, each machine-checked

The first two were checked before the theorems were deleted; the third and fourth are checked
in `Encoding/Correspond.lean` and are what the restated theorem ran into. The third is
closed; the fourth moved the statement.

### 1. `Rebuilt` was unsatisfiable at the states `encode` ran to — **fixed**

`Rebuilt P d` is the saturation hypothesis `encode_complete`, `encode_simulation` and
`encode_simulation_of_domain` all carry. It is satisfiable for some states and not for the ones
that matter. Two source programs differing only in *which* term is built:

* `P₁ = (f 1) (union 1 2)` — the union's larger endpoint `2` is not a view key, so the
  rebuild has nothing to move. `Rebuilt P₁ d₁` holds.
* `P₀ = (f 2) (union 1 2)` — the larger endpoint **is** the view key. The column-0 rebuild
  rule has a firing that writes a row the state lacks, and neither an action nor a merge
  step can ever write it, because `encode P₀` emits no `Cmd.run`. `¬ Rebuilt P₀ d₀`.

The general form: **any** state satisfying `Rebuilt` must already hold every re-keyed view
row. A hypothesis nothing reachable satisfies makes the three theorems it guards vacuous.

**Appending `(run)`s does not work**, and that was the whole difficulty: the number of
rounds needed to re-key grows with term depth, so no fixed number of `(run)` commands
saturates for all inputs. The fix had to run to saturation.

**Repaired by rulesets.** `Spec/Step.lean` now has `Cmd.saturate R`, whose postcondition
is `RunSaturated R` — the ruleset at a fixpoint and no merge step left. The maintenance
rules join `rebuildRuleset` and `encodeCmd` emits `Cmd.saturate rebuildRuleset` after
every run, so `Rebuilt` is now a *postcondition* rather than a hypothesis:
`Encoding/Encode.lean`'s `saturateReach_rebuilt` and `cmdStep_rebuilt`. One flat ruleset
suffices where egglog nests three, because a fixpoint of a union of rulesets is a fixpoint
of each.

The proof column then undid the repair one level down, and finding 3 is that and its fix:
both halves of `RunSaturated` are reachable now, `satProgram_programStep` compiled.

### 2. `CongOn` cannot express existence

`CongOn db ts a b` is definitionally `Cong (db.addTerms ts) a b`, so
`CongOn db [a, a] a a` holds for **every** database and **every** term — no
well-formedness, no membership, no signature, no program. The witness, `congOn_refl`, was one
line.

**It survived `Cong` losing its `refl` rule**, which is worth checking rather than
assuming, since that deletion is what re-examined every other reflexivity guard
(`Proofs/Counterexamples.lean`). `Database.addTerm` writes a reflexive *equation* per subterm,
so `(a, a) ∈ (db.addTerms [a, a]).eqs` and `Cong.assert` reads it straight back.

Five of the M11 statements conclude `CongOn`, so each says nothing wherever its two terms
coincide. That is not a corner case. `encodeBuild` emits
`.set (viewName f) es [.app f es]` — an **identity** view row, key and output denoting the
same term — for every application it encodes. So `encode_rows_sound`'s second conjunct, at
the most common row in the target, reduces to `congOn_refl` and is dischargeable without
looking at the source, the program, the target, or the row. Likewise
`encode_proof_view_rows_check` at a two-column identity row, and
`encode_rows_sound`'s first conjunct at a `@UF` row whose key is its own parent — which
every interned term is until something unions it.

`Encoding/Correspond.lean`'s `SameClass` avoids the trap a third way: it is an existential
over view entries, so its diagonal `SameClass d a a` says "the target gives `a` an id",
which is exactly the e-node correspondence and is false for most terms. The sweep's
`agree-true` column (778 over the corpus, 159 of them off the diagonal) is what says so.

**Do not "fix" this by replacing `CongOn` with `Cong`.** `CongOn` is the right relation
for the job it was introduced for: after `(Add 1 2)` and `(union 1 2)` the rebuild re-keys
`@AddView [1,1] ↦ Add[1,2]`, and `CongOn src [Add 1 1, Add 1 2] (Add 1 1) (Add 1 2)` is a
true, non-vacuous claim that `Cong src` cannot even state, because `Add 1 1` was never
built and every term `Cong src` relates is one `src` holds (`eqsInTerms_free`). The defect
is confined to the diagonal. Two repairs that keep what `CongOn` is for:

* **conjoin membership** — `k ∈ src.terms ∧ p ∈ src.terms ∧ Cong src k p`. This is what
  makes the diagonal say something, and it is now *definitional*: `Database.terms` is
  `{t | Cong db t t}`, so `Cong src a a` and `a ∈ src.terms` are the same proposition.
* **split the cases** — `CongOn` only where the rebuild has re-keyed, `Cong` elsewhere.

### 3. `MergeSaturated` counted the proof column, so nothing was `Rebuilt` — **closed**

`Spec/Step.lean`'s `MergeSaturated db` is "no merge collision *changes* anything", and it is
phrased that way because **every entry collides with itself** — "no step applies" is
unsatisfiable at a `:merge` with no block. With a proof column a self-collision changed
something. `mergeBody` writes

```
@UF (ordering-max old0 new0) ↦ (ordering-min old0 new0, @Trans (@Sym hi_pf) lo_pf)
```

and at a self-collision `old0 = new0 = v`, `old1 = new1 = pf`, so it wrote the self-loop
`@UF(v) ↦ (v, @Trans (@Sym pf) pf)` — a term one composition **larger** than the proof it
started from. A `MergeSaturated` state had to hold that entry, and that entry's own
self-collision the next one: the whole tower. No state with finitely many terms holds it, so
nothing that had built one term was `MergeSaturated`, `Rebuilt P d` was unsatisfiable, and so
was `ProgramStep Database.empty (encode P) tgt` for every `P` that builds a term.

It was a **specification/implementation gap, not an encoder bug**. `viewDecl` and `ufDecl`
declare `identityVals := some 1`, which takes the proof column out of the change test, and
`Impl/Merge.lean`'s `noConflict` read it where `MergeStep` did not.

**The fix is in `Spec/Step.lean`.** `MergeConflict decl body a b` is `noConflict` negated —
`a.take k ≠ b.take k` at `identityVals := some k`, and `body = [] ∨ a ≠ b` without one — and
`MergeStep.collide` carries it as a premise. A self-collision at either encoded table is
therefore not a step, and `Encoding/Correspond.lean` carries the two witnesses, both
`sorry`-free: `refutationState_mergeSaturated` (the state the refutation used to be
instantiated at, now merge-saturated) and `satProgram_programStep`, a compiled
`ProgramStep Database.empty (encode P) tgt` for a `P` that builds a term, with both fixpoint
conditions of the trailing `Cmd.saturate rebuildRuleset` discharged.

**What it cost, in `Spec/Scope.lean`.** `MergeConflict` compares value tuples by identity,
which is not stable under congruence, so `MergeStep.transport_owes` — the ordering-free arm
of `execM_contained`'s side condition — cannot move a firing onto congruent values unless the
test is constantly true. `Signature.OrderingFree` is now the fragment where a merge reads
nothing congruence-unstable: `FnDecl.OrderingFree` adds `identityVals = none`, and
`MergeSpec.OrderingFree` asks `body = []` in place of `Actions.OrderingFree body`. That keeps
every `:merge` *expression*, which is what that arm was described as covering; it drops
`:merge` **action blocks** from it. `encode`'s own output takes the union-free arm, so nothing
in M11 is affected.

`encode_corresponds` still carries `execM (encode P) = some tgt`, for a different reason than
before: the hypothesis has to name the state the corpus sweep decides, and `sameClassF`,
`FDatabase.SubtermClosed` and `FDatabase.EqsRefl` are all `FDatabase`-shaped where
`ProgramStep` mentions a `Database` and a family of them.

The shape of the defect is the same as finding 1's and it was found the same way: by
insisting on a witness before accepting a `sorry`.

### 4. The unrestricted `iff` was false, and finding 2 said where — **statement moved**

Finding 2's own example is the counterexample, one step further on. The rebuild's column
rules re-key `@AddView [1,2]` onto `@AddView [1,1]` after `(union 1 2)`, so `(Add 1 1)` reads
an id — and `Cong src` relates `(Add 1 1)` to nothing at all, its own self included, because
`Cong.congr` wants both sides self-congruent and no other rule produces an application. So

```
SameClass tgt (Add 1 1) (Add 1 1)   holds
Cong src   (Add 1 1) (Add 1 1)      does not
```

and `SameClass tgt a b → Cong src a b` is false at `witnessProgram`, the program
`encode_corresponds_witness` is already stated over. `encode_corresponds_invents_enode` is
that refutation compiled, its two measurements decided by
`difftest correspond-selftest`'s witness case.

**Why the sweep is green anyway, and what it therefore measures.** `difftest correspond`'s
universe is `src.terms ++ tgt.terms`, and `(Add 1 1)` is in neither: it is a *key tuple* of an
entry term, not a subterm of one, and nothing writes it into either term set. So the sweep
never puts it on a pair, and its 0 INVENTED is a claim about the two databases' e-nodes — which
is exactly what the statement now says.

**The repair is finding 2's own first repair**, "conjoin membership": both halves of
`encode_corresponds` are stated at `a ∈ src.terms` and `b ∈ src.terms`. `Cong src a b` implies
both, so the forward half pays nothing for them. The alternative — conclude
`CongOn src [a, b] a b`, which the invented e-node does satisfy — is finding 2's second
repair and is *not* taken: it would leave the two halves of one `iff` quantified over
different sources.

**And it is not a defect in `encode`.** The entry the rebuild wrote is true of the terms it is
about; what was defective is stating the correspondence as an unrestricted `iff`.

## The rebuild has no fixpoint, and every proof-side repair is dead

`Encoding/Match.lean` carries the statement: `uf_row_succ` and `uTgt_saturate_infinite` say
that after a `union` between two distinct built terms, `Cmd.saturate rebuildRuleset` can only
reach a state holding an injective image of `Nat`. One turn of the crank re-keys the `@UF` row
through a *stale* view row; the collision that makes is not a self-collision, so
`identityVals := some 1` does not disarm it; and `mergeBody` settles it at a proof one
composition larger — proof sizes 6, 11, 16, 21, … from the `@Fiat` the `union` wrote. Its
docstring has the four steps.

Four repairs to the proof vocabulary have been investigated and all four are dead. **The
characterisation is the part worth keeping**, so it comes first.

### Proofs are paths, so normalisation is path reduction

A proof term denotes a walk in the graph whose nodes are terms and whose edges are the steps
something puts there: an asserted `union`, a rule head's `union`, and one congruence edge per
constructor position. `@Sym` reverses a walk, `@Trans` concatenates two, `@Congr_k` lifts `k`
walks through a constructor. Cancellation — `@Trans (@Sym p) (@Trans p r) → r` and its mirror
— quotients out backtracking, so a normal form is a **reduced walk**. The reduced walks
between two nodes are the cosets of the graph's fundamental group: one per pair when the graph
is a forest, and **infinitely many as soon as the graph has a cycle**. So a canonical proof per
proposition exists exactly on forests, and on nothing else.

Two data points, both checked against a spec-faithful harness (`Term.blt` and `bltList`
comparing whole terms, `mergeBody`/`mergeResult`/`loPfE`/`hiPfE`, and `pathCompressRule`
plus `rebuildRules`' e-class and column rules transcribed; validated against `uf_row_succ`'s
tower):

* The **tower** is a forest — `union A B` at two nullary constructors is two nodes and one
  edge — and identity collapse alone converges on it, in one round.
* `(F A) (F B) (union A B)` **with a rule** `(F x) ⇒ (union (F x) x)` is not. Its nodes are
  `A`, `B`, `F(A)`, `F(B)`; its edges are `A–B` asserted, `A–F(A)` and `B–F(B)` from the rule
  head, and `F(A)–F(B)` by congruence. Four nodes, four edges, connected, so cycle rank
  `4 − 4 + 1 = 1`. It is the one shape of fourteen that **no** law set converges on — all nine
  tried, including the maximal unsound one, in both the shared-`@Fiat` and the
  per-assertion-`@Fiat_j` reading.

**Rebuild convergence is weaker than canonicity, and the harness says so in both directions**,
which is why the forest condition is a statement about normal forms and not a decision
procedure for termination:

* A forest is not sufficient. `(F A) (F B) (union A B)` without the rule is a forest — nodes
  `A, B, F(A), F(B)`, edges `A–B` and `F(A)–F(B)`, cycle rank 0 — and **no cancellation-free
  law set converges on it**. Reaching the canonical walk needs cancellation, which is the
  unsound fragment below.
* A cycle is not fatal. `A B C` with all three of `(union A B) (union B C) (union A C)` is a
  triangle, cycle rank 1, and it converges under cancellation: the rebuild composes only the
  walks its own three rules compose and never enumerates the coset.

What makes the cycle-rank-1 shape fatal is *which* edge closes its cycle. `F(A)–F(B)` is a
**congruence** edge, and the column rule re-derives it every round from the round's current
proof, wrapping it in `@Congr_1`. So the round-`n+1` proof carries a round-`n`-shaped proof
one `@Congr_1` deeper — 14 symbols to 99 in one round under the sound law set — and no law
that keeps `@Congr_k` meaningful can strip the wrapper. The successor is not literally the
predecessor plus a constructor, because normalisation reshuffles the interior; the invariant
is the nesting depth, and it grows by one per round.

**Consequence: the only proof-side cure is proof irrelevance**, and proof irrelevance is not a
rewrite system. The two designs that remain are therefore changes to what `Spec/Step.lean`
counts as a *step*, not to the proof vocabulary — last subsection.

### 1. Identity collapse — fixes only forests

`@Trans @Refl q → q`, `@Sym @Refl → @Refl`, `@Congr_k @Refl … → @Refl`. The vocabulary
has no `@Refl` to collapse — `encodeBuild` writes `fiatE` in every view row — so this is
"add one, and collapse it", and the harness is *generous* to the candidate by modelling it.
Even so it converges on four of fourteen shapes, and all four are forests. It is not a
sufficient condition on forests: the forest above defeats it.

### 2. A pinned proof table (`:merge old`) — fails, and is worse

egglog's own `<S>Proof` is `:merge old` (`egglog/src/proofs/proof_encoding.rs:617,685`), which
suggests pinning the proof column into a sidecar table that never composes. It does not
transfer, for two reasons.

**egglog's pinned table is not carrying the interesting proof.** `<S>Proof` holds a
*reflexive anchor*, read only as a fallback when a term has no `@UF` row
(`proof_container_rebuild.rs:50-56`: `uf_canon_proof` returns "the `@UF_<S>` row's proof
`term = leader`, or `fallback`", and the caller passes `<S>Proof(term)`). egglog still composes
in `ordered_union_merge` — `@Sym(hi_pf) ; lo_pf`, the same skeleton as `mergeBody` — and in
`path_compress` — `@Trans pb pc`. What actually terminates egglog's rebuild is
`(delete (view keys))` in `proof_encoding_rebuild.rs` (lines 55-56, 151, 318, 363, 405): the
displaced row is *removed*, so there is no stale row to fire against next round. `Spec/`'s
`terms` never shrinks, which is the whole gap.

**And simulated, it is worse than the status quo.** `:merge old` is a don't-add, not a remove,
and `Database.Out` is existential — `∃ bs, CongList db as bs ∧ Term.app f (bs ++ vs) ∈ db.terms`
— so every historical proof at a key stays readable and every reader multiplies over all of
them. It fails all three shapes tried. On chained unions (`X Y Z`, `(union Y Z) (union X Y)`)
it adds 6, 6, 13, 51, 263, 1633 rows per round, where the status quo adds one.

### 3. `rewrite` rules over the proof tables — cannot remove, and would break a proved theorem

Four independent refutations, any one sufficient.

* A `rewrite` **desugars to a `union`** (`egglog/src/ast/desugar.rs`, `desugar_rewrite` emits
  `Action::Union`), so it equates the big proof with the small one and leaves both in `terms`.
  Equating is not removing, and it is removal the fixpoint needs.
* It fires only once the bad term exists, so it is a round behind the rule that made it.
* The colliding column is the **e-class**, not the proof: `MergeConflict` at
  `identityVals := some 1` compares column 0, and the tower's growth is in column 1. Making
  two proofs equal does not stop the collision that mints them.
* `encode` would stop being union-free, which falsifies the *proved* `encode_unionFree`
  (`Encoding/Encode.lean`, axioms `[propext, Quot.sound]`). That is load-bearing: it is what
  makes every state an encoded program reaches diagonal, hence `Cong` on the target the
  identity on the terms it holds, hence `Database.Out` a syntactic lookup — which is exactly
  what `Encoding/Match.lean`'s `out_of_matches_values` needs, and what puts `encode` in
  `execM_contained`'s union-free arm.

### 4. Normalise on build, via a `Prim` — sound fragment insufficient, sufficient fragment unsound

The sound fragment is `@Sym`/`@Trans`/`@Congr_k` bookkeeping — `@Sym (@Sym p) → p`,
`@Sym (@Trans p q) → @Trans (@Sym q) (@Sym p)`, associativity, identity collapse, and
`@Congr_k` distribution. It converges on four of fourteen shapes. The tower's own shape and
the forest above are both outside it.

The sufficient fragment adds cancellation and reaches thirteen of fourteen — and is
**unsound**, refuted on two lines. Take `(union B D) (union C D)` with `B < C < D` under
`Term.blt`. Both edges key at `@UF(D)`, so they collide; `mergeBody` writes
`@Trans (@Sym @Fiat) @Fiat`; cancellation reduces that to the identity; and the settled row is
`@UF(C) ↦ (B, @Refl)`, a claim that `C = B` which is neither asserted nor reflexive. The
checker refuses it whichever way the identity is spelled: `@Refl` is not one of
`Checker.lean`'s node kinds at all, and at `@Fiat` `props` offers `C.eqs` filtered by the
endpoints plus `reflProps`, and `(C, B)` is in neither. So the state carries a row no proof
justifies. Cancellation is unsound precisely because `@Fiat` is **non-functional**: one
nullary node stands for every assertion, so `@Trans (@Sym @Fiat) @Fiat` looks like a round
trip along one edge when it is a path along two.

**Per-assertion `@Fiat_j` does not rescue it.** Indexing the constant by the assertion repairs
that counterexample — `@Trans (@Sym @Fiat_1) @Fiat_0` no longer cancels — and repairs the two
unjustified rows the audit finds on the triangle as well. It changes **zero** convergence
cells: all fourteen shapes × nine law sets are bit-identical between the shared and indexed
readings. And it does not restore cancellation's soundness, because `@Rule_i` is non-functional
for the same reason: `Checker.lean`'s `headEqs` is multi-valued per head, so a head asserting
two `union`s that share their maximal endpoint gives both `@UF` edges the *same* proof
`@Rule_0(pf)`. On `(F x) ⇒ (union (F x) B) (union (F x) C)` with `B < C < F(A)`, cancellation
produces `@UF(C) ↦ (B, @Refl)` again, with `@Fiat_j` on. Indexing `@Rule_i` per head action
would meet the same wall one level up: any proof constructor whose denotation is a *set* of
propositions makes `@Trans (@Sym p) p` mean less than it looks like.

### What is left, and it is not in the proof vocabulary

Both remaining designs change `Spec/Step.lean`'s notion of a step.

* **A re-derived equality is not a change.** A row's identity is `(key, e-class)` and the proof
  is metadata: `MergeConflict` already reads only the counted columns, and this extends the
  same idea to `RunRules`, so a firing that re-proves a row the state holds is not a firing
  that changes it. This is proof irrelevance at the level of the state, which is where the
  characterisation above says it has to live.
* **The rebuild replaces rather than accumulates.** A fifth field, `entries : Set Term`, with
  `Impl/Interp.lean`'s `toDatabase` setting `entries := rows`, is egglog's `(delete (view keys))`
  in the specification. `Database.Contained` and `Database.Recorded` are stated on `eqs` alone
  (`Spec/Database.lean`, `Spec/Congruence.lean`), so `execM_contained` and both `Recorded`
  transports survive verbatim; what changes is which table reads see the displaced row.

## The lesson worth keeping

All four defects were invisible while the statements carried `sorry`. A statement nothing
discharges can be trivially true without anyone noticing, and two of thirteen were; a
statement nothing discharges can equally be *false* without anyone noticing, which is finding
4. Before proving an M11 statement, check that it is not already provable for the wrong reason
— `#print axioms` on a hypothesis-free proof of the conclusion is the cheap test — and check
its conclusion at the witness, which is the test finding 4 came out of.

**And check the other direction too.** `encode_corresponds` is an `iff`, which is trivially
true if `SameClass` is accidentally always false, so `encode_corresponds_witness` exhibits a
pair both sides say yes to as well as a pair both say no to, and `CorrReport.agreeTrue` is
that measurement over the corpus. Finding 3 came out of the first half of the same
discipline: the hypotheses were checked for joint satisfiability before the `sorry` was
allowed to stand, and they were not.

One more of the same kind is recorded but unswept: the remaining eleven original statements
were never checked for vacuity.

## What survives

`Encoding/Encode.lean` — `encode`, `encodeBuild`, `maintenanceRules`, `Rebuilt`,
`EncodeDomain`, `viewName`/`termName`/`ufName`, `rebuildRuleset`. The encoder's definitions
depend on none of the deleted files. `Rebuilt` is now reachable — see finding 1 — and the proofs
the file carries are the three payoff theorems next to it and `encode_unionFree`.

**A third obstacle, and it is unrepairable in general.** `mergeBody`/`mergeResult` — the `:merge`
shared by `@UF` and every view — are built from `ordering-min`/`ordering-max`, hence from the
`ordering-gt` inside them, which is **not congruence-stable**, and no operator is: the
obstruction is that a choice operator has to commit to a side, not that `Term.blt` reads
structure, so e-class ids, a class minimum, a database-aware primitive and a new operator baked
into the language fail alike (`MERGE.md`, "The representative deviation"). It bites this encoder
concretely rather than abstractly: an unrestricted `MergeStep.transport_recorded` is **false**,
refuted at `mergeBody` itself (`transport_recorded_false`, with both states well formed and
`A.Recorded C`). The specification's collision keeps one parent, every collision the
implementation can run keeps another, and a `MergeStep` **asserts no equation** — the union-find
edge is a *term*, `@UF(max, min, pf)`, and `.set` records reflexive pairs only — so the two
candidate parents are exactly as unrelated after the merge as before. That refutes the "any
consistent choice of parent induces the same equivalence" argument at its root: the union-find
does not absorb a different choice.

The lemma that carries that name today is the *restricted* one: it takes
`C.Diag ∨ Signature.OrderingFree C.sig`, and each arm proves it — the first by the collapse below,
the second at `MergeStep.transport_owes`. The refutation is why the hypothesis is there, and it
stands against dropping it. It is in the tree and `lake build` checks it:
`Proofs/Counterexamples.lean`'s `transport_recorded_false`, `transport_recorded_false'` — the same
with `C.WF` added, which the counterexample also satisfies — and `recorded_iff_subset`, the positive
companion. Axioms `[propext, Classical.choice, Quot.sound]` for the two refutations, and
`[propext, Quot.sound]` for `recorded_iff_subset`.

**The M11 side condition, restated — and it is now the delivered hypothesis, not just an
observation.** `encode` emits only `.set` and `.letBind`, never `.union`; a source `union` becomes a
`.set @UF …`. So from `Database.empty` the target's `eqs` is diagonal-only, and `Cong` on the target
is the **identity on the terms the target holds** — not "syntactic equality", which was the old
phrasing and is wrong now that `Cong` has no `refl` rule. `Cong` reads `eqs` and nothing else, so no
table of the target can add a derivation. It is the one M11 side condition that survived both the
congruence collapse and the deletion.

**What it is worth has grown, and this is the finding to restate M11 around.** On a diagonal state
`Database.Recorded` **is** `Database.Contained` — nothing is congruent-but-distinct, so a re-keying
has nothing to hide behind. That is a library theorem now, `Database.Recorded.contained_of_diag`,
and it is what proves the two surviving `Recorded` transports, which accordingly carry `C.Diag`. By
the side condition every state an encoded program reaches is diagonal, so **a restated M11 can use
those transports directly**, with no congruence-stability hypothesis; and `encode`'s output lands in
the same arm as `execM_contained`'s `p.UnionFree`, the exact hypothesis under which that theorem is
proved — `encode` uses `ordering-max` *inside a rule action*, so it would fail an ordering-free
hypothesis and passes a union-free one. (`encode_unionFree`, in `Encoding/Encode.lean`, is that by
compiled proof, axioms `[propext, Quot.sound]`.) The refutations are not thereby harmless —
they say where the danger lives, which is a *source* program combining a `union` with a user
`:merge` that calls `ordering-min`. A restatement that stays on encoded programs never meets one;
one that quantifies over source programs must.

The proof checker was never written. `CHECKER.md` scopes it; `Checks` was an opaque
stand-in in the deleted statements.
