# M11, the proof encoding — parked

`Encoding/Encode.lean` defines the encoding. Its *original* theorems and their vacuity
witnesses are **deleted**; this file is what survives of them, and it exists so the design is
not re-attempted with the same defects.

**One statement is back, and it is stated where it can be measured.**
`Encoding/Correspond.lean` has `encode_corresponds` — `Cong src a b ↔ SameClass tgt a b` —
together with the decision procedure `sameClassF`, the proof that the two agree
(`sameClassF_iff`, both directions, no `sorry`), and a compiled witness that its hypotheses
are jointly satisfiable at a state where both sides of the `iff` are non-trivial
(`encode_corresponds_witness`). `difftest correspond 64` sweeps exactly that relation over
the corpus and reports 70 of 70 agreeing, 0 LOST, 0 INVENTED, 0 `link-diff`. The theorem
itself carries `sorry`, in four named obligations; finding 3 below is why its target is the
interpreter's state and not `ProgramStep`'s — the vacuity is gone, but the decision procedure
still needs an `FDatabase`.

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

## Three findings, each machine-checked

The first two were checked before the theorems were deleted; the third is checked in
`Encoding/Correspond.lean`, is what the restated theorem ran into, and is now closed.

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

## The lesson worth keeping

All three defects were invisible while the statements carried `sorry`. A statement nothing
discharges can be trivially true without anyone noticing, and two of thirteen were. Before
proving an M11 statement, check that it is not already provable for the wrong reason —
`#print axioms` on a hypothesis-free proof of the conclusion is the cheap test.

**And check the other direction too.** `encode_corresponds` is an `iff`, which is trivially
true if `SameClass` is accidentally always false, so `encode_corresponds_witness` exhibits a
pair both sides say yes to as well as a pair both say no to, and `CorrReport.agreeTrue` is
that measurement over the corpus. Finding 3 came out of the first half of the same
discipline: the hypotheses were checked for joint satisfiability before the `sorry` was
allowed to stand, and they were not.

A fourth of the same kind is recorded but unswept: the remaining eleven original statements
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
