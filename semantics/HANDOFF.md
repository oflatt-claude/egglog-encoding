# Handoff

What is done, what is stated but unproved, what is known false, and what to do next.
[`PLAN.md`](PLAN.md) has the design rationale and milestones; this file has the state and
the queue. Read [`README.md`](README.md) first for the layout.

## State of play

`lake build` is clean (718 jobs).

**19 `sorry`s, in two files:** 13 in `Proofs/Encode.lean` (M11 — every statement there is
unproved on purpose, the statements *are* the deliverable) and 6 in `Proofs/Merge.lean`,
all six on the "known false" list below.

**The `execM` refinement chain is 17 of 17 proved**, including `execM_contained`. That took
a one-line change to `Spec/Merge.lean`: `CmdStep.action` now carries a `MergeClosure` phase,
because egglog resolves a `:merge` collision at a top-level `set` with no `(run)` — see
"The merge phase" below for the evidence.

**Nine of the seventeen were false as stated.** They now carry repaired statements, and
every refutation has a compiling witness in `Proofs/Counterexamples.lean`, so they are
checked by `lake build` rather than asserted in prose. Three of the nine were wrong in ways
their already-proved M10 counterparts in `Proofs/Interp.lean` had already solved:
`matchQueryM_MValidQuerySubst` lacked the `Env.Agree` that
`validQuerySubst_of_mem_matchQuery` concludes with, `patternHoldsM_MValidSubst` lacked
`patternHolds_iff`'s `ValidEnv`, and `execActions_ActionsStep` lacked `SetLegal`. **When
stating an M9 lemma, read its M10 counterpart first.** The base rate on unproved-against
statements in this development is bad; assume the M11 statements are no better.

**M11 has one known defect that is independent of the encoder being unfinished:** the
`Rebuilt` hypothesis is reachability-vacuous, so `encode_complete`, `encode_simulation` and
`encode_simulation_run` are currently vacuously true for every program that does real work.
`Proofs/Rebuilt.lean` has the machine-checked witnesses. This is the thing to fix before
anyone writes an M11 proof — see "The `Rebuilt` problem".

Two new files, both `sorry`-free and both in the build so they cannot rot:
`Proofs/Counterexamples.lean` (falsity witnesses) and `Proofs/Rebuilt.lean` (the `Rebuilt`
vacuity result).

`make lean-difftest` was **not re-run**. Nothing under `Impl/` changed and `DiffTest.lean`
is unchanged, so its last result (118 passed / 0 failed / 0 skipped, across 60 random
constructor cases, 30 random `:merge` cases and 28 curated) should still hold — but it is
inherited, not re-verified. `Spec/Merge.lean` did change; difftest does not execute `Spec/`.

Three theorems are load-bearing enough to check on every change:

| theorem | expected axioms |
| --- | --- |
| `Egglog.mcong_iff_cong` | `propext` **alone** |
| `Egglog.exec_toDatabase` | `propext, Classical.choice, Quot.sound` |
| `Egglog.mem_closure_iff` | `propext, Classical.choice, Quot.sound` |

All three hold right now. Check with `lean_verify` (lean-lsp MCP) or `#print axioms`, not by
grepping for `sorry` — it asks the kernel what a theorem actually depends on and traces into
Mathlib.

## The two contracts

`Spec/` is append-only: nothing is ever removed from `terms`, `rows` or `eqs`, and a merge
adds the combined row *beside* the two it merged. This is load-bearing — it is what makes
every monotonicity lemma hold, what lets the M11 safety theorem be an invariant needing
neither termination nor confluence, and what the encoding relies on ("proofs refer to terms
after they leave the e-graph").

`Impl/` has **two** interpreters, with two different contracts, and confusing them wastes
time:

- `exec` (`Impl/Interp.lean`) is the constructor interpreter. It has no merge phase at all.
  Its contract is an **equality**: `exec_toDatabase : (exec p).map toDatabase = run p`.
- `execM` (`Impl/Merge.lean`) is the merge interpreter. It **deletes** the rows a merge
  combined, so it is not a state the specification can reach. Its contract is
  **containment**: `execM_contained`, proved, under two side conditions (below).

`hasMergeRow_eq_false` + `mergeRound_eq_self` + `mergeSaturateF_eq_self` prove the merge
phase is the identity on a constructor-only database, which is why deletion cannot affect
`exec_toDatabase`.

Containment alone is satisfied by a do-nothing implementation, so two statements carry the
completeness weight: the constructor-fragment equality above, and
`execM_current_of_lattice` (the implementation holds the `Current` value at each key class)
for merges that are joins. For a non-lattice merge nothing is claimed — that is `MERGE.md`'s
"order-dependent merges are the user's fault".

## The merge phase runs between commands

`CmdStep.action` carries a `MergeClosure` leg:

```lean
| action {db d db' : Database} {a : Action} :
    Database.ActionStep db a d → MergeClosure d db' → CmdStep db (.action a) db'
```

Without it the specification could not reach the states `execM` reaches, and
`execM_contained` was **false** — `Proofs/Counterexamples.lean` recorded the refutation
until the spec was fixed. Checked against the release binary, no `(run)` anywhere:

```
(function f () i64 :merge (max old new))  (set (f) 1)  (set (f) 2)
→ (print-size f) = 1,   (f) -> 2
```

Swapping the merge gives `old` → 1, `new` → 2, `min` → 1, `max` → 2, so the merge *function*
really runs at the second `set` rather than last-write-wins. `print-size` and
`print-function` are both `&self` and cannot rebuild, so nothing else is doing it. The path
is `lib.rs:2101` → `eval_actions` (`lib.rs:1490`), which compiles a bare action into a
one-rule run and calls `run_rules` at `lib.rs:1508`; every rule-set run ends in `merge_all`
(`core-relations/.../execute.rs:654`). The implementation was faithful all along; the
specification was the side that was wrong.

The blast radius was four proofs in `Proofs/Step.lean` plus `CmdStep.contained`. M10 and
`exec_toDatabase` did not move, because they go through `stepCmd`/`runProgram`, not
`CmdStep`.

## The refinement chain

In `Proofs/Merge.lean`, under "The refinement chain". All seventeen proved, in this order:

1. **`FDatabase.Inv` preservation** — `empty`, `addTerm`, `addEq`, `addRow`, `execAction`,
   `mergeRound`. `Inv` is now `WF` + `CtorTerms` + `RowsComplete` + **`RowsWF`** +
   **`ctorRows`**. The last two are not decoration: without `rowsWF` a `lookup`'s result is
   an unconstrained row output and `execAction` cannot re-establish `ctorTerms`; `ctorRows`
   is `closureF_ok`'s `hrow`. `Spec/Database.lean`'s `RowsWF` docstring predicted the first
   ("belongs there once something reads it").
2. **Evaluation** — `execExpr_MEval`, `execExprList_MEvalList`, via `Out_of_mem_outs`, which
   is where `Cong.toMCong'` is spent.
3. **Actions and matching** — `execAction_ActionStep`, `execActions_ActionsStep`,
   `patternHoldsM_MValidSubst`, `matchQueryM_MValidQuerySubst`. All but the first needed a
   repaired statement.
4. **Containment** — `mergeRound_contained`, `mergeSaturateF_contained`,
   `execRunRulesM_contained`, `execCmdM_contained`, `execProgramM_contained`.

Three things this file used to get wrong about the shape of the work:

**Stages 1 and 2 are coupled.** `Inv.execAction` cannot be proved without knowing what
`execExpr` produces — that is `execExpr_ctorTerm`, which says the merge interpreter only
ever builds constructor terms (the `.union` branch's head is a constructor by the guard it
tested, a primitive returns an operand or a literal, and a `lookup` returns a row output
that `rowsWF` places in `terms`). They have to be done together.

**The transport lemma was a 5× overestimate.** `MergeStep.diamond_of_join`'s docstring
budgets 150–250 lines for an `ActionsStep` transport lemma and calls it the whole cost.
`Database.ActionsStep.mono` is ~35: an `ActionStep`'s effect is fixed by its `MEval`
witnesses, and `Expr.MEval.mono` carries those into a larger database unchanged. That is
enough for *containment*, which needs only a lower bound on the result. `diamond_of_join`
still wants the exact componentwise join and stays open.

**The legality side conditions are one condition seen from several places.** An action block
that writes a row has to be `SetLegal`, and that has to hold of merge bodies, of rule heads,
and of top-level actions. `Program.SetLegal` covers only the last, because
`Cmd.SetLegal (.decl _ _)` is `True` and so nothing constrains a declaration's merge body —
hence `Signature.MergesLegal` is carried separately. Folding it into `Cmd.SetLegal` would
let these come from `Program.SetLegal` instead of being threaded by hand.

The two program-level side conditions on `execM_contained`:

- `Signature.MergesLegal sig` — a declared merge body writes only legal `set`s.
  `Falsity.mergeRound_inv_false` is why it cannot be dropped.
- `FDatabase.ProgramLegal` — each command's head is a legal `set`, and a declaration names
  something the state does not yet mention (`FDatabase.Unused`, egglog's own
  declare-before-use). `Falsity.claim1` shows a declaration can otherwise destroy `Inv`.

Neither is vacuous: `empty.ProgramLegal` is provable for the three-command `:merge` program
that used to refute `execM_contained`, so `:merge` programs are still in scope.

The design work behind the chain is done and proved; do not redo it. `execExpr` compares
keys with `closureF`, which computes **`Cong`**, while `Database.Out` compares them with
**`MCong`**. `Cong.toMCong'` bridges that over `CtorTerms` and `RowsComplete` — which,
unlike `CtorRows`, survive a `:merge` declaration, because they constrain `terms` and the
constructor rows, and `mergeRound_confined` proves a merge touches neither.

## The `Rebuilt` problem

**This is the live M11 issue and it is not about the encoder being unfinished.** Witnesses
in `Proofs/Rebuilt.lean`.

`Rebuilt P d` is the hypothesis `encode_complete`, `encode_simulation` and
`encode_simulation_run` carry, so whether it is satisfiable decides whether those say
anything.

```lean
def Rebuilt (P : Program) (d : Database) : Prop :=
  (∀ r ∈ maintenanceRules P, ∀ d' ∈ RuleResults d r, Database.Contained d' d) ∧
    MergeSaturated d
```

**Its shape is sound.** `rebuilt₁` exhibits a state satisfying both conjuncts. Conjunct 2 is
fine now that `CmdStep.action` merges: `MergeSaturated` is "no step *changes* anything", and
the reflexive self-loop a self-collision writes is itself installed by that merge phase, so
`mergeSaturated₁` holds at a state with a genuine `@UF` edge.

**Conjunct 1 fails whenever the union does any work.** `encode P` emits no `Cmd.run` when
`P` has none, only `CmdStep.run` reaches `RunRules`, and a merge only ever re-adds a row at
an *existing* key — so a view row keyed on a non-leader can never be re-keyed.
`rebuilt_rekeys` is the general form, and needs no reachability: any `Rebuilt` state holding
`@fView [c]↦[e]` and `@UF [c]↦[x]` must already hold `@fView [x]↦[e]`. So without a trailing
`(run)`, `Rebuilt` holds **iff the union is inert with respect to every view row**, which
`Term.blt`'s orientation decides — `not_rebuilt₀` and `rebuilt₁` are the same program
differing only in which literal is built.

**The previously recorded fix does not work.** Requiring `P` to end in `(run)` swaps one
vacuous hypothesis for another. `Cmd.run` is a single round and `RunRules` fires every rule
against the pre-state, so no rule sees another's output within the round. Union chains need
a round per link; congruence propagating upward needs one per level, so **the count grows
with term depth** — and with source rules that build terms each round there may be no bound
at all.

The root cause: `Rebuilt` is a **fixpoint** condition, and the Rust reaches that state by
running a *schedule* — `(saturate (seq (run @rebuilding_cleanup) (saturate (run @parent))
(run @rebuilding)))`. The model has no rulesets or schedules, so `Rebuilt` was introduced as
a state predicate standing in for the schedule, and then nothing in the target language can
reach it. The intent is right; the target language cannot express the thing.

Three ways out, cheapest first:

1. **Restate as reachability instead of a fixpoint** — recommended, because it is the same
   move already made in M9 when `mergeRound_closure` (fixpoint) became containment
   (reachability), and it fits this development's stated preference for avoiding "cannot
   step" notions.

   ```lean
   def MaintenanceStep (P : Program) (d d' : Database) : Prop :=
     ∃ r ∈ maintenanceRules P, d' ∈ RuleResults d r
   def MaintenanceClosure (P : Program) := Relation.ReflTransGen (MaintenanceStep P)
   ```

   `encode_complete` then drops `hreb` and concludes
   `∃ tgt', MaintenanceClosure P tgt tgt' ∧ SameClass tgt' a b`. **No termination obligation
   at all**, works for `P` with rules, and `Rebuilt P d` becomes exactly "no
   `MaintenanceStep` changes `d`" — the saturation predicate of that relation, so the two
   stay connected rather than one replacing the other.
2. **Achievability lemma** — keep `Rebuilt` a hypothesis and add

   ```lean
   theorem rebuilt_reachable (hdom : P.EncodeDomain) :
       ∃ k tgt, ProgramStep Database.empty (encode (P ++ List.replicate k .run)) tgt
              ∧ Rebuilt P tgt
   ```

   Keeps both previously-rejected alternatives rejected (no `(run)` injected inside `encode`,
   no saturation predicate). Plausible for rule-free `P`, since nothing in the maintenance
   rules or the merge body creates a term — `ordering-min`/`max` return an operand, re-keying
   moves keys among existing terms — so the row set is bounded and the closure finite. For
   `P` with rules it may genuinely not exist, which is the same non-termination the source
   has and the honest place for the statement to stop.
3. **Model the schedule** — give the target language rulesets and `saturate` so `encode`
   emits what the Rust emits, making `Rebuilt` reachable by construction. Most faithful, and
   what the paper eventually wants if the model is to mirror the real schedule, but it
   touches `Spec/Syntax.lean`, `CmdStep`, and everything that cases on `Cmd`.

Two facts that simplify whichever route is taken:

- `maintenanceRules P` does not depend on how many `(run)`s `P` contains, so appending runs
  changes only the reachable `tgt`, never the predicate.
- `encode_complete`'s "runs must be appended to **both** sides" is narrower than its
  docstring claims. `mergeClosure_eq_of_allConstructors` (machine-checked) shows `MergeStep`
  never applies to an `EncodeDomain` source, so `CmdStep.action`'s merge leg is the identity
  there and trailing `(run)`s are a strict no-op on the source — for the rule-free fragment
  they can be appended to the target alone without breaking soundness.

## Known false

Do not try to prove these. Each has a machine-checked witness or a worked counterexample.

`Proofs/Counterexamples.lean` holds the compiling witnesses for the first block. Every one
keeps its `:merge` function **nullary**: that makes `congrKeys cl [] []` reduce through
`List.all []` without ever forcing `cl = closureF`, whose well-founded recursion the kernel
cannot unfold, and with that the whole interpreter down to `mergeSaturateF 64` reduces by
`rfl`. That trick is what makes concrete counterexamples about the merge phase tractable.

| statement | why |
| --- | --- |
| `FDatabase.Inv.addTerm` / `.addEq` / `.addRow` as originally stated | `addTerm` takes an arbitrary `Term`, so inserting an application of a declared `:merge` function breaks `CtorTerms`. All three now carry the constructor-term condition on what they insert. `addRow`'s `hf` was also defending the wrong field — `RowsComplete` is an inclusion, which adding a row cannot break — and now earns its keep against `ctorRows` |
| `FDatabase.Inv.mergeRound` as originally stated | a merge body is an arbitrary `List Action` with no `SetLegal` obligation, so a `(set (F) …)` inside one, on a constructor `F`, writes a `.union` row whose output is not `[.app F args]`. `mergeRound_inv_false` is the witness; `Inv.mergeRound_of_legalMerges` is the repair. `CtorTerms` *is* preserved, as its docstring claims — the break is `ctorRows` |
| `FDatabase.execActions_ActionsStep` as originally stated | the `cons` step cannot re-establish `Inv` for the recursive call without `Actions.SetLegal as d.sig`: a `set` on a constructor breaks `ctorRows`, and `execExpr_MEval` is unavailable from that point on |
| `FDatabase.patternHoldsM_MValidSubst` as originally stated | `patternHoldsM` reads `σ` only through `d.env ++ σ`, so a `σ` carrying bindings the pattern never mentions still passes, while every `MValidSubst` constructor demands `ValidEnv (p.freeVars db.env) db σ`. `patternHoldsM_MValidSubst_false` is the witness. `Proofs/Interp.lean`'s `patternHolds_iff` already carries the hypothesis |
| `FDatabase.matchQueryM_MValidQuerySubst` as originally stated | `Query.freeVars` **deduplicates** while `Env.UnionAll` is literal concatenation, so `MValidQuerySubst db q σ` forces `σ.length = Σᵢ \|pᵢ.freeVars\|` and any query with a repeated variable is unsatisfiable — `q = [.expr (.var "x"), .expr (.var "x")]` is the witness (`matchQueryM_MValidQuerySubst_false`). The conclusion has to be up to `Env.Agree`, exactly as `Proofs/Interp.lean`'s `validQuerySubst_of_mem_matchQuery` already concludes |
| any **unconditional** `FDatabase.Inv.decl` | `CtorTerms` is relative to `db.sig`, so declaring `g` as `:merge` after `g()` is already a term breaks it (`claim1`). This is what `FDatabase.Unused` in `ProgramLegal` excludes |
| `MCong.mono` / `MCongList.mono` / `Out.mono` *without* `d₁.sig = d₂.sig` | `Contained` ignores `sig` but `MCong.fd` needs `mergeOf f = .union`; redeclaring `f` as `:no-merge` adds nothing yet destroys a derivation (`mcong_mono_needs_sig`) |
| `Expr.MEval_of_eval`'s original hypothesis `∀ f, Prim.ofName f = none` | unsatisfiable (`not_forall_ofName_eq_none`); use `MEval_of_eval'` |
| `MergeStep.diamond_of_join`'s `hjoin` | vacuous — take `le := fun _ _ => False` |
| `RunStep.unique_of_confluent`'s `hconf` | Newman's lemma needs termination; `MergeStep` deliberately has none. Use the proved `unique_of_diamond` |
| `mergeRound_closure` | every `MergeStep` grows the state, so no closure reaches a state with fewer rows |
| `execM_reachable` | **despite the name this is about `exec`**, the constructor interpreter, which has no merge phase — so the row above is not its reason. It is false because `Expr.eval` builds an application for *every* name; its docstring has two counterexample programs. Repairable with `CtorDecls` + `Expr.NoPrim`, then blocked on the `CtorRows` preservation lemmas, so not false forever |
| `FDatabase.mergeRound_rowCount` as stated | `hpure` bounds the merge body but not its *result* |

## Queue

Roughly in priority order.

1. **Fix `Rebuilt`** — see "The `Rebuilt` problem". Until this lands, three of M11's
   thirteen statements are vacuously true and proving them would establish nothing. Do this
   before any other M11 work.
2. **`execM_current_of_lattice`** — the completeness companion to `execM_contained`, without
   which containment is satisfied by a do-nothing implementation. ~200–300 lines on the
   finished chain: an induction over the merge phase carrying "every output the spec records
   at this key class is `le` the one the implementation holds", whose step is that
   `mergeOneWith` replaces two rows by their join. Deleting the merged rows is what makes
   that invariant maintainable at all.
3. **Fold merge-body legality into `Cmd.SetLegal`** so `Signature.MergesLegal` and the
   rule-head condition come from `Program.SetLegal` rather than being threaded by hand.
   Small, and it shrinks every stage-4 statement.
4. **M11 proper** — `Proofs/Encode.lean`'s 13 statements. The language blocker is gone
   (multi-column `set` and `Pattern.values` landed), so the remaining gap is the encoder:
   `encode` does not yet emit proof rows, which is why theorems (12) and (13) are vacuous
   today, and `Checks` is still `opaque`. `CHECKER.md` scopes the checker at 150–250 lines
   for the minimal five-justification subset, and argues the real cost is the *conversion*
   layer (~579 lines of `convert_raw_proof` plus ~700 of `proof_head.rs` replay), singling
   out `Firing`'s memoized cross-row walk as the least pleasant thing in the subtree. Its
   recommendation is to split M11(1) at the layer boundary.
5. **`MEval.lookup`-in-a-query coverage** — the generator only ever `set`s merge functions
   and queries constructors, so this path has *zero* differential coverage despite being
   reachable through `execM`. Every previously untested path here turned out to hide a
   defect, and this one already has one: `execExpr`'s lookup branch requires the *first*
   congruent row to be single-column, so a multi-column row shadowing a single-column one
   makes it return `none` where `MEval` succeeds (`claim3`). Harmless to the chain — `none`
   imposes no obligation — but it would surface as `STUCK` in difftest. Reaching it needs a
   function whose rows differ in column count at one key, which egglog's type checker rejects
   and this model does not: `FnDecl.outArity` is never read outside `Tests/Egg.lean`. Arity
   checking is missing model-wide.
6. **`SetLegal` for `Pattern.values`** — egglog recognizes the destructure only for a
   tuple-output `f`. Needs `Rule.SetLegal` extended to the query, where the `CtorRows` chain
   currently covers only rule heads. Nothing unsound meanwhile: a destructure writes nothing.
7. **Tidy-ups.** Move `CongOn` into `Spec/Congruence.lean` and have `ValidSubst` use it — it
   is already there unnamed, as `ValidSubst.eq`'s last premise (`Spec/Match.lean`), inherited
   from the Redex. Restate `mcong_iff_cong_premises` as the `Iff` next to `mcong_iff_cong`.
   Relocate the lemmas stranded by import order. Flagged in place: `evalAction_sig`
   (`Proofs/Step.lean`), the `addTerm_eq_self` family (`Proofs/Merge.lean`),
   `Signature.AllConstructors.mergeOf_eq` (`Proofs/Step.lean` — the most literal instance,
   duplicating `Signature.mergeOf_eq_union` under another name to dodge an import cycle), and
   `Database.Contained.addTerm_mono` (`Proofs/Merge.lean`). *Not* flagged, so do not trust
   the flags alone: the `contained_addRow` duplicate in `Proofs/Merge.lean`, whose whole
   docstring is "A `set` only adds" with nothing saying it restates
   `Database.Contained.addRow`; `Expr.NoPrim`, which per `README.md`'s definitions-only rule
   is already where it belongs, so the strays there are really the two `@[simp]` lemmas
   beside it; and `Database.sig_addTerms` in `Proofs/Merge.lean`, which duplicates
   `Proofs/Database.lean`'s `addTerms_sig`.
8. **M12** — collapse `Cong`/`MCong` and migrate `Proofs/Interp.lean` from equalities to
   reachability (~1000–1400 lines). Deliberately deferred: the split maps onto the two sides
   of M11's simulation theorem, which is structure, not duplication. Decide on evidence from
   M11, or when the paper wants one semantics on the page.
9. **Compare against [`lambdaclass/truth_research`](https://github.com/lambdaclass/truth_research)**
   for design insight. Unexamined so far.

## Gotchas

These have each cost real time.

- **`lean_verify`, not the build.** Writing `h.ge` for a set inclusion compiles fine and
  silently pulls `Classical.choice` into every downstream axiom set — `mcong_iff_cong` went
  from `propext` alone to three axioms with a green build. Use `▸`.
- **The LSP caches imports.** After editing a file's *dependency*, run `lean_build` before
  trusting `lean_verify`; it has reported a spurious `sorryAx` from a stale cache.
- **Never edit a proof file by line index.** A scripted insertion at a computed line number
  silently deleted 357 lines here. Use anchored replacement, asserting each pattern occurs
  exactly once.
- **Develop a proof in a scratch file, not in `Proofs/Merge.lean`.** A file that does
  `import EgglogSemantics` and is checked with `lake env lean scratch/X.lean` sees the whole
  library without rebuilding it, so the edit-check loop is seconds rather than minutes. Move
  the finished proof in afterwards. `Proofs/Merge.lean` is one file, so a lemma must appear
  *after* everything it uses — several stage-4 lemmas need `mergeOneWith_inv`,
  `mergeRound_confined`, `execAction_sig` and `mem_mergeEnv`, which sit near the end, so they
  belong at the end too rather than at their stub's position.
- **Nullary `:merge` functions make counterexamples computable.** `congrKeys cl [] []`
  reduces through `List.all []` without forcing `cl = closureF`, whose well-founded recursion
  the kernel cannot unfold. With nullary keys the whole interpreter, down to
  `mergeSaturateF 64`, reduces by `rfl`. Without that trick these counterexamples are
  impractical.
- **Structure eta will misdirect `rw`.** In `ActionStep`'s `.letBind` case a bare
  `rw [toDatabase_setEnv]` rewrites the goal's *first* argument, because `d.toDatabase`
  unifies with `{d with env := d.env}.toDatabase`; the follow-up `rw` then fails. Pin the
  arguments: `toDatabase_setEnv (d := d.addTerm t) (σ := (v, t) :: d.env)`.
- **`lake build` does not rebuild the difftest executable** — `lake build difftest` does.
  `scripts/difftest.sh` handles this; a manual run may not.
- **A green suite is not evidence the property held.** Three separate defects hid behind one:
  `min`/`max` were missing from `Prim.ofName` and silently became constructor applications;
  the generator's `pick` read an LCG's low bits and had period 4; and a stale-read test agreed
  with egglog only because `addRow` prepends and the reader took the first row. Check the
  profile distribution, not just the pass count.
- **`make lean-check` greps the sources for `sorry`** because `lake build` only warns. It
  drops backtick-quoted hits, because two module docstrings discuss `sorry` in prose and
  without that filter the target could never pass.
- **Do not use `native_decide`** — it adds `Lean.ofReduceBool` to downstream axiom sets.
- `Cong`/`CongList` and `MCong`/`MCongList` are mutually inductive, so the `induction` tactic
  refuses them; recurse with `match` inside a `mutual theorem` block.
