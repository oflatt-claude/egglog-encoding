# Handoff

What is done, what is stated but unproved, what is known false, and what to do next.
[`PLAN.md`](PLAN.md) has the design rationale and milestones; this file has the state and
the queue. Read [`README.md`](README.md) first for the layout.

## State of play

`lake build` is clean (717 jobs). `make lean-difftest` is **118 passed / 0 failed /
0 skipped**, across 60 random constructor cases (38 distinct profiles), 30 random `:merge`
cases (20 distinct profiles), and 28 curated cases.

**21 `sorry`s, all in two files:** 13 in `Proofs/Encode.lean` (M11 — every statement there
is unproved on purpose, the statements *are* the deliverable) and 8 in `Proofs/Merge.lean`.

**Fifteen of the refinement chain's seventeen lemmas are proved.** The two that are not —
`execCmdM_contained` and `execProgramM_contained` — are *refuted*, and are blocked on the
one-line specification fix in queue item 0, not on proof effort.

**Nine of the seventeen were false as stated** and now carry repaired statements; see
"Known false". Three of those nine were wrong in ways the already-proved M10 analogues in
`Proofs/Interp.lean` had solved years earlier in the file's own history —
`matchQueryM_MValidQuerySubst` lacked the `Env.Agree` that
`validQuerySubst_of_mem_matchQuery` carries, `patternHoldsM_MValidSubst` lacked
`patternHolds_iff`'s `ValidEnv`, `execActions_ActionsStep` lacked `SetLegal`. When stating
an M9 lemma, read its M10 counterpart first.

`Proofs/Counterexamples.lean` holds the machine-checked witness for every "false as
stated" claim, so they are checked by `lake build` rather than asserted in prose.

Everything else is proved. Three theorems are load-bearing enough to check on every
change:

| theorem | expected axioms |
| --- | --- |
| `Egglog.mcong_iff_cong` | `propext` **alone** |
| `Egglog.exec_toDatabase` | `propext, Classical.choice, Quot.sound` |
| `Egglog.mem_closure_iff` | `propext, Classical.choice, Quot.sound` |

Check with `lean_verify` (lean-lsp MCP), not by grepping for `sorry` — it asks the kernel
what a theorem actually depends on and traces into Mathlib.

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
  **containment**: `execM_contained` — which is currently *false*, for a reason that is a
  bug in `Spec/Merge.lean` rather than in `execM`. Queue item 0.

`hasMergeRow_eq_false` + `mergeRound_eq_self` + `mergeSaturateF_eq_self` prove the merge
phase is the identity on a constructor-only database, which is why deletion cannot affect
`exec_toDatabase`.

Containment alone is satisfied by a do-nothing implementation, so two statements carry the
completeness weight: the constructor-fragment equality above, and
`execM_current_of_lattice` (the implementation holds the `Current` value at each key class)
for merges that are joins. For a non-lattice merge nothing is claimed — that is
`MERGE.md`'s "order-dependent merges are the user's fault".

## Next up: the refinement chain (2 of 17 left, both blocked)

In `Proofs/Merge.lean`, under "The refinement chain". The two that remain are refuted
rather than merely unproved, so the next move is queue item 0's specification fix, not more
proof effort.

1. ~~**`FDatabase.Inv` preservation**~~ — done. `Inv` is now `WF` + `CtorTerms` +
   `RowsComplete` + **`RowsWF`** + **`ctorRows`**. The last two are not optional: without
   `rowsWF` a `lookup`'s result is unconstrained and `execAction` cannot re-establish
   `ctorTerms`; `ctorRows` is `closureF_ok`'s `hrow`. `Spec/Database.lean`'s `RowsWF`
   docstring predicted this ("belongs there once something reads it").
2. ~~**Evaluation**~~ — done, via `Out_of_mem_outs`, which is where `Cong.toMCong'` is spent.
3. ~~**Actions and matching**~~ — done. Both matching lemmas needed repair.
4. **Containment** — `mergeRound_contained`, `mergeSaturateF_contained` and
   `execRunRulesM_contained` are done, each carrying a legality side condition;
   `execCmdM_contained` and `execProgramM_contained` are **refuted** and wait on item 0.

Stages 1 and 2 are **coupled**, contrary to what this file used to claim: `Inv.execAction`
cannot be proved without knowing what `execExpr` produces (`execExpr_ctorTerm`), so they
have to be done together.

The legality side conditions are all the same condition seen from different places: an
action block that writes a row must be `SetLegal`, and that has to hold for merge bodies
(`Inv.mergeRound`, `mergeRound_contained`, `mergeSaturateF_contained`) and for rule heads
(`execRunRulesM_contained`) as well as for the top-level actions `Program.SetLegal` already
covers. The spec-level gap is that `Cmd.SetLegal (.decl _ _)` is `True`, so nothing
constrains a declaration's merge body; closing that would let these hypotheses come from
`Program.SetLegal` instead of being threaded by hand.

The design work is done and proved; do not redo it. `execExpr` compares keys with
`closureF`, which computes **`Cong`**, while `Database.Out` compares them with **`MCong`**.
`Cong.toMCong'` bridges that, over `CtorTerms` and `RowsComplete` — which, unlike
`CtorRows`, survive a `:merge` declaration, because they constrain `terms` and the
constructor rows and `mergeRound_confined` proves a merge touches neither.

## Known false, with counterexamples in their docstrings

Do not try to prove these. Each has a machine-checked witness or a worked counterexample.

`Proofs/Counterexamples.lean` holds the compiling witnesses for the first block, so they
are checked by `lake build` rather than described in prose. Every one keeps its `:merge`
function **nullary**: that makes `congrKeys cl [] []` reduce through `List.all []` without
forcing `cl = closureF`, whose well-founded recursion the kernel cannot unfold, and with it
the whole interpreter down to `mergeSaturateF 64` reduces by `rfl`.

| statement | why |
| --- | --- |
| **`execM_contained`**, and `execCmdM_contained` / `execProgramM_contained` above it | `execCmdM` runs a merge phase after every top-level `.action`; the spec's `CmdStep.action` has **no** merge phase, so the implementation reaches states holding a merge *result* no `ProgramStep` state holds. `claim2_execM` refutes it on `(function f () i64 :merge 7) (set (f) 1) (set (f) 2)`, where `execM prog = some d2` by `rfl`. The docstring's "may find fewer results, never more — the safe direction" is wrong: deletion is safe, the *added* row is not. **This one is a bug in `Spec/Merge.lean`, not in the interpreter** — see queue item 0, which has the egglog evidence and the one-line fix that makes all three true again |
| `FDatabase.Inv.addTerm` / `.addEq` / `.addRow` as originally stated | `addTerm` takes an arbitrary `Term`, so inserting an application of a declared `:merge` function breaks `CtorTerms`. All three now carry the constructor-term condition on what they insert. `addRow`'s `hf` was also defending the wrong field — `RowsComplete` is an inclusion, which adding a row cannot break — and now earns its keep against `ctorRows` |
| `FDatabase.Inv.mergeRound` as originally stated | a merge body is an arbitrary `List Action` with no `SetLegal` obligation, so a `(set (F) …)` inside one, on a constructor `F`, writes a `.union` row whose output is not `[.app F args]`. `mergeRound_inv_false` is the witness; `Inv.mergeRound_of_legalMerges` is the repair. `CtorTerms` *is* preserved — the break is `ctorRows`. The gap is in the spec: `Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about merge bodies |
| `FDatabase.execActions_ActionsStep` as originally stated | the `cons` step cannot re-establish `Inv` for the recursive call without `Actions.SetLegal as d.sig`, since a `set` on a constructor breaks `ctorRows` and `execExpr_MEval` is unavailable from that point on |
| `FDatabase.patternHoldsM_MValidSubst` as originally stated | `patternHoldsM` reads `σ` only through `d.env ++ σ`, so a `σ` carrying bindings the pattern never mentions still passes, while every `MValidSubst` constructor demands `ValidEnv (p.freeVars db.env) db σ`. `patternHoldsM_MValidSubst_false` is the witness. `Proofs/Interp.lean`'s `patternHolds_iff` already carries the hypothesis |
| `FDatabase.matchQueryM_MValidQuerySubst` as originally stated | `Query.freeVars` **deduplicates** while `Env.UnionAll` is literal concatenation, so `MValidQuerySubst db q σ` forces `σ.length = Σᵢ \|pᵢ.freeVars\|` and any query with a repeated variable is unsatisfiable — `q = [.expr (.var "x"), .expr (.var "x")]` is the witness (`matchQueryM_MValidQuerySubst_false`). The conclusion has to be up to `Env.Agree`, exactly as `Proofs/Interp.lean`'s `validQuerySubst_of_mem_matchQuery` already concludes |
| any `FDatabase.Inv.decl` | `CtorTerms` is relative to `db.sig`, so declaring `g` as `:merge` after `g()` is already a term breaks it (`claim1`). Harmless for `execCmdM_contained`'s `.decl` case, whose goal is trivial, but `execProgramM_contained`'s induction has nothing to carry across a declaration |
| `MCong.mono` / `MCongList.mono` / `Out.mono` *without* `d₁.sig = d₂.sig` | `Contained` ignores `sig` but `MCong.fd` needs `mergeOf f = .union`; redeclaring `f` as `:no-merge` adds nothing yet destroys a derivation (`mcong_mono_needs_sig`) |
| `Expr.MEval_of_eval`'s original hypothesis `∀ f, Prim.ofName f = none` | unsatisfiable (`not_forall_ofName_eq_none`); use `MEval_of_eval'` |
| `MergeStep.diamond_of_join`'s `hjoin` | vacuous — take `le := fun _ _ => False` |
| `RunStep.unique_of_confluent`'s `hconf` | Newman's lemma needs termination; `MergeStep` deliberately has none. Use the proved `unique_of_diamond` |
| `mergeRound_closure` | every `MergeStep` grows the state, so no closure reaches a state with fewer rows |
| `execM_reachable` | **despite the name this is about `exec`**, the constructor interpreter, which has no merge phase — so the row above is not its reason. It is false because `Expr.eval` builds an application for *every* name; its docstring has two counterexample programs. Repairable with `CtorDecls` + `Expr.NoPrim`, then blocked on the `CtorRows` preservation lemmas, not false forever |
| `FDatabase.mergeRound_rowCount` as stated | `hpure` bounds the merge body but not its *result* |

## Queue

Roughly in priority order.

0. **Give `CmdStep.action` a merge phase.** `execM_contained` is refuted, and the defect is
   in `Spec/Merge.lean`, not in the interpreter. Checked against the release binary, with
   **no `(run)` anywhere**:

   ```
   (function f () i64 :merge (max old new))  (set (f) 1)  (set (f) 2)
   → (print-size f) = 1,  (f) -> 2
   ```

   and swapping the merge gives `old` → 1, `new` → 2, `min` → 1, `max` → 2, so the merge
   *function* really runs at the second `set` rather than last-write-wins. `print-size` and
   `print-function` are both `&self` and cannot rebuild, so nothing else can be doing it.
   The path is `lib.rs:2101` → `eval_actions` (`lib.rs:1490`), which compiles a bare action
   into a one-rule run and calls `run_rules` at `lib.rs:1508`; every rule-set run ends in
   `merge_all` (`core-relations/.../execute.rs:654`). So `execCmdM` is faithful and the
   specification is not. The edit:

   ```lean
   | action {db d db' : Database} {a : Action} :
       Database.ActionStep db a d → MergeClosure d db' → CmdStep db (.action a) db'
   ```

   Cost is mostly negative. `execCmdM_action_contained` is already proved against the
   amended rule and needs no transport lemma. `CmdStep.contained` survives via
   `MergeClosure.contained`; `invariant_of_step` is unaffected; the constructor fragment is
   untouched because `MergeStep.saturated_of_allConstructors` makes the added closure the
   identity, so M10 and `exec_toDatabase` do not move. The real cost is that
   `Proofs/Counterexamples.lean`'s `Falsity.claim2_*` become false and must go — they are
   recording this spec bug, so that is the point.
1. **The refinement chain** above, then `execM_current_of_lattice` (~200–300 lines on top).
2. **M11 proper** — `Proofs/Encode.lean`'s 13 statements. The language blocker is gone
   (multi-column `set` and `Pattern.values` landed), so the proof column is now an
   *encoder* gap, not a language one. `CHECKER.md` scopes it.
3. **`EncodeDomain` gains "ends in `(run)`"** — otherwise `Rebuilt` is vacuous, since
   maintenance rules only fire inside `Cmd.run`. Decided against appending a `(run)` inside
   `encode` (source and target would run different numbers of rounds — a soundness break)
   and against a saturation predicate (reintroduces the "cannot step" fixpoint notion this
   development deliberately avoids).
4. **`MEval.lookup`-in-a-query coverage** — the generator only ever `set`s merge functions
   and queries constructors, so this path has *zero* differential coverage despite being
   reachable through `execM`. Every previous untested path here turned out to hide a defect.
5. **`SetLegal` for `Pattern.values`** — egglog recognizes the destructure only for a
   tuple-output `f`. Needs `Rule.SetLegal` extended to the query, where the `CtorRows` chain
   currently covers only rule heads. Nothing unsound meanwhile: a destructure writes nothing.
6. ~~**The `ActionsStep` transport lemma** (~150–250 lines)~~ — the estimate was 5x high in
   the form that was actually needed. `Database.ActionsStep.mono` is proved in ~35 lines:
   an `ActionStep`'s effect is fixed by its `MEval` witnesses and `Expr.MEval.mono` carries
   those into a larger database unchanged. That is enough for containment, which wants only
   a *lower bound* on the result. `diamond_of_join` is still open because it wants the
   exact componentwise join, which this does not give.
7. **Tidy-ups.** Move `CongOn` into `Spec/Congruence.lean` and have `ValidSubst` use it — it
   is already there unnamed, as `ValidSubst.eq`'s last premise (`Spec/Match.lean`), inherited
   from the Redex. Restate `mcong_iff_cong_premises` as the `Iff` next to `mcong_iff_cong`.
   Relocate the lemmas stranded by import order. Flagged in place: `evalAction_sig`
   (`Proofs/Step.lean`), the `addTerm_eq_self` family (`Proofs/Merge.lean`),
   `Signature.AllConstructors.mergeOf_eq` (`Proofs/Step.lean`, the most literal instance —
   it duplicates `Signature.mergeOf_eq_union` under another name to dodge an import cycle),
   and `Database.Contained.addTerm_mono` (`Proofs/Merge.lean`). *Not* flagged, and both
   worth a comment before anyone trusts this list: the `contained_addRow` duplicate at
   `Proofs/Merge.lean` — its whole docstring is "A `set` only adds", with nothing saying it
   restates `Database.Contained.addRow` — and `Expr.NoPrim`, which per `README.md`'s
   definitions-only rule is already where it belongs, so the strays there are really the two
   `@[simp]` lemmas beside it in `Proofs/Merge.lean`.
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
- **`lake build` does not rebuild the difftest executable** — `lake build difftest` does.
  `scripts/difftest.sh` handles this; a manual run may not.
- **A green suite is not evidence the property held.** Three separate defects hid behind one:
  `min`/`max` were missing from `Prim.ofName` and silently became constructor applications;
  the generator's `pick` read an LCG's low bits and had period 4; and a stale-read test agreed
  with egglog only because `addRow` prepends and the reader took the first row. Check the
  profile distribution, not just the pass count.
- **Do not use `native_decide`** — it adds `Lean.ofReduceBool` to downstream axiom sets.
- `Cong`/`CongList` and `MCong`/`MCongList` are mutually inductive, so the `induction` tactic
  refuses them; recurse with `match` inside a `mutual theorem` block.
