# Handoff

What is done, what is stated but unproved, what is known false, and what to do next.
[`PLAN.md`](PLAN.md) has the design rationale and milestones; this file has the state and
the queue. Read [`README.md`](README.md) first for the layout.

## State of play

`lake build` is clean (716 jobs). `make lean-difftest` is **118 passed / 0 failed /
0 skipped**, across 60 random constructor cases (38 distinct profiles), 30 random `:merge`
cases (20 distinct profiles), and 28 curated cases.

**28 `sorry`s, all in two files:** 13 in `Proofs/Encode.lean` (M11 — every statement there
is unproved on purpose, the statements *are* the deliverable) and 15 in `Proofs/Merge.lean`.

Eight of the refinement chain's seventeen lemmas are now proved: `Inv.empty`,
`Inv.addTerm`, `Inv.addEq`, `Inv.addRow`, `Inv.execAction`, `Inv.mergeRound`,
`execExpr_MEval`, `execExprList_MEvalList`. **Five of them were false as stated** and
carry repaired statements — see "Known false" below. Nine remain.

Do not grep for `sorry` to count these: `Proofs/Encode.lean:7` has the word in prose
inside a module docstring, so `make lean-check`'s `! grep -rnw … sorry` can never pass
even at zero real obligations. That is a latent false failure in the gate.

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
  **containment**: `execM_contained`.

`hasMergeRow_eq_false` + `mergeRound_eq_self` + `mergeSaturateF_eq_self` prove the merge
phase is the identity on a constructor-only database, which is why deletion cannot affect
`exec_toDatabase`.

Containment alone is satisfied by a do-nothing implementation, so two statements carry the
completeness weight: the constructor-fragment equality above, and
`execM_current_of_lattice` (the implementation holds the `Current` value at each key class)
for merges that are joins. For a non-lattice merge nothing is claimed — that is
`MERGE.md`'s "order-dependent merges are the user's fault".

## Next up: the refinement chain (9 of 17 left)

In `Proofs/Merge.lean`, under "The refinement chain". **`execM_contained` is false** — see
below — so deriving it is no longer the goal; the chain's remaining value is stages 3 and 4
plus whatever replaces the `.action` case.

1. ~~**`FDatabase.Inv` preservation**~~ — done. `Inv` is now `WF` + `CtorTerms` +
   `RowsComplete` + **`RowsWF`** + **`ctorRows`**. The last two are not optional: without
   `rowsWF` a `lookup`'s result is unconstrained and `execAction` cannot re-establish
   `ctorTerms`; `ctorRows` is `closureF_ok`'s `hrow`. `Spec/Database.lean`'s `RowsWF`
   docstring predicted this ("belongs there once something reads it").
2. ~~**Evaluation**~~ — done, via `Out_of_mem_outs`, which is where `Cong.toMCong'` is spent.
3. **Actions and matching** — `execAction_ActionStep`, `execActions_ActionsStep`,
   `patternHoldsM_MValidSubst`, `matchQueryM_MValidQuerySubst`. `Inv.execActions` and
   `Inv.setEnv`/`setEnvRules`/`filterRows` are already proved and are what these need.
4. **Containment** — `mergeRound_contained`, `mergeSaturateF_contained`,
   `execRunRulesM_contained`; `execCmdM_contained` and `execProgramM_contained` are
   **false** as stated. These are the only places a witness must be *chosen* rather than
   computed.

Stages 1 and 2 are **coupled**, contrary to what this file used to claim: `Inv.execAction`
cannot be proved without knowing what `execExpr` produces (`execExpr_ctorTerm`), so they
have to be done together.

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
| **`execM_contained`**, and `execCmdM_contained` / `execProgramM_contained` above it | `execCmdM` runs a merge phase after every top-level `.action`; the spec's `CmdStep.action` has **no** merge phase, so the implementation reaches states holding a merge *result* no `ProgramStep` state holds. `claim2_execM` refutes it on `(function f () i64 :merge 7) (set (f) 1) (set (f) 2)`, where `execM prog = some d2` by `rfl`. The docstring's "may find fewer results, never more — the safe direction" is wrong: deletion is safe, the *added* row is not |
| `FDatabase.Inv.addTerm` / `.addEq` / `.addRow` as originally stated | `addTerm` takes an arbitrary `Term`, so inserting an application of a declared `:merge` function breaks `CtorTerms`. All three now carry the constructor-term condition on what they insert. `addRow`'s `hf` was also defending the wrong field — `RowsComplete` is an inclusion, which adding a row cannot break — and now earns its keep against `ctorRows` |
| `FDatabase.Inv.mergeRound` as originally stated | a merge body is an arbitrary `List Action` with no `SetLegal` obligation, so a `(set (F) …)` inside one, on a constructor `F`, writes a `.union` row whose output is not `[.app F args]`. `mergeRound_inv_false` is the witness; `Inv.mergeRound_of_legalMerges` is the repair. `CtorTerms` *is* preserved — the break is `ctorRows`. The gap is in the spec: `Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about merge bodies |
| any `FDatabase.Inv.decl` | `CtorTerms` is relative to `db.sig`, so declaring `g` as `:merge` after `g()` is already a term breaks it (`claim1`). Harmless for `execCmdM_contained`'s `.decl` case, whose goal is trivial, but `execProgramM_contained`'s induction has nothing to carry across a declaration |
| `MCong.mono` / `MCongList.mono` / `Out.mono` *without* `d₁.sig = d₂.sig` | `Contained` ignores `sig` but `MCong.fd` needs `mergeOf f = .union`; redeclaring `f` as `:no-merge` adds nothing yet destroys a derivation (`mcong_mono_needs_sig`) |
| `Expr.MEval_of_eval`'s original hypothesis `∀ f, Prim.ofName f = none` | unsatisfiable (`not_forall_ofName_eq_none`); use `MEval_of_eval'` |
| `MergeStep.diamond_of_join`'s `hjoin` | vacuous — take `le := fun _ _ => False` |
| `RunStep.unique_of_confluent`'s `hconf` | Newman's lemma needs termination; `MergeStep` deliberately has none. Use the proved `unique_of_diamond` |
| `execM_reachable` for `execM`, `mergeRound_closure` | every `MergeStep` grows the state, so no closure reaches a state with fewer rows |
| `FDatabase.mergeRound_rowCount` as stated | `hpure` bounds the merge body but not its *result* |

## Queue

Roughly in priority order.

0. **Decide what `execM`'s contract actually is.** `execM_contained` is refuted, so this
   blocks the rest of the chain. Either the spec's `CmdStep.action` gains a merge phase
   (which is what egglog does — it resolves collisions as part of the action, not only
   inside `(run)`), or `execCmdM` stops merging after `.action`. The first looks right and
   makes the implementation the faithful one; it changes `Spec/Merge.lean`, so it wants a
   difftest run behind it. While this is open, stage 4 cannot be stated correctly.
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
6. **The `ActionsStep` transport lemma** (~150–250 lines) would settle `diamond_of_join` in a
   *stronger* one-step form than `MERGE.md`'s open question 2 contemplates: a step's effect
   is independent of the ambient state, and nothing is ever removed.
7. **Tidy-ups.** Move `CongOn` into `Spec/Congruence.lean` and have `ValidSubst` use it — it
   is already there unnamed, as `ValidSubst.eq`'s last premise (`Spec/Match.lean`), inherited
   from the Redex. Restate `mcong_iff_cong_premises` as the `Iff` next to `mcong_iff_cong`.
   Relocate the lemmas stranded by import order (`evalAction_sig`, `Expr.NoPrim`, the
   `addTerm_eq_self` family, and the `contained_addRow` duplicate) — all flagged in place.
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
