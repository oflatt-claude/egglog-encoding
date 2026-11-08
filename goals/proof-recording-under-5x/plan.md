# Proof recording below 5×: execution plan

Use the accepted [facts](facts.md) as the contract. Work in
`/Users/saul/p/wt/egglog-encoding/proof-recording-outliers`, on
`codex/proof-recording-outliers`, based on `e8a2a58d`. Preserve the dirty primary
encoding checkout and the unrelated typed-API work in `../egg-smol`.

## Approach and starting evidence

Fix the presentation independently, reproduce the three outliers, profile their
costs, and evaluate Eli's existing container work before choosing a custom
optimization. Keep one small experimental change at a time. Accept the goal only
after both ratios are below 5× for every original selected replay.

**Typed generation remains deferred.** [PR #69](https://github.com/saulshanabrook/egglog-encoding/pull/69)
is closed without merging; its local revival and timer-control work are recorded
in [deferred work](deferred-work.json). The user has explicitly ruled out reviving
that encoder-wide conversion or developing/adopting a strongly typed Rust
authoring API here. Frontend profiling is still useful, but any optimization must
preserve the accepted source-generation, parser/typechecker and runtime contracts.
Do not introduce a new typed IR/binder or treat the old timings or architectural
proposals as authorization to reopen that workstream. Preserve declaration
order, scoping, error and rollback behavior when reducing redundant work.

The [frozen cohort](cohort.json) contains all 127 selected file identities; every
input hash has been checked against this worktree. The [saved phase data](paper-attribution.json)
is from November 4, not a fresh measurement of the current baseline:

| Replay | Off → recording wall time | Off → recording peak RSS | Diagnostic lead |
| --- | --- | --- | --- |
| Luminal gemma | 0.327 → 2.260 s | 65.4 → 203.0 MiB | Recording type checking + frontend: 1.476 s |
| Luminal gemma4_moe | 0.683 → 4.285 s | 94.9 → 289.5 MiB | Recording type checking + frontend: 2.557 s |
| DialEgg timer-nmm-80 | 1.425 → 2.580 s | 133.2 → 892.2 MiB | Memory growth needs allocation/state evidence |

These leads determine the first probes; they do not establish the current root
causes or the effect of Eli's changes.

## Ordered work

1. **Complete the figure correction.** The shared specification
   `figures/eval/corpus-cdf.vl.json` now retains metric columns, aligns plot areas,
   hides unused overview marks/axes, and names the overview's metric. The memory
   overview sits below Peak RSS. `figures/eval.test.mjs` covers no tail, either
   single-metric tail, and both tails. The regenerated PDF is in the paired paper
   worktree, `/Users/saul/p/wt/extended-egglog-paper/fix-recording-overview`, on
   `codex/fix-recording-overview` from paper `main` (`310f3b4`).

   Verification already completed: `make test-figures` (23 passed), actual PDF
   raster inspection, embedded-font inspection, and equality of all 254 plotted
   metric records before/after. See [figure validation](figure-validation.json).
   No benchmark observations were collected for this correction.

2. **Reproduce and profile the baseline.** Reuse compatible environments/build
   caches, with the existing lockfiles and Python 3.12. Keep raw reports and
   profiles in ignored `benchmarks/local/proof-recording-under-5x/`. Reproduce
   the three real inputs with three fresh runs per condition:

   ```sh
   UV_PYTHON=3.12 ./bench.py \
     benchmarks/corpus/luminal/gemma-call-01.egg \
     benchmarks/corpus/luminal/gemma4_moe-call-01.egg \
     benchmarks/corpus/dialegg/timer-nmm-80-call-01.egg \
     --target baseline=@e8a2a58d --compare-target baseline=@e8a2a58d \
     --treatment proofs --compare-treatment off \
     --rounds 3 --timeout-sec 60 --force-run --detail rulesets \
     --report benchmarks/local/proof-recording-under-5x/baseline.jsonl
   ```

   Use the verified public CPU-profiler interface on one endpoint at a time:

   ```sh
   UV_PYTHON=3.12 ./bench.py profile \
     benchmarks/corpus/luminal/gemma-call-01.egg \
     --target @e8a2a58d --treatment proofs --profile-seconds 10 \
     --timeout-sec 60 \
     --profiles-dir benchmarks/local/proof-recording-under-5x/profiles
   ```

   Repeat only where the first profile or phase report leaves a consequential
   uncertainty. Trace Luminal setup through `egglog/src/lib.rs`,
   `egglog/src/typechecking.rs`, `egglog/src/proofs/proof_encoding.rs`, and
   `proof_encoding_helpers.rs`. For DialEgg, inspect proof-table/container growth
   and rebuilding at stable execution boundaries in `proof_container_rebuild.rs`,
   `proof_encoding_rebuild.rs`, and `egglog/core-relations/src/containers/`.
   Use diagnostic input copies and, if needed, a small temporary counter probe;
   preserve the original timed inputs. CPU samples do not measure allocations
   or explain peak RSS by themselves. Keep allocation diagnostics separate from
   benchmark observations.

3. **Evaluate Eli's stack in isolation.** The current candidate is
   [PRs #974–#985](https://github.com/egraphs-good/egglog/pull/985), with tip
   `df7e28de604546c747435eabab89fd935e83e7d1` and stack base
   `b912caa9694c0c029f9ae3d91db0adc8824e14f5`; refresh the live head before use.
   Reuse/open its upstream checkout with the PR-worktree skill from the existing
   upstream clone at `/Users/saul/p/egg-smol`, preserving that checkout's dirty
   typed-API work. Prepare a separate downstream integration experiment that
   preserves this root Cargo workspace and proof implementation. Do not replace
   the vendored tree or rewrite subtree history/metadata.

   The old packed-join PR #959 is superseded; its replacement stack #993–#1000
   is merged and the downstream subtree has advanced beyond that merge. Check
   ancestry/content before attributing any gain to new packed-join work.

   Make one bounded integration attempt. Resolve small compatibility problems;
   record exact conflicts/compiler failures if integrating the full container
   stack would require an unrelated API redesign. Measure a working integration
   on the three canaries using its own fresh off/proofs ratio, then compare its
   absolute recording costs with the baseline. Keep the experimental stack
   separate from the minimal final patch. The result is a measured effect or a
   concrete blocker, not an assumption that upstream tests prove this workload.

4. **Run the smallest useful optimization experiments.** Record at least two
   competing explanations for each remaining outlier, predictions, and a probe
   that distinguishes them. Let fresh profiles decide between generated-program
   setup/typechecking, command execution, proof representation/container storage,
   and rebuilding/index work. Prefer redundant-work or allocation reductions
   within the current pipeline; an encoder-wide typed rewrite is excluded even
   if generated typechecking dominates a profile. Change one variable at a time.
   Start with one round on the target and a nearby passing canary; use three rounds to confirm
   a promising result. Preserve each trial's command, source diff/revision,
   binary hash, observations, and reason for keeping or rejecting it in a short
   experiment ledger. Revert unsuccessful temporary changes promptly.

   Verification follows the affected path. For example, use
   `cargo test --locked -p egglog --lib custom_set_rows_keep_canonical_input_and_output_proofs`
   or `constructor_merge_reads_a_dirty_view` for proof/merge changes, and
   `cargo test --locked -p egglog-core-relations --lib containers::tests` for
   container changes. Add a focused semantic regression only for a new invariant
   or demonstrated bug. Retain relevant output/check behavior on the real
   canaries. Avoid full-workspace validation between experiments.

5. **Check breadth, then collect final evidence once stable.** Screen all 127
   frozen inputs with a short comparison after a promising change; promote any
   new failure or ≥5× result into the focused canary set. At stabilization,
   collect ten fresh successful observations for each of off/proofs on every
   frozen input, with the same executable, resource profile and machine settings
   within each variant. Use `--rounds 10 --force-run --timeout-sec 500` and a
   task-owned report path; derive the ordered file arguments from `cohort.json`.

   Implement a task-local acceptance check over the raw rows/shared statistics:
   require all 127 unique input hashes, the pinned candidate binary, ten success
   rows per treatment/input, finite positive measurements, and both ratios
   strictly below 5. Reuse the existing independent Fieller calculations in
   `benchmarking/reports/analysis.py` / `benchmarking/figure_results.py`; retain
   per-replay means, intervals and absolute before/after costs. Missing or failed
   cases prevent acceptance. A faster off denominator can increase a ratio, so
   inspect absolute recording cost as well.

6. **Finish the figure and handoff.** Once acceptance passes, render recording
   with a full-range panel for each metric and omit the overview composition.
   Use the existing view-domain binding and omission path in
   `benchmarking/figures.py`; adjust the recording-only full-range policy and
   labels minimally if needed. Retain the frozen eligibility for the final
   artifact if fresh off timings cross the original 0.2-second cutoff, and keep
   Python exports and executed Vega membership/statistics in agreement.
   Display every in-scope result without clipping or changing workloads.

   Verify the final per-replay dataset and rendered geometry, rerun the affected
   focused tests, and run `UV_PYTHON=3.12 make check` once after substantive Rust
   changes stabilize, rather than after each trial. Inspect the final PDF at
   manuscript width, its fonts, and its numeric exports; update the paired paper
   branch. Preserve raw evidence, remove task-owned disposable scratch, and
   report achieved results and remaining limitations accurately.

## Risks and stop rules

- The container stack predates several downstream proof/backend changes;
  compatibility work must remain bounded and separately reviewable.
- The saved Luminal setup attribution needs fresh confirmation. Container work
  may help DialEgg RSS without closing Luminal's setup costs.
- A frontend hotspot does not reopen the deferred typed-generation/authoring API
  redesign. If the existing pipeline cannot meet the target with small changes,
  report that limitation instead of expanding the architecture scope.
- The current CDF recalculates eligibility from off timing. The frozen 127-input
  acceptance set must stay explicit throughout performance and figure work.
- If focused experiments leave any ratio ≥5×, keep that case visible, record the
  remaining bottleneck, and leave the performance goal incomplete. Exhausting
  useful small experiments does not justify claiming the target was reached.
