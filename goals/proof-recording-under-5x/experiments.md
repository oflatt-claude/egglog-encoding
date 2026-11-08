# Performance experiment ledger

The target and fixed input population remain [facts.md](facts.md) and
[cohort.json](cohort.json). The typed generation / Rust authoring API conversion
remains deferred.

**Final retained result:** [E031 below](#e031--final-stabilized-collection-and-handoff)
and [results.md](results.md) supersede the earlier provisional collections.
All 127 mean runtime/RSS ratios pass on `ede9f943`; Gemma's runtime confidence
interval still crosses 5×. The earlier slow observations and rejected variants
remain in this historical ledger.

## E000 — fresh baseline

- Status: complete; 18/18 successful runs, three observations per input/treatment.
- Source: `e8a2a58d501bc762b7a35441edb98ed0c301b73c` in the frozen local checkout
  `.bench-worktrees/baseline/`; 16 GiB allocator cap, 60-second process timeout.
- Exact invocation: the three-input baseline command in `plan.md`.
- Raw observations and public report: ignored
  `benchmarks/local/proof-recording-under-5x/baseline.{jsonl,md,log}`.
- Outcome: Gemma runtime is about 7.1× off; Gemma4 MoE runtime about 6.3×;
  DialEgg peak RSS about 6.7× (892 MiB versus 133 MiB). The outliers reproduce.
- Fresh phase decomposition: typechecking plus other frontend work accounts for
  about 72% / 68% of Gemma / Gemma4 MoE's added wall time; DialEgg's added time
  is primarily program execution/rebuilding. No memory mechanism is inferred
  from CPU/phase timings alone.

## E001 — Eli's sequence-container stack integration

- Status: bounded integration attempted; blocked by a broad compatibility port.
- Upstream PR #985 live tip: `df7e28de604546c747435eabab89fd935e83e7d1`;
  complete stack base `b912caa9694c0c029f9ae3d91db0adc8824e14f5`.
- Upstream checkout: `/Users/saul/p/wt/egglog/pr985-codex-inline-containers`.
- Isolated downstream experiment:
  `/Users/saul/p/wt/egglog-encoding/proof-recording-eli-containers`, base `e8a2a58d`.
- Probe: exact upstream stack patch applied under `egglog/`, preserving the
  root workspace and excluding upstream root Cargo manifest/lockfile.
- Outcome: three-way application conflicts in 13 files / 22 regions, including
  container maintenance, dependency graph, execution actions, the newer packed
  join executor, bridge registration, and Vec/Map/Set/UnstableFn primitives.
  The stack replaces the legacy container-value contract with sequence
  encode/decode/rebuild operations. This is not a small drop-in change to this
  downstream revision.
- Evidence: ignored `eli-containers.patch`, `eli-apply-check.log`,
  `eli-integration.log`, `eli-conflicted-files.json`, and
  `eli-integration-conflicts.patch` beside the baseline report.
- Disposition: retained the evidence and restored the experimental worktree to
  its clean base. No claim about this stack's performance on the current proof
  encoder is established. Pursue small changes in the current implementation.

## E002 — baseline CPU profile

- Status: complete, using the explicit frozen baseline path.
- Competing explanations: (a) constraint solving / repeated resolution dominates
  generated setup; (b) AST construction, traversal/cloning, or installation
  dominates. The confirming/disconfirming probe is a sampled call-stack profile
  alongside the already collected phase breakdown.
- Target: Gemma, `proofs`, approximately ten sampled seconds, 60-second watchdog;
  public `./bench.py profile` command, with `--target` set to the absolute frozen
  `.bench-worktrees/baseline` path.
- A rejected initial attempt used `@e8a2a58d`, which selected the then-clean
  integration worktree. Its source changed during the profile build. That
  process tree was stopped and its artifacts moved to ignored
  `rejected-ref-profile/`; none of its measurements are accepted.
- The corrected build disables the compiler wrapper for this diagnostic and
  uses a clean, immutable source path. Future baseline/profile comparisons use
  this explicit path instead of relying on a ref to choose among clean worktrees.

## Memory hypotheses to distinguish

- M1: retained Rust/container bookkeeping dominates DialEgg's additional RSS.
- M2: proof rows, join indexes, and execution buffers dominate that RSS.
- Next probe: allocator statistics plus table/state counts on separate
  diagnostic runs of the unchanged actual DialEgg input. Profile CPU shares
  will not be used as allocation evidence.

- Valid artifact: `profiles/v5/bab3ec59e04333a14a2aa1ddeb798c888ae3d1435d60388b8c9c531bed19001c/48e976d7ad8efaae76eade21c6cad033b4bb4de26fc5536fcd6af9ac6e33ee96/proofs-nee-auto10s.json.gz` under the ignored task directory.
- Inclusive sampled CPU: typechecking 42.3%, standalone actions 38.5%, constraint solving 15.2%, expression annotation 13.7%, primitive compatibility 9.5%. Shares overlap. See `gemma-profile-inclusive.json` for caller stacks.

## E003 / E004 — known primitive signatures

- Added an optional exact signature check to the existing type-constraint interface; custom constraints retain the original solver. No source-generation pipeline or authoring API change.
- E003 checks `SimpleTypeConstraint` signatures by sort names and arity. One-round exploratory Gemma recording was 2.38 s; added typecheck time decreased from approximately 939 ms to 842 ms, but whole-process timing did not establish a gain by itself.
- E004 also handles `get-fresh!`'s placeholder signature directly, preserving the original distinction between inference over real string arguments and overload resolution over placeholders. Gemma recording was 2.18 s versus fresh baseline mean 2.37 s; Gemma4 MoE was 4.18 s versus 4.40 s. Ratios remain 6.48x / 5.96x. These are exploratory one-round results, not acceptance evidence.
- Exact source patches and raw observations: `e003-simple-signature.*`, `e004-fresh-signature.*` under the ignored task directory. Add differential constraint and existing capability/ambiguity checks before retaining.

## DialEgg memory localization

- Diagnostic input copies stop immediately before saturation or append `print-size` after the unchanged program. These are not benchmark observations.
- Before saturation: off 9.4 MiB, proofs 14.6 MiB peak RSS. Full run: off 132.9 MiB, proofs 892.4 MiB. Growth is in execution, not initial declaration storage.
- Visible table counts match exactly: 188,037 rows in 51 tables, including 88,560 matmul and cost rows each.
- A temporary diagnostic build exposes hidden rows: recording has 17,109,587 rows in 81 tables, led by 8,737,023 RuleLink rows and 2,863,070 each of Congr and Rule_6 rows. Off has 188,279 rows including globals. Additional proof state is substantial; allocator end statistics alone do not distinguish it from transient buffers.
- Temporary capacity counters also show large contiguous flat buffers (RuleLink: 97,275,408-cell capacity near 52 million used cells). This motivates testing storage growth separately from proof semantics.
- Diagnostics and exact temporary source patches live under `diagnostics/` in the ignored task directory; restore that isolated worktree after capturing evidence.

## E005 — exact contiguous flat-buffer growth

- Changed `RowBuffer::reserve` to `reserve_exact`; this also affects sorted-write table buffers, so the probe did not isolate flat-table growth. No semantic changes.
- One-round RSS was 828 MiB versus baseline 892 MiB, still above target. The run also overlapped a diagnostic build. Its wall times cannot isolate either the flat-storage effect or scheduling contention.
- Disposition: patch saved as `e005-exact-flat-growth.patch`, source reverted. Try retaining submitted chunks to avoid old-buffer copies entirely, rather than repeated exact reallocations.

## E006 — retain flat-table chunks

- Status: all ten focused flat-table tests pass, including bounded/sparse scans split across four batches. One-round DialEgg RSS falls to 724.7 MiB (5.46x), versus 892.3 MiB baseline. This improves the target but does not meet it.
- Hypothesis: contiguous append growth adds substantial peak memory above retained proof data. Store already submitted immutable row batches without copying old rows, preserving all rows, logical row IDs, scans, snapshots and clear/version behavior.
- Prediction: recording RSS decreases with identical row counts; off remains unaffected because these proof tables alone use flat storage. Existing flat-table tests exercise duplicates, deltas, bounded/sparse scans, concurrent buffers, clone isolation and late buffers after clear.


## E007 — compact whole-row chunks

- Converted each incoming chunk to a boxed flat slice. Eleven-column proof batches retain constant rule names, proof-column numbers, Unit and timestamps once per row.
- The focused ten-test storage suite passes. DialEgg RSS rises to 771.2 MiB (5.81x), consistent with extra compacted copies plus pooled source buffers; this is not a confirmed attribution of individual allocations.
- Disposition: saved `e007-compact-chunks.patch`; replaced by the next more selective representation, not retained as a finished fix.

## E008 — constant columns within immutable chunks

- Status: all eleven focused flat-table tests pass. DialEgg recording RSS is 571.2 MiB versus off 132.8 MiB, a 4.30x exploratory ratio; the same value reproduces in E009. Strict proof and all-cohort checks remain pending.
- Hypothesis: many of the millions of proof rows repeat the same value in a column throughout an incoming batch (e.g. Unit, timestamp, rule name or proof-column number). Keep constant columns once per batch and store every varying value exactly.
- Prediction: fewer retained bytes with exactly the same logical rows, duplicates, physical column values and IDs. Disconfirmation: no meaningful RSS reduction, any changed row values/counts, or failing sparse/bounded scan, snapshot or parallel-buffer behavior.
- This is one private generic table representation change. It does not discard proof rows, change proof encoding semantics, alter allocator settings, or touch the deferred typed pipeline.
- Added a cross-batch constant/variable-column regression to the existing storage suite. Full proof-focused checks are still required before retaining this candidate.


## E009 — fixed-sort fresh primitives

- The encoder emits a nullary fresh primitive whose fixed signature is derived from the declared sort, rather than passing the sort name as a string on every fresh call. It still emits text through the original parser, typechecker, and evaluator. The generic fresh form remains available for replay compatibility.
- One-round recording times: Gemma 2.065 s / off 0.334 s (6.18x); Gemma4 MoE 3.944 s / off 0.694 s (5.69x). RSS remains 571.2 MiB on DialEgg (4.30x). All six runs succeed.
- This does not yet close runtime. Before retaining, constrain registration to encoded/replayed programs (avoid expanding the native user namespace), and check sanitization/replay, scope, capability and ambiguity behavior.

## E010 — flat assignment map probe

- Status: one round succeeds. Gemma recording 2.006 s (6.06x); Gemma4 MoE 3.816 s (5.51x). The small change has only a modest gain and needs a broader overload-heavy canary before retention.
- Competing costs: persistent-map lookup/node allocation versus copying assignments during overload backtracking. Replace only the assignment map implementation, preserving key equality, hasher, constraint order and rollback by cloning.
- Prediction: monomorphic generated action typing may get faster; disconfirmation is extra cloning making overload-heavy typing slower or any changed inference/errors. If it regresses, revert immediately and keep persistent storage.


## E011 — read already-bound globals directly

- Status: one round succeeds: Gemma 1.926 s (5.69x), Gemma4 MoE 3.684 s (5.35x); DialEgg RSS remains about 571 MiB. A later focused test caught primitive globals taking this eq-sort-only path; E017 restores their original direct function read.
- Existing encoding reads a bound eq-sort global through set-if-empty, minting two unused fallback ids at each read. The original source typechecker already requires the binding to exist.
- Generalize the existing source-output reader from nullary custom-function roots to keyed global views. Ordinary action/extract reads use it directly; merge-body lookup retains its existing fallback and dependency handling.
- Prediction: remove two redundant fresh calls per eq-sort global read, reducing generated AST/constraint/evaluator work while reading the same committed canonical value. Disconfirmation: changed reads after union or scope, missing staged/global values, replay failure, or no useful timing gain.
- Before retention, exercise checked eq-sort globals after unions and push/pop, term-only rules, existing merge-global fixtures, sanitized replay, and primitive-context checks.


## E012 — constructor bindings in ordinary typing (rejected)

- Extended the existing closed-constructor fast path to typed-global leaves and `let` bindings. The existing differential oracle passes across contexts and spans before and after the extension.
- Gemma off improves from about 338 ms to 296 ms while recording remains about 1.95 s, increasing its recording/off ratio to 6.59x. This optimizes the shared source pass rather than the recording overhead.
- Disposition: source and oracle changes reverted; `e012-constructor-bindings.patch` and measurements retained as evidence.

## E013 — parse the generated local scope directly

- Emit generated actions inside the existing `(begin ...)` syntax, preserving their local scope while avoiding a temporary command vector per action and the subsequent regrouping pass. Pending declarations remain outside the block; empty blocks remain omitted.
- Removed the single-use regrouping helper. One-round Gemma / Gemma4 MoE recording times: 1.836 s / 3.572 s. Their ratios remain 5.76x / 5.29x.

## E014 — unused bare fresh ids

- Track the bare fresh-id variables emitted by this encoder. After ordinary parsing, remove only unread bindings among those identities from local action blocks and rule heads. Keep arbitrary primitives, string literals, global commands that may be read later, and all written proof rows.
- One-round Gemma / Gemma4 MoE: 1.815 s / 3.420 s, ratios 5.45x / 4.73x. RSS falls to 182 / 259 MiB; DialEgg remains 571 MiB (4.30x).
- Scope/literal/user-primitive regression added during stabilization.

## E015 — no panic fallback for non-failing fresh calls

- The bridge now owns a fresh-id entrypoint that always returns `Some`. Its calls lower through the existing non-fallback external instruction. This avoids registering an unreachable lazy panic callback per fresh call; arbitrary primitives retain their existing fallback and failure behavior.
- One-round Gemma / Gemma4 MoE: 1.759 s / 3.411 s, ratios 5.37x / 4.97x. RSS falls to 167 / 233 MiB. New bridge regression verifies distinct ids, no additional panic-function registration, and metadata cleanup.

## E016 — mint the canonical id only on an interning miss

- Add an internal view-interner variant: keys plus proof payload in, canonical id out. Its external path uses the existing prediction-aware multi-output insertion, with a counter default; its lowered path uses existing `LookupOrInsertDefault` and `WriteVal::IncCounter`.
- Constructor encoding replaces an eager bare fresh call plus set-if-empty with one interning call. Other supplied-output writes keep the original operation. Existing and pending rows reuse their canonical id and proof payload.
- All six exploratory runs succeed. Runtime ratios: Gemma 4.94x (1.624 s / 0.329 s), Gemma4 MoE 4.56x (3.074 s / 0.674 s), DialEgg 1.85x. RSS ratios: 2.82x, 2.79x, 4.29x respectively (DialEgg 570.8 MiB / 133.0 MiB).
- These are one-round observations, not goal acceptance. Exact patches and all raw observations remain under the ignored task directory.

## E017 — minimize and check the candidate

- Reverted E009's per-sort fresh primitive family and E010's flat assignment map, retaining the original generic fresh syntax, native namespace, and persistent-map API. Their earlier small gains need not complicate the final patch after removing redundant calls.
- Added an external-vs-lowered interning regression for duplicate pending keys, committed hits, retained first payload and counter increments only on a miss. Added a differential signature check against general solving and the fresh-liveness scope/literal test.
- First broad focused run: 213/217 egglog library tests passed. Two failures exposed primitive globals being routed to an eq-sort-only reader; fixed by retaining their original function-read path. The other two are inspected documentation snapshots whose fresh+set-if-empty sequence becomes one intern call; updated those two only, without metadata churn.
- The newly added bridge test initially had an invalid tuple-merge fixture; corrected its merge arity before assessing the implementation.
- Focused checks now pass: all 35 bridge tests, all 219 egglog library tests, and both typed primitive/termdag integration suites. The interning test uses before/after fresh-id probes within each batch, respecting the allocator's counter reservations. Three-round remeasurement of this minimized source is running before extending collection.

- Minimized three-round result: Gemma recording/off 4.992x (1.648 s / 0.330 s), Gemma4 MoE 4.755x (3.225 s / 0.678 s), DialEgg RSS 4.291x (570.7 / 133.0 MiB). All 18 observations succeed. Gemma's interval crosses 5, so this is still exploratory evidence.

## E018 — batch fixed-signature assignments (rejected)

- A private contiguous assignment batch preserves assignment order, first errors, partial progress and pretty-print composition. All 220 library tests, including the differential update test, pass.
- One-round Gemma is 1.635 s / off 0.340 s (4.80x), but recording typecheck changes only from 544 ms to 537 ms. Much of the apparent ratio improvement comes from the off denominator; the recording gain is too small to establish with this probe.
- Disposition: saved exact patch and observations, then reverted the batch implementation and its extra test. Keep the smaller E017 constraint interface and persistent assignment map.
- Stabilizing the reviewed interning, liveness, fixed-signature and storage changes; run the required full check once, then collect the fixed cohort. No change to input schedules or allocator policy.

## E019 — frozen-cohort screen

- Candidate source is pinned as `ec8bea0b` (constant-column proof storage) plus `81db104d` (generated-action/fresh-id work). The source-generation/parser/typechecker architecture remains unchanged.
- Broad check: formatting, linting, docs, 1,071 Python tests (2 skipped), and workspace Rust tests pass. Interrupted the lengthy paper-corpus section after 130 successful paper benchmark tests and no unexpected failures, before final timing. This is **not** a completed `make check`; a final full check remains required after performance stabilization.
- Rationale for deferring the remainder: Gemma is still close to 5x, so screen the whole frozen population before paying for a full corpus validation cycle on a potentially insufficient candidate.
- Collection uses the public CLI, exactly the 127 frozen byte identities, one fresh off and proofs observation per input, timeout 500 seconds and the unchanged 16 GiB allocator profile. Exact argv, source revision/patch hash, UTC bounds, executable hash, raw samples and phase output are retained in `e019-cohort-screen*` under the task evidence directory.
- Screen result: 254/254 successful observations. Gemma is the only failing runtime point at 5.057x (1.649 s / 0.326 s). Gemma4 MoE is 4.729x; the next-highest runtime point is 3.921x. Every memory point is below 5x; DialEgg remains the largest at 4.290x. The full-cohort acceptance checker confirms exactly one issue. No input is dropped or changed.
- No off mean in this screen falls below 0.2 seconds, but several are close. The figure binder now supports an explicit frozen-input cohort (default selection remains unchanged), with Python/export and executed-Vega checks. The final task catalog will select precisely these 127 identities.

## E020 — profile the remaining Gemma overhead

- Remaining alternatives: (1) repeated inference assignment lookup/node allocation still dominates generated typing, or (2) parsing/lowering/installing the generated local action program now dominates after removing redundant fresh operations.
- Re-profile the pinned minimized candidate on Gemma for ten sampled CPU seconds through `./bench.py profile`, using this exact worktree path rather than ref resolution. Retain the complete sampled artifact and summary. This diagnostic is separate from the successful 127-input timing screen.
- The next experiment must target a remaining sampled cost and preserve the existing source-generation, parser/typechecker and runtime contracts. Do not expand the typed-generation design.
- Current profile: 6 iterations, 10.05 sampled CPU seconds; 33.2% in typechecking, 29.4% in standalone-action typing, 9.7% in constraint solving, 6.3% in action annotation, and 8.2% in parsing (inclusive and overlapping). The analyzer resolves 96.3% of application leaf CPU; unresolved frames remain explicit. Exact artifact and inclusive summary are retained separately from baseline profiling.

## E021 — revisit the assignment map on the remaining outlier

- Revisit E010 as one controlled storage change on the minimized candidate: replace the constraint assignment map with the existing `hashbrown` dependency, retaining the same keys, values, Fx hasher, constraint order and branch-clone/rollback algorithm. Update comments to describe cloning honestly.
- Prediction: recording inference/annotation loses persistent-node lookup/allocation overhead; a three-round Gemma timing must show a useful absolute reduction, not only a slower off denominator. Competing risk: cloning a flat map increases overload-branch costs. Run library/typed API tests and include the second Luminal and an execution-heavy MISAAL control in timing. Revert if insufficient or regressive.
- Result: all 219 library tests pass and all 24 timing observations succeed. Gemma recording falls from E017's 1.648 s to 1.566 s, while off falls from 0.330 s to 0.321 s: ratio 4.878x. Added recording typecheck time falls from about 487 ms to 415 ms, supporting the intended mechanism rather than an off-denominator artifact.
- Gemma4 MoE is 4.602x (3.052 s / 0.663 s); the MISAAL matmul control is 3.704x (0.870 s / 0.235 s). DialEgg memory stays 4.295x. Retain this tiny implementation change. `Assignment`'s concrete public map type now uses `hashbrown`; branch clones are O(n) instead of persistent snapshots, so final workspace/overload checks and the full-cohort audit remain required.
- Source commit: `915fec1c`.

## First full collection — superseded (`915fec1c`)

- Stabilized candidate collection requests exactly ten new off/proofs observations on each frozen identity, one executable and the unchanged 500-second / 16 GiB resource profile. The new report path prevents reuse of exploratory rows.
- The final goal is still pending until the complete 127-case acceptance audit, the complete `make check`, and the final full-range figure/PDF audit pass.
- Final timing audit passes: all 2,540 new observations succeed, exactly ten per off/proofs/input on one pinned executable (`a8a54f23df1e731a227d3178f866d4b12148a88433a0c5fa814ea2205825eeaf`). All 127 runtime and memory mean ratios are strictly below 5x. Every 95% Fieller upper endpoint is also below 5x.
- Worst runtime: Gemma 4.972711x [4.949811, 4.995777]; Gemma4 MoE 4.590411x [4.577058, 4.603821]. Worst peak RSS: DialEgg 4.295025x [4.294840, 4.295210]. No timing acceptance issues remain.
- Four MISAAL off means are now below the historical 0.2-second cutoff. The explicitly frozen cohort keeps these four files in the final figure, retaining all 127 cases.
- Final correctness and real-data figure/PDF audits are now running. The goal remains active until those required checks finish.

## E022 — bound assignment snapshot cost

- The first ten-round collection at `915fec1c` passes every timing/RSS ratio, but final broad validation reveals a severe performance regression outside the plotted cohort: the 869-test file suite grows from 9.37 s on the persistent-map candidate to 147.41 s with the always-flat map. All 869 still pass; the last slow case is `stresstest_large_expr_desugar`. This prevents retaining the unconditional flat map despite its successful benchmark ratios.
- The residual risk predicted in E021 is realized: overload backtracking clones a large flat assignment map. Preserve cheap flat lookup for monomorphic inference and bounded small snapshots; promote large maps to the original persistent representation when a branch needs to clone them. The constraint order and rollback algorithm stay unchanged.
- Probe the exact large-expression round trip first, then remeasure Gemma/control cases. If both pass, repeat the complete fresh timing acceptance on the stabilized replacement; do not treat the earlier ten-round result as final evidence for different code.
- The initial final-check attempt is retained as `e021-make-check.log` and was stopped during the paper corpus after the regression was isolated. Sampling the old file-test PID was too late because that process had already exited; no sampled attribution is claimed.
- Simplified the storage rule to promote on the first branch snapshot, with no size threshold. Monomorphic inference keeps flat lookup; branching uses the original persistent map. A clone-count/isolation regression checks independent snapshots without copying large values repeatedly.
- Focused validation passes: 220 library tests, all 869 file tests in 9.49 seconds (versus 147.41 seconds for the unconditional flat map and 9.37 seconds before it), 13 typed-primitive tests and 9 typed-termdag tests. The first bounded-threshold prototype also passed the isolated large-expression test in 3.99 seconds; the retained rule is simpler and passes the complete file suite.
- Recheck the two Luminal inputs and a MISAAL control with ten short observations per endpoint before paying for another full-cohort collection. These results do not replace the required fresh final 127-input acceptance.
- Ten-round canary results: Gemma 4.986311x (1.57184 s / 0.31523 s), Gemma4 MoE 4.628054x, and MISAAL matmul 3.715120x; all 60 observations succeed. The file-suite regression is fixed, but Gemma's interval still crosses 5x, so test one further allocation reduction before final stabilization.

## E023 — reuse fixed signatures of internal proof primitives

- Internal mint/intern primitives return the same fixed sort vector for every constraint request, while inference and annotation currently allocate fresh constraint objects/signature vectors each time. Cache that metadata only for the private internal-registration path; public/custom primitive registrations retain their existing getter behavior.
- On valid-arity internal calls, use the same ordered assignment constraints directly from the cached sort vector; invalid arity retains the original getter and exact error/span path. Known-signature compatibility uses the same sort-name equality as before. This preserves generated text, parsing, ordinary inference, overload/context filtering and evaluation.
- Prediction: fewer temporary allocations in recording typing/annotation, with a useful absolute Gemma reduction. Differential fixed-signature checks and the focused library/file suites must pass; reject if allocation removal does not yield useful timing or changes diagnostics.
- Focused validation passes on the signature-cache candidate: all 220 library tests, all 869 file tests in 10.32 s, and both typed API suites. The differential signature test also passes after adding cached-vs-uncached internal mint checks across arities/type permutations and verifying ordinary public primitive registration remains uncached.
- Cache reuse is opt-in only through the existing private internal primitive registration. Generic fresh constraints and all public/custom primitive registrations keep their existing per-call path. Rechecking the three canaries with three fresh observations per endpoint now.
- E023 first layout: Gemma 1.5619 s recording / 0.3356 s off (4.654x), Gemma4 MoE 3.0182 s / 0.6819 s (4.426x). Absolute recording gains are modest; much of the ratio shift is a slower off denominator. Recording RSS also rises about 4–6 MiB. The signature field widens PrimitiveWithId, which is carried by resolved calls. Do not accept the favorable ratio alone.

## E024 — keep cached signatures behind the existing primitive Arc

- Keep the same cached metadata behind a private internal primitive adapter, without adding fields to PrimitiveWithId or resolved AST nodes. The adapter returns a small shared-signature constraint; valid-arity calls build the same ordered assignments, while invalid arity calls the original getter with the actual span.
- Public/custom primitive registration still calls its getter per request. The extended differential probe compares cached/uncached compatibility and constraints across arities/types, including the original arity error, and counts public getter invocations. Generated syntax, the normal solver and execution are unchanged.
- Prediction: retain the allocation saving without widening every resolved expression or increasing ordinary off allocation costs. Recheck absolute timing/RSS, not just ratios, before retention.
- E024 focused tests pass after fixing the diagnostic test fixture to use an actual span: 220 library tests, 869 file tests in 9.28 s, and both typed API suites. The initial fixture tried to pretty-print Span::Panic, which intentionally panics; this was a test-fixture issue, not a changed program diagnostic.
- E024 timing: Gemma 1.5983 s / off 0.3251 s (4.917x), Gemma4 MoE 3.1361 s / 0.6829 s (4.592x), and MISAAL 0.9031 s / 0.2439 s (3.703x). RSS returns to the pre-field sizes, but useful absolute recording improvement is not established.
- Disposition: reject both signature-cache layouts and restore source exactly to `c5d94ad8`. Keep the smaller existing signature checks and persistent-snapshot assignment policy, whose ten-round Gemma canary mean is 4.986x and whose full file suite takes 9.49 s. No additional metadata hook/cache adapter remains in production.
- Run the required full check to completion on this stabilized source before repeating the fresh full-cohort timing. The first full-cohort data at `915fec1c` remains valid evidence for that rejected variant, not acceptance evidence for `c5d94ad8`.

## Final validation resource diagnosis

- The stabilized `c5d94ad8` default-profile `make check` passes nits/docs, 1,072 Python tests (two skipped), workspace Rust tests, all 869 file tests in 9.61 s, and all 486 application corpus strict correctness replays. The remaining slow slotted reference checks are still running.
- The independent native Math12 `egg-proof-testing` condition fails with allocator-cap exit86 at the default 16 GiB guard. A focused reproduction fails the same way after211.87s, after term/off/strict/ordinary-native validation and during native checked proofs. A short process sample is in native egg rebuilding/explanations; the native Math driver, allocator crate and lockfile have no diff from the baseline. This is outside the127 recording target; its failure is retained, not a successful observation.
- The existing `benchmarks/ignore.json` already records Math12 proof-testing and native egg-proof-testing as unavailable under10GiB. No policy entry is added or broadened. A focused existing-profile run with `PAPER_TEST_MEMORY_LIMIT_BYTES=10737418240` passes its remaining Math term/off/native oracle in66.16s, with both proof-check conditions explicitly excluded.
- Final full validation will use that existing10GiB correctness profile. The project already has opt-level3 test builds. A proposed opt-level2 override was removed before the retry reached its tests; final validation reuses the original optimized builds/assertions with four test threads. This changes only verification execution; final recording collection remains500s/16GiB on the unchanged release executable, without competing CPU-heavy checks.
- The lowered-cap full retry is stopped after `csrmv-statewalk-call-03` fails at10GiB; that source replay already passed the original16GiB run. It is not a passing validation result. No exclusion entry has changed. The Inbox asks whether to extend the pre-existing native Math12 resource entry to its demonstrated16GiB limit; that decision is pending.
- The final c5 recording collection starts at2026-11-08T08:17:10Z with the same500s/16GiB settings and byte-identical127 inputs, checking the three original outliers first. The collector only changes selector order; the cohort file/hash is unchanged.
- The remaining native SDQL correctness reference is temporarily suspended while timed observations run, then resumed in the collector wrapper's finally clause. Its parent remains alive and the original125-minute five-mode correctness deadline still applies. The original full check and10GiB retry remain distinct logs. No CPU-heavy verification overlaps timing.
- Correction to the earlier timing interpretation: the paper deadline is500s×3 per mode, multiplied by the number of requested modes, so the five-mode SDQL trial has a125-minute deadline, not25minutes. Its long-running sample is native `slotted_egraphs::rewrite::multipat::multi_ematch`; neither that crate, the slotted-reference driver, nor paper-test source has a source diff from baseline.

- The user explicitly directs removing the memory guard for the native Math correctness test instead of extending its resource exclusion. That supersedes the Inbox question; no new ignore entry is authorized or added. Prepare a narrow test-only split: native egg Math comparisons run in a separate uncapped child from the uncapped parent, repeating off as their count oracle. The regular Math term/strict-proof checks keep the selected cap. The existing timeout remains. A capped child cannot remove its inherited hard VM limit.
- The prepared patch is `native-math-uncapped.patch`, apply-checked but held outside tracked source until the timed collection finishes. Recording workloads/binary/resource settings remain unchanged. Rerun the actual Math correctness case after applying it.

## E025 — fresh c5 screen and targeted reprofile

- Stop the fresh `final-cohort-v2` collection early and preserve its raw rows/provenance. Its first five Gemma pairs have a5.01937 mean ratio; this remains too borderline to justify the rest of a ten-round acceptance attempt. This is an incomplete exploratory screen, not final acceptance or a ten-round failure claim. The source is unchangedc5, binarya3050b10..., and the collector exits130 at the requested interruption.
- The reference suspension wrapper resumes native SDQL child55016 in finally; it is running again. The fresh public profile runs five Gemma iterations and observes10.38CPU seconds, with95.9% symbolicated application leaf CPU. Inclusive typechecking30.35%, standalone-actions typing26.76%, annotation actions6.21%, annotation expressions5.68%, solver7.00%, String cloning7.42%, and primitive compatibility1.27% overlap. Save `gemma-c5-profile-inclusive.json`; CPU samples are not allocation counts.
- Another independent benchmark collection and Lean work are also active on this host. Do not claim an idle machine or infer that all timing shifts are caused by code. The final candidate still needs the agreed fresh ten-round ratios and per-case intervals.

## E026 — avoid owned annotation lookup keys

- Competing explanations: annotation repeatedly allocates temporary `AtomTerm::Var` names for read-only sort lookups; alternatively remaining primitive constraint creation dominates. The new profile favors looking at annotation/string work before revisiting the rejected signature caches (compatibility now1.27% inclusive).
- Add a borrowed local-name query only for the flat assignment map. It hashes like the existing AtomTerm name and explicitly matches only local variables; a global with the same string has the same hash but is not equivalent. Persistent snapshots retain the original owned-key lookup. Replace the three annotation lookups; constraint solving, binding insertion, inference order, generated text and API remain unchanged.
- A focused regression covers local/global names with colliding hashes, a global-only name, an unbound name, Unicode names, and the persistent snapshot path. Prediction: lower annotation allocation/time and a useful absolute Gemma reduction, with unchanged controls. The test and timing results are pending.
- Native Math rerun succeeds after the user-requested guard change: the uncapped native proof/iteration/count comparison and the separate16GiB-capped source term/off/strict proof checks both pass (2tests,504.35s). Registration at10GiB also keeps the native proof check enabled/uncapped while the source strict mode retains its existing cap-specific exclusion. Commitc0f9c91f contains only the test-process split and its documentation. No ignore entry changes.
- E026 focused validation passes:221library tests (including borrowed local/global collisions and snapshots),869file tests in20.27s while other work runs, and the isolated large-expression desugaring case in4.23s (the earlier persistent-snapshot prototype was3.99s). This has no recurrence of the unconditional-map147s regression. Begin the three-round Luminal/MISAAL comparison with the actual source diff saved in e026-borrowed-annotation.patch.
- E026 first three-round timing succeeds on all18observations but is inconclusive: independent Rust compilation is active during it, and MoE recording ranges3.24–7.20s on one executable. Other endpoints also vary sharply. Do not accept/reject the lookup change from these mean ratios or attribute that variance to code.
- Prepare an explicit clean `c0f9c91f` control worktree (same C5 engine, before borrowed lookup), reusing cloned compatible release dependencies. Compare control proofs directly against candidate proofs through the public runner with ten observations per endpoint on the two Luminal inputs and MISAAL control. Keep exact binary/source identities and use fresh off/proofs collection only after a useful change is retained.
- The direct E026 comparison finishes all60observations successfully. Its independent Fieller intervals remain wide and include no change: Gemma candidate/control0.783[0.557,1.319], MoE0.815[0.575,1.390], MISAAL1.009[0.581,1.696]. Extreme control rounds (Gemma5.415s,MoE10.539s) dominate the raw means; do not claim a19–22% causal speedup. The small borrowed-key change is retained as a direct elimination of redundant owned-key allocations, with its measured uncertainty explicit; commit758ef987. The final frozen-cohort criterion remains unmet.
- The original full paper trial set completes:510passed,1failed,7043.03s. Its sole failure is the native Math16GiB guard case, now flipped by the independently passing uncapped/native + capped/source Math rerun (2tests). The long SDQL reference passes. ReferencePID55016 has exited; never signal it again. Final nits/workspace/figure validation still needs to cover the eventual stabilized source.

## E027 — reserve known assignment capacity

- The C5 profile also shows several raw-table growth/rehash paths. Every Problem already computes the required-variable set before solving; reserve that many flat-map entries once, keeping the existing inference/assignment/snapshot behavior.
- One implementation line, no new API or constraint representation. Existing library error and snapshot tests cover semantics; do not add a test that merely mirrors reserve. Prediction: less hash-table growth for large generated action blocks and a small absolute reduction on Gemma. Reject if timing or the known branching stress case regresses.
- E027 combined trial:221library tests pass. All18canary observations succeed; Gemma mean4.801× (off0.33664s, recording1.61609s), MoE5.457× (off0.68603s, recording3.74349s), MISAAL3.757×. The MoE result includes a slow recording observation; retain it in full. Host-load samples are saved, and no full acceptance is claimed.

## E028 — reserve capacity alone, discard unestablished borrowed lookup

- Reduce the final candidate further: the borrowed-key trial does not establish a useful gain with its wide intervals, so remove its helper, three call-site edits and regression. Its patch/data/commit identity remain experimental evidence. Drop only the unpublished E026 trial commit from the task branch; the user-requested native Math guard commitc0f9c91f remains.
- The only additional performance diff againstc0f9c91f is now `assignment.0.flat.reserve(self.range.len())`. Measure this one variable independently, with the library suite and the same three-case comparison. E026 is **not retained** and must not appear in the final implementation summary as an accepted optimization.
- E028 reserve-only library suite passes220tests. All18three-round canary observations succeed: Gemma5.1366× (recording1.68615s/off0.32826s; recording values1.6188,1.6451,1.7945s), MoE4.5911×, MISAAL3.7214×. Keep the slow Gemma observation. This does not meet even the preliminary mean target, and no final acceptance is claimed.
- E029 repeats the same reserve-only source on the fixed three canaries with ten fresh observations per treatment, before choosing whether to keep it or try another small reduction. Source remainsc0f9c91f plus the one-line reserve; E026 is removed. Use the fresh report e029-reserve-confirmation.jsonl and retained host-load/provenance captures.
- E029 ten-round reserve-only confirmation completes60successful observations: Gemma5.167474× (recording1.872926s/off0.362445s), MoE4.573978×, MISAAL4.026213×. The target remains unmet. No final127-input acceptance is available.
- Local CI-profile `RUST_TEST_ARGS='--skip paper/' UV_PYTHON=3.12 make check` passes on the one-line capacity trial. This uses the repository CI skip-paper profile; the separate broad paper run and passing repaired-Math rerun supply the stated paper coverage. Do not call the original failed marker a passing full invocation.
- The paper is restored to committedd104431 (corrected overview placement, original data), and rebuilds successfully. Its rejected915optimized bundle is saved under e021-paper-bundle. Remove stale canonical accepted JSON copies until genuinely new acceptance exists.
- Resource priority is now awaiting the person: Inbox question msg_01M6X7F2ED631CKMFF9H3TKF4H/q-35f73949 asks whether to coordinate a30-minute quiet timing window with the other active Codex tasks. No other task/process has been interrupted or messaged. Continue independent preparation; do not claim controlled timings or interrupt other work without that answer.

## E030 — revalidate the host confounder without interrupting other tasks

- Previous goal turn is progress: the user-requested Math guard fix and actual rerun, completed CI-profile checks, restored honest paper figure, and committed evidence changed authoritative state. The goal remains incomplete.
- On continuation, the bulk collector is confirmed live (PID65125); no Rust/Lean compiler currently appears among CPU-heavy processes. The Inbox timing-priority choice is still open. That choice is needed before disrupting other tasks; it does not forbid our own non-disruptive diagnostics or establish a user requirement that every other job must stop.
- Run one short ten-round Gemma-only public comparison with host-load capture, on the unchanged reserve-only candidate, leaving the other task untouched. This distinguishes the earlier loaded multi-case result from the current lighter host state. It is not final127-input acceptance and will not justify dropping slow observations.
- E030 current lighter-load diagnostic completes20/20successful observations: Gemma off0.320651s, recording1.593112s, ratio4.968363×. The ten recording observations cluster1.5867–1.5990s, unlike the earlier multi-second outliers. The remaining bulk collector is left untouched. This is a promising focused result, not final127-input acceptance.
- Stabilize the smallest candidate: retain the one-line assignment capacity reservation with the previously verified snapshot policy. Existing CI-profile checks cover this exact source patch, and the separate broad paper coverage plus repaired Math rerun are retained. Begin a new complete frozen-cohort ten-round collection; do not reuse incompletev2 or rejected915data.

## E031 — final stabilized collection and handoff

- Source `ede9f94368994e403893e55edf6e35ec66c826b2`, executable
  `b9b6cd18c23a141db285c0f5f91864d589023e1abfece0d56a0fe67a9a97c517`.
  The final collector runs from 2026-11-08T10:03:36Z to 10:28:51Z, with
  identical start/end source pins and an empty tracked-source patch. An
  untracked task checkpoint explains the raw rows' dirty-checkout flag.
- `final-cohort-v3.jsonl` contains exactly 2,540 new successful observations,
  ten per off/proofs endpoint on all 127 frozen input hashes. Timeout remains
  500 seconds and the allocator cap 16 GiB. No exploratory or failed observation
  is substituted into this dataset. The collector and finalizer both exit 0.
- Acceptance passes every runtime and peak-RSS mean ratio. Gemma has the largest
  runtime ratio, 4.978895× [4.914324, 5.044428], from off 0.321648 s and recording
  1.601452 s. Its interval crosses 5×; only the mean criterion is satisfied.
  Gemma4 MoE is 4.598648× [4.528812, 4.669719]. DialEgg has the largest memory
  ratio, 4.294365× [4.294170, 4.294560], from 132.881 MiB to 570.641 MiB.
- Public figure rendering reuses all 2,540 cached rows and leaves the raw JSONL
  byte-identical. The executed Vega audit passes all 254 plotted points,
  127 identities per metric, full ranks, in-bounds geometry and the absence of
  overview panels. Numeric-export auditing matches all 254 condition means and
  intervals, all 127 comparisons, and 3,556 per-replay TeX macros.
- Local CI-profile checks pass on byte-identical final non-goal source. The
  earlier full paper trial remains 510 passed / one native Math guard failure;
  the actual uncapped-native/capped-source Math rerun passes both tests after
  commit `c0f9c91f`. No exclusion is added. The failed default invocation and
  interrupted lower-cap attempt retain their original nonzero status.
- The paper update is committed at `3045d9e` on `codex/fix-recording-overview`.
  `make main.pdf` succeeds; the recording figure is inspected at manuscript
  width on page 26, every figure font is embedded, and its PDF/macros/table
  match the accepted exports byte-for-byte. Other figure bundles are unchanged.
- Canonical final evidence is now [results.md](results.md),
  [final-acceptance.json](final-acceptance.json),
  [final-validation.json](final-validation.json), and
  [final-handoff.json](final-handoff.json). Earlier `final-cohort`/`final-cohort-v2`
  evidence remains explicitly superseded. Signature-cache and borrowed-key
  experiments are discarded; the strongly typed generation/API rewrite stays
  deferred, and Eli's incompatible stack remains unmeasured.
