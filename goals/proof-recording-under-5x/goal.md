# Proof recording below 5×

Bring both recording/off whole-process runtime and peak-RSS ratios below 5× for
every one of the 127 frozen paper replays, preserving their inputs and semantic
work. Identify bottlenecks first, evaluate Eli's sequence-backed container stack,
then use small proof-encoding or engine changes with fast, focused iteration.
The earlier encoder-wide typed generation conversion and a new strongly typed
Rust authoring API remain deferred.

The shared understanding is [facts.md](facts.md), including the user's explicit
typed-generation deferral. The approved execution plan is [plan.md](plan.md);
[plan-review-result.json](plan-review-result.json) records approval without
annotations. [cohort.json](cohort.json) fixes the acceptance input identities.

## Workspace and starting state

Execute in `/Users/saul/p/wt/egglog-encoding/proof-recording-outliers`, on
`codex/proof-recording-outliers`; the performance baseline is `e8a2a58d`.
The primary checkout and unrelated typed-API work are dirty and must be preserved.

The initial figure placement correction is complete: source commit `f92a05ad`, paired
paper commit `d104431` on `codex/fix-recording-overview` in
`/Users/saul/p/wt/extended-egglog-paper/fix-recording-overview`.
[figure-validation.json](figure-validation.json) records 23 passing figure tests,
unchanged statistics for all 254 metric points, and PDF visual/font checks.
At setup, no fresh performance measurements or performance implementation changes
had been made. Historical leads and the deferred work are recorded in
[paper-attribution.json](paper-attribution.json) and
[deferred-work.json](deferred-work.json).

## Completion evidence

The stabilized source is `ede9f94368994e403893e55edf6e35ec66c826b2`.
All 2,540 fresh observations succeed on the original 127 inputs, and every
runtime and peak-RSS mean ratio is below 5×. The limiting runtime case is Gemma
at 4.978895×, with a 95% Fieller interval of [4.914324, 5.044428]; acceptance is
defined on means, so this retains the uncertainty around the threshold.

[Results](results.md) report all per-replay means and intervals, source changes,
rejected experiments, API caveats and reproduction commands. The
[acceptance dataset](final-acceptance.json), [figure audit](figure-audit.json),
[numeric-export audit](numeric-export-audit.json), and
[final handoff](final-handoff.json) pin the complete evidence. The paper branch
now contains the accepted full-range figure without overviews at `3045d9e`.

[Final validation](final-validation.json) distinguishes the passing local
CI-profile `make check`, the earlier broad paper run (510 passed, one native Math
guard failure), and the passing two-test Math rerun after the user-requested
uncapped native process split. The original failed full invocation remains
explicit. No resource exclusion or benchmark guard was changed.

## Done condition

All 127 input identities have ten fresh successful off and proofs observations
on the stabilized candidate, and every per-replay runtime and peak-RSS ratio of
arithmetic means is strictly below 5. Relevant correctness checks and final
validation pass, per-replay means/95% intervals and reproducible evidence are
retained, and the recording figure shows both full metric ranges without
zoom/overview panels. Missing results or any remaining ratio ≥5× leave the goal
incomplete; do not change the cohort, reduce semantic work, or revive the deferred
typed architecture to claim completion.
