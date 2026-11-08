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

The figure placement correction is complete: source commit `f92a05ad`, paired
paper commit `d104431` on `codex/fix-recording-overview` in
`/Users/saul/p/wt/extended-egglog-paper/fix-recording-overview`.
[figure-validation.json](figure-validation.json) records 23 passing figure tests,
unchanged statistics for all 254 metric points, and PDF visual/font checks.
No fresh performance measurements or performance implementation changes have
been made during setup. Historical leads and the deferred work are recorded in
[paper-attribution.json](paper-attribution.json) and
[deferred-work.json](deferred-work.json).

## Done condition

All 127 input identities have ten fresh successful off and proofs observations
on the stabilized candidate, and every per-replay runtime and peak-RSS ratio of
arithmetic means is strictly below 5. Relevant correctness checks and final
validation pass, per-replay means/95% intervals and reproducible evidence are
retained, and the recording figure shows both full metric ranges without
zoom/overview panels. Missing results or any remaining ratio ≥5× leave the goal
incomplete; do not change the cohort, reduce semantic work, or revive the deferred
typed architecture to claim completion.
