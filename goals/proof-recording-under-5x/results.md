# Proof recording progress

The goal is **not complete**. No accepted final dataset exists for the current candidate.

The initial figure placement fix is committed. Native Math correctness now runs
in a separate uncapped process, and both native and guarded source Math checks
pass (2 tests, 504.35 seconds). The completed broad paper run passed the other
510 tests; its sole old failure was the native Math memory guard.

The current branch is `codex/proof-recording-outliers`, with engine base `c0f9c91f` and one
experimental performance line reserving the known assignment-map capacity.
The borrowed annotation lookup and signature caches were rejected. The latest
ten-round focused screen measures Gemma at 5.167×, MoE at 4.574×, and the MISAAL
control at 4.026×. Concurrent host activity leaves timing highly variable.

A scheduling decision for a quiet final timing window is waiting in the
[Plannotator Inbox](http://localhost:61603/#thread=msg_01M6WHM6M69MPAERHKE0P92GQ5).
Final CI-profile checks pass. The required fresh ten-round collection on all
127 frozen inputs, acceptance audit, final figure and paper refresh remain.

The paper has been restored to the committed original-data layout fix. The
provisional optimized bundle and first ten-round data use rejected source
`915fec1c` and remain archived as experimental evidence. Its unconditional
flat map passed plotted ratios but regressed the file suite to 147.41 seconds.
The retained persistent snapshot policy fixes that regression. Rejected results
remain under explicit `e021-*` evidence names.

See [the experiment ledger](experiments.md), [the approved plan](plan.md), and
[the frozen cohort](cohort.json). The deferred typed-generation conversion and
new Rust authoring API remain excluded.
