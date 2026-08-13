# Where Current Term-Encoding Time Goes

Status: measured diagnostic on current `origin/main`, followed by the retained
V3 phase-timing implementation documented in the evidence ledger below.

Baseline commit: `5ead0a0cacf847a129294a870de13503f2d7f9c4`

This commit includes PR #61, which records direct ruleset runs in the overall
report. That fix is necessary, but it does not account for rule planning and
assembly or for the frontend pipeline outside ruleset execution.

## Short answer

There is no single dominant term-encoding cost across the benchmark suite.

- Math is dominated by replacing native rebuilding with `@rebuilding` and
  `@parent` plus the extra Apply/Merge work of the encoded representation.
- Pointer analysis is dominated by generating, desugaring, typechecking, and
  installing the encoded program. Its actual rule execution is tiny.
- Hardboiled is split between the generated frontend and slower transformed
  user rules.
- Luminal is dominated by two nearly equal costs: generated frontend work and
  planning/searching transformed user rules. Encoded UF/rebuild maintenance is
  only about 5.5% of its slowdown.
- Herbie is mixed across frontend, transformed user rules, encoded
  maintenance, and command work.
- eggcc is also mixed. A previously hidden ruleset-assembly cost is important:
  assembling `@rebuilding` and `@parent` costs about 253 ms, before their
  Search/Apply/Merge timers begin.

Therefore the current two-part model is incomplete:

1. encoded UF and rebuild maintenance;
2. generating and re-typechecking an encoded program;

There is a third material cost:

3. changed physical rule shape, including per-invocation rule assembly,
   query planning, and user-rule search.

There is also smaller workload-dependent top-level command work.

## Question and hypotheses

Question: for each of the six representative workloads, which mechanisms
explain the wall-time increase from `off` to `term` on the same binary?

The diagnostic distinguished these competing hypotheses:

- H1: explicit encoded UF/rebuild maintenance dominates.
- H2: the second frontend and generated-program installation dominate.
- H3: source rules become physically different queries and spend more time in
  rule assembly/planning/search even when generated maintenance is cheap.
- H4: top-level actions, input loading, checks, extraction, or scheduler-driver
  work dominate outside the rulesets.

The results support different hypotheses on different workloads.

## Measurement

The decisive report is:

```text
/tmp/term-overhead-main-5ead0a0-instrumented-assembly-v1.jsonl
```

The instrumented binary SHA-256 is:

```text
3c140fc59901ec0d448778dc511f23ed12498434344ebd74010fe4db75dcd48e
```

Command shape:

```text
./bench.py \
  --target . --treatment term \
  --compare-target . --compare-treatment off \
  --rounds 6 --timeout-sec 120 --force-run \
  --report /tmp/term-overhead-main-5ead0a0-instrumented-assembly-v1.jsonl
```

Both endpoints use the same release binary, workload bytes, fact-directory
bytes, and one execution thread. Runs alternate `off` and `term` for each file.
All 72 runs succeeded.

The instrumentation measured disjoint intervals for:

- initialization and source-file reading;
- source parsing, macros, typechecking, and other source resolution;
- encoding generation, including parsing emitted encoding text;
- generated desugaring and generated typechecking;
- installing functions and compiled rules;
- top-level actions, input, scheduler-driver work, and other commands;
- per-ruleset assembly, Search, Apply, unattributed execution, Merge, and
  Rebuild.

The report's additive residual is wall time minus all those intervals. It is
only 0.5% to 6.2% of each measured slowdown, which is a useful check that the
phase boundaries explain nearly all of the difference.

An earlier stock-main report, without the temporary extra timers, is retained
at:

```text
/tmp/term-overhead-main-5ead0a0-v1.jsonl
```

Its ratios agree with the diagnostic run. A separate ten-round diagnostic run
at `/tmp/term-overhead-main-5ead0a0-instrumented-v1.jsonl` contains substantial
machine-contention outliers and is retained rather than filtered. During the
campaign an unrelated long-running process was executing
`/tmp/churchroad-wide-multiply.egg`. The decisive six-round paired run was
stable despite that background process; its tight paired confidence intervals
support the relative decomposition, while its absolute milliseconds remain
machine-specific.

## Additive slowdown decomposition

All numbers are paired mean `term - off` wall milliseconds over six rounds.
Percentages are shares of that file's wall-time increase.

| Workload | Off | Term | Slowdown | Frontend | Transformed user rules | UF/rebuild substitution | Command work | Residual |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Math | 376.6 | 839.8 | 463.2 | 3.4 (0.7%) | 166.8 (36.0%) | 289.2 (62.4%) | 1.1 (0.2%) | 2.7 (0.6%) |
| eggcc | 839.5 | 1235.2 | 395.7 | 142.3 (36.0%) | 118.8 (30.0%) | 87.4 (22.1%) | 37.6 (9.5%) | 9.7 (2.4%) |
| Pointer | 8.0 | 15.5 | 7.6 | 6.4 (83.9%) | 0.2 (2.2%) | 0.6 (7.3%) | 0.0 (0.5%) | 0.5 (6.2%) |
| Hardboiled | 115.6 | 222.1 | 106.5 | 49.4 (46.4%) | 35.2 (33.1%) | 11.5 (10.8%) | 6.9 (6.5%) | 3.4 (3.2%) |
| Luminal | 372.5 | 1291.0 | 918.5 | 357.8 (39.0%) | 418.1 (45.5%) | 50.5 (5.5%) | 68.2 (7.4%) | 24.0 (2.6%) |
| Herbie | 54.3 | 109.5 | 55.2 | 17.5 (31.8%) | 14.7 (26.7%) | 12.0 (21.7%) | 9.4 (17.1%) | 1.5 (2.7%) |

The paired 95% confidence intervals for the total slowdowns are:

| Workload | Paired slowdown 95% CI |
| --- | ---: |
| Math | 451.4–475.1 ms |
| eggcc | 384.8–406.7 ms |
| Pointer | 7.2–7.9 ms |
| Hardboiled | 103.4–109.6 ms |
| Luminal | 889.1–947.9 ms |
| Herbie | 53.7–56.7 ms |

### Category definitions

The table is exactly additive.

- Frontend includes initialization, source-file reading, source parsing,
  macros, source typechecking, other source resolution, encoding generation,
  generated desugaring, generated typechecking, and installing functions and
  rules.
- Transformed user rules includes Assembly, Search, Apply, Execution overhead,
  and Merge for rulesets whose names do not begin with `@`. Rebuild is excluded
  from this column.
- UF/rebuild substitution includes every phase of generated `@...` maintenance
  rules plus the `term - off` difference in non-`@` Rebuild. This subtracts the
  native rebuilding that term mode replaces, rather than presenting generated
  maintenance as if native rebuilding were free.
- Command work includes top-level actions, input, schedule interpretation after
  subtracting all recorded ruleset phases, and checks/extraction/other commands.
- Residual is process wall time not claimed by any measured phase.

## What the rule timers say

### Math: encoded maintenance really is the main problem

Term mode spends 443.0 ms in generated `@...` maintenance:

- 300.7 ms Search;
- 63.3 ms Apply;
- 78.5 ms Merge;
- less than 0.5 ms assembly and unattributed work.

Off mode spends 153.7 ms in native Rebuild. Replacing that native work therefore
costs a net 289.2 ms. The transformed default ruleset adds another 88.0 ms Apply
and 76.8 ms Merge. Generated typechecking is only 1.7 ms.

This is the workload where optimizing or native-backing the encoded UF/rebuild
machinery is directly decisive.

### eggcc: rule assembly was hiding outside the report

Term mode's generated maintenance costs 339.8 ms, but 253.0 ms of that is
ruleset assembly before Search starts:

- `@rebuilding` assembly: 206.8 ms;
- `@parent` assembly: 43.4 ms;
- other generated maintenance assembly: about 2.7 ms.

Off mode spends 252.5 ms in native Rebuild, leaving a net UF/rebuild
substitution cost of 87.4 ms.

The frontend adds 142.3 ms:

- encoding generation: 37.0 ms;
- generated desugaring: 13.1 ms;
- generated typechecking: 71.0 ms;
- installation: 23.6 ms;
- small offsets in the unchanged source frontend: about -2.4 ms.

Transformed user rules add 118.8 ms, including 57.6 ms Search, 26.6 ms Apply,
21.1 ms Merge, and 13.0 ms assembly. Schedule-driver work adds another 36.6 ms.

So neither "UF" nor "re-typechecking" alone explains eggcc. Avoiding repeated
assembly of the large generated maintenance rulesets is also a first-class
opportunity.

### Pointer: almost entirely the second frontend

The total slowdown is only 7.6 ms, but 6.4 ms is frontend work:

- encoding generation: 2.3 ms;
- generated desugaring: 0.5 ms;
- generated typechecking: 2.3 ms;
- installation: 1.2 ms.

User-rule execution adds about 0.2 ms and the net maintenance substitution adds
about 0.6 ms. This benchmark primarily measures fixed per-program encoding
cost, not UF execution.

### Hardboiled: frontend first, changed user search second

The frontend contributes 49.4 ms, led by 25.8 ms generated typechecking and
12.1 ms encoding generation. Transformed user rules add 35.2 ms, including
24.6 ms Search. Net encoded maintenance is 11.5 ms.

### Luminal: not a UF bottleneck

The 918.5 ms slowdown divides primarily into:

- 357.8 ms frontend;
- 418.1 ms transformed user rules;
- 68.2 ms command work;
- only 50.5 ms net UF/rebuild substitution.

The frontend includes 192.0 ms generated typechecking, 88.2 ms encoding,
43.7 ms installation, and 25.4 ms generated desugaring. Top-level encoded
actions add 65.0 ms.

Within transformed user rules, Search adds 322.3 ms and assembly adds 90.9 ms.
This agrees with the corrected ruleset report: `fusion_grow` and `fusion_pair`
search much slower under the wider encoded relation/query shapes. Improving
`@UF` alone cannot materially close Luminal's gap.

### Herbie: no single dominant bucket

Frontend contributes 17.5 ms, transformed user rules 14.7 ms, net maintenance
12.0 ms, and command work 9.4 ms. The command bucket includes about 7.7 ms in
checks/extraction/other commands across the fixture's repeated push/pop scopes.

## Is rule-execution difference enough to measure encoding overhead?

It is necessary, but not sufficient.

After PR #61, the existing report can correctly expose:

- generated maintenance rulesets such as `@rebuilding` and `@parent`;
- Search, Apply, Execution overhead, Merge, and Rebuild;
- changes in source-named rulesets after encoding.

That is enough to identify Math's main bottleneck and Luminal's changed Search
shape. It is not enough for Pointer, eggcc, Hardboiled, or Herbie because it
still leaves these costs in one residual:

- source versus generated typechecking;
- encoding generation and parsing of emitted text;
- generated desugaring;
- function/rule installation;
- ruleset assembly and per-invocation plan construction;
- top-level actions and command work.

In particular, looking only at the five currently reported ruleset phases would
misclassify eggcc's approximately 253 ms generated-maintenance assembly cost as
frontend or generic outside overhead.

## Minimal permanent reporting change

A narrow reporting PR should add measurement before optimization PRs.

1. Add `Assembly` before `Search` to each per-ruleset timing record. It should
   include first-use cached-plan construction and rebuilding the executable
   ruleset for each invocation.
2. Add disjoint outside-ruleset leaves under two explicit parents:
   - Lowering / Parse, total Typecheck, and Other;
   - Commands / Install, Actions/input, and Other/schedules;
   - residual derived per observation from process wall time.
3. Charge source typechecking performed in the separate original-typechecker
   e-graph to the outer total Typecheck leaf. Keeping one shared Typecheck leaf
   makes the off-versus-encoded delta directly show the checking added by the
   encoding, without storing mode-specific fields.
4. Render an additive per-file slowdown table like the one above, in addition
   to detailed ruleset rows. Do not infer "frontend" from the wall-time
   residual after collection.
5. Preserve same-binary comparisons and one-thread execution for additive
   Search/Apply timing.

The diagnostic patch used here added 196 lines across five Rust files. That is
too broad and ad hoc to retain as production code, but it validates the phase
boundaries for a smaller, reviewed implementation. A four-round clean-versus-
instrumented timer-tax comparison is retained at
`/tmp/term-overhead-timer-tax-off-v1.jsonl`; machine contention made its wall
CI inconclusive, while RSS was indistinguishable on nearly all workloads. A
production PR should include a cleaner timer-tax check.

## Consequences for the unification roadmap

The measurements argue against a single "replace encoded UF" campaign.

- Preserve the one-relational-UF destination, but treat it as the Math-focused
  and maintenance-focused track.
- Typed emission that removes generated parsing/desugaring/typechecking is the
  direct track for Pointer and a large part of eggcc, Hardboiled, Luminal, and
  Herbie.
- Identity/view fusion that restores narrow source query shapes is at least as
  important as UF fusion for Luminal.
- Cache or eliminate repeated assembly of generated maintenance rulesets;
  otherwise eggcc can spend more time preparing `@rebuilding` than executing
  its Search/Apply/Merge phases.
- Keep top-level encoded action lowering visible. It is about 65 ms of
  Luminal's slowdown even after the frontend is separated.

The performance target should be evaluated per workload as well as in suite
aggregate. A change that fixes Math's `@rebuilding` cost can leave Pointer and
Luminal almost untouched, while a typed-frontend change can make Pointer much
faster and barely move Math.

## P0b implementation evidence ledger

Status: complete on `codex/term-encoding-always-on` from
`5ead0a0cacf847a129294a870de13503f2d7f9c4`.

Smallest falsifiable contract: a synthetic V3 observation assigns distinct
nanosecond values to every exclusive leaf under Lowering, Commands, and
Ruleset. The report must display every leaf once, and the leaves plus the
derived residual must reconstruct external wall time. A real CLI fixture must
also show nonzero source Parse, Typecheck, Commands / Install, Commands /
Actions, and Ruleset / Assembly values.

Current hypothesis: most of the previously unexplained proof/term-encoding
slowdown can be localized without splitting source and generated passes. Total
Typecheck is enough to answer how much extra typechecking the encoded mode
adds, provided typechecking done by the cloned source checker is charged to the
outer e-graph. Ruleset / Assembly must include first-use cached-plan creation
and per-invocation executable-ruleset materialization, while core execution
setup belongs to Ruleset / Execution overhead.

Falsifiers:

- nested command or schedule time appears both in Commands and Ruleset;
- source typechecking in encoded modes falls into Lowering / Other;
- generated parsing is omitted from Lowering / Parse;
- internal rebuild-rule assembly is recorded again outside Ruleset / Rebuild;
- the synthetic leaves plus residual do not equal wall time;
- timer instrumentation causes a material wall-time regression in an
  instrumented-versus-clean same-treatment comparison.

Evidence to retain: focused Rust producer/CLI tests, focused Python
schema-analysis-rendering tests, `make check`, `make benchmark-smoke`, the Rich
and Markdown width matrix, one real off-versus-proofs phase report, and a
timer-tax comparison. Failed hypotheses and inconclusive timing intervals stay
recorded rather than being discarded.

Implementation result:

- The producer and consumer contract is now V3. The initial tests failed on the
  missing nested process schema, Assembly field, and analysis types, then pass
  with all thirteen leaves reconstructing synthetic wall time exactly.
- `/tmp/term-overhead-off-proofs-v3.jsonl` contains four fresh rounds for all
  six default workloads. The suite proof/off wall ratio is 3.04–3.16x. Its
  phase tables leave small residual shares on the substantive workloads and
  make the previously hidden Typecheck, Install, Actions/input, and Assembly
  changes explicit.
- `/tmp/term-overhead-timer-tax-v3.jsonl` compares ten rounds of the
  instrumented off mode with a temporary V3-compatible `5ead0a0` control. The
  suite means are 1.7591 s versus 1.7408 s, a 1.0105x point ratio; the displayed
  95% interval rounds to 1.00–1.02x. This rejects a 5–10% suite-level timer tax,
  though it does detect a small roughly 1% effect.
- `/tmp/term-overhead-timer-tax-proofs-v3.jsonl` repeats the control comparison
  for proofs over four rounds; the suite interval is 0.873–1.07x and therefore
  inconclusive, with every per-file wall interval including 1.
- Focused and six-file Rich reports render successfully at widths 80, 119, 120,
  160, and 200. Widths 80 and 119 emit exactly one detailed-report warning;
  wider reports emit none. Markdown output is byte-identical across all five
  widths for each scope.
- `make check` and `make benchmark-smoke` both pass in the implementation
  worktree.

## Flat mechanism-ledger follow-up

Status: supersedes the fixed nested V3 transport above while retaining its
timer sites and the ruleset Assembly measurement.

The persisted timing summary is now one sorted list of exclusive leaves:

```json
{"schema_version":3,"timings":[{"path":["program","search","fusion_grow"],"ns":123}]}
```

The first path segment is the additive responsibility shown in the report;
deeper segments retain diagnostic resolution. The stable responsibilities are
Typecheck, Frontend, Program, Equality, and Commands. Residual remains derived
as process wall time minus the sum of every leaf. No parent total is stored.
Ruleset names are separate path segments, so names containing `/` cannot be
misparsed.

Rulesets receive an explicit timing role when declared. Program rules write
Assembly, Search, Apply, Execution, and Merge under `program`; their native
Rebuild tail writes under `equality/rebuild`. Encoded maintenance rules write
all phases under `equality`. Thus the net cost of replacing native rebuilding
with relational maintenance is an ordinary candidate-minus-baseline Equality
difference, not a reporting-time credit calculation or an `@`-prefix guess.

Checks have their own `commands/check` leaf. The transient backend query and
the surrounding compilation/validation overhead are charged there in both off
and encoded modes. The motivating claim that term-mode checks themselves were
showing up as the default ruleset was falsified by check-only CLI probes: the
old report recorded no transient check ruleset in either mode. Hardboiled has a
real default `(run)`. Keeping the explicit check leaf still removes the
ambiguity and prevents future routing asymmetry.

One boundary remains intentionally command-scoped: a top-level action such as
`(union ...)` can trigger `flush_updates` and native rebuilding, but its
transient backend report is not a named ruleset run. That entire interval is
therefore recorded under `commands/actions`, not `equality/rebuild`.

The fresh six-round report confirms the separation on real fixtures.
Hardboiled records `commands/check` means of 1.697 ms off and 3.299 ms term,
while its independent default-ruleset Search means are 60.349 ms and 84.870
ms. Herbie records 0.175 ms and 0.241 ms for checks. Check evaluation is
therefore visible without being mistaken for transformed program-rule Search.

At `--detail phases`, presentation starts with one additive
slowdown-decomposition table with a Suite row and one row per file. At
`--detail rulesets`, one driver panel per file unfolds exactly the Program and
Equality cells from that table. Program children contain source rules' own five
execution phases; Equality children contain every encoded-maintenance ruleset
and one global native-Rebuild replacement row when its delta is nonzero. The
two parent phase summaries retain the unique diagnostic question from the
removed global rollup: whether Program or Equality cost is Assembly, Search,
Rebuild, or another execution phase. Up to five source children plus an exact
per-group Other are shown, while the small fixed set of nonzero maintenance
children is shown in full. Native Rebuild is never attributed to whichever
source ruleset happened to trigger it.

### Readability rationale

The headline table follows a task-first rather than decorative color design.
A [controlled IEEE VIS table-reading
study](https://ieeexplore.ieeevis.org/year/2024/program/paper_v-full-1288.html)
found that visual aids are task dependent: color and bar encodings help some
extrema tasks, while row striping performs better for some complex comparison
tasks. [W3C table guidance](https://www.w3.org/WAI/tutorials/tables/tips/)
likewise recommends row orientation aids with sufficient contrast, and
[WCAG's use-of-color guidance](https://www.w3.org/WAI/WCAG20/Understanding/use-of-color)
requires that color not be the only signal.

Accordingly, percent share comes first for vertical comparison, every report
table uses the same compact header-rule style, and `◆` identifies the largest
absolute mechanism share. Rich and interactive reports also bold that dominant
cell and dim contributions below 5%. Expected added overhead is neutral; green
is reserved for improvements, while yellow and red are reserved for measurement
warnings and errors. Signed values and the `◆` marker keep the meaning
independent of color. The contributor panels stay textual rather than adding in-cell bars:
the primary task is finding a dominant role, ruleset, and phase, and bars would
add another renderer-specific encoding to an already dense diagnostic.

### Complexity audit and minimization

The retained complexity falls into six distinct responsibilities. Keeping
them separate makes it possible to decide which parts are measurement
requirements and which are only report presentation.

| Layer | Added responsibility | Why it remains | Simplification retained |
| --- | --- | --- | --- |
| Engine phase boundaries | Measure seven process leaves and six exclusive ruleset phases, including Assembly | Without these boundaries, Pointer frontend time and eggcc plan construction return to an undifferentiated residual | Static path slices and one duration map; no mode-specific timer structs |
| Semantic routing | Route source rules, relational equality maintenance, native Rebuild, and transient checks consistently | Equality is a responsibility implemented differently by the two treatments, so name-prefix inference or a report-time credit gives the wrong abstraction | One two-variant role enum; checks use one symmetric `commands/check` path |
| Scope-safe accounting | Preserve roles and accumulated time across push/pop, and subtract nested process/ruleset intervals from command timers | Otherwise nested schedules, checks, and rulesets are double-counted | One exclusive-subtraction boundary around commands and lowering; Residual verifies closure |
| Wire format | Persist exact measurements without fixing the set of diagnostic counters | A five-field record could answer today's headline but would lose the Assembly/Search evidence that chose different optimization PRs | One sorted open list of segmented `path -> ns` leaves; no parent totals and no separate per-ruleset record |
| Analysis | Align independent endpoint samples, derive Residual, and unfold Program and Equality into named children | Source own work, encoded maintenance, and native Rebuild must remain separate to keep every sign truthful | One generic exact-path sample map; the two parent groups equal the decomposition directly |
| Presentation and validation | Render one scan-first mechanism table and one compact driver panel per file; test additive closure at both hierarchy levels | Only the five buckets hides which ruleset carries Assembly/Search, while role totals falsely attach global Rebuild to source rules | Two mechanism parents, source top five plus exact Other, all maintenance children, and one native-Rebuild child |

The minimization pass removed or avoided the main sources of accidental
complexity:

- fixed nested timing structs and a second per-ruleset wire schema were
  replaced by the one open path ledger;
- the native-Rebuild "credit" disappeared because both equality
  implementations are recorded under `equality` before analysis;
- `@`-prefix classification disappeared in favor of declaration-time roles;
- mechanism and ruleset-driver reports now share one aligned sample map;
- the global depth-two rollup and ten-column ruleset tables became one compact
  four-column panel per file whose two parent rows directly match Program and
  Equality, with truthful per-group children and an exact source remainder;
- report invariants use ordinary exceptions, so `python -O` cannot remove
  cache-safety checks;
- the visual treatment uses existing table primitives rather than adding bar
  geometry or renderer-specific calculations.

Two tempting reductions would make the design simpler only on paper.
Collapsing persistence to the five headline buckets would make the measured
eggcc Assembly and Luminal Search costs inseparable. Inferring maintenance
from generated names would remove the role enum but make semantics depend on a
printer convention. Neither is retained.

The one plausible future reduction is to carry the semantic role inside the
engine's aggregated `RunReport`. That could remove the second role map used to
survive push/pop, but it would also make a benchmark-accounting concept part of
the public cross-crate report type. It is deferred until the role is useful to
the engine itself. Likewise, the extra timers can be gated if this moves
upstream and the measured tax becomes unacceptable; the current control run
does not justify that branch.

As a review-surface count against `5ead0a0`, the current implementation is net
`+329` Rust source lines including the new 74-line timer module and inline
tests, net `+175` Python report lines, net `+345` external test/snapshot lines,
and net `+53` README lines. These are diff counts rather than runtime
complexity: the Rust report transport itself shrank while replacing V2, and
the snapshots contain no executable logic. The largest irreducible pieces are
the exclusive timing boundaries and their tests; the open-map transport and
mechanism/name projection are the parts deliberately kept small.

The final driver redesign reduced production Python report complexity
from the pre-amendment net `+218` lines to `+175`: it deleted
`PhaseRollupView`, `_phase_rollups`, the global rollup renderer, endpoint-total
ruleset confidence intervals, the ten-column ruleset table, and the per-table
row-guide styling switch. External
validation grew because it now locks down direct mechanism-parent equality,
per-parent child additivity, deterministic phase threshold, and all report
renderers and supported widths. That growth is test-only; no second runtime
analysis or presentation path remains.

### Fresh off-versus-term evidence

The six-round report is:

```text
/tmp/term-overhead-mechanisms-v3-20260812.jsonl
```

All 72 runs succeeded. The displayed suite wall ratio is `2.04–2.09x`.
The report treats endpoint samples as independent because the JSONL has no
persistent round-pair identity. Its additive suite slowdown is:

| Mechanism | Delta | Share of slowdown |
| --- | ---: | ---: |
| Typecheck | +290 ms | 15.7% |
| Frontend/install | +270 ms | 14.6% |
| Program rules | +723 ms | 39.1% |
| Equality/rebuild | +416 ms | 22.5% |
| Commands | +116 ms | 6.28% |
| Residual | +34.0 ms | 1.84% |

The file rows preserve the earlier diagnosis: Math is 62.5% Equality;
Pointer is 79.1% Typecheck plus Frontend; Luminal is 46.3% Program and only
4.89% Equality; eggcc and Herbie remain mixed. The small residual is the
accounting self-check that the table explains nearly all of the observed
slowdown.

### Instrumentation-tax control

The clean-control report is:

```text
/tmp/term-overhead-timer-tax-leaves-v3-20260812.jsonl
```

It compares ten off-mode rounds of this instrumented build against a temporary
clean `5ead0a0` build. The clean build received only a compatibility adapter
that emits the same flat V3 leaf count and serialization shape with the new
process and Assembly values fixed at zero; it does not execute their timers.
This holds timing-summary serialization approximately constant while isolating
the additional timer sites.

The clean suite mean was `1.723830 s`; the instrumented suite mean was
`1.727558 s`, for an instrumented/clean point ratio of `1.00216x`. The report's
95% interval is `0.995–1.01x` and includes 1. This run therefore detects no
suite-level timer slowdown and rules out a 5–10% tax under the measured
off-mode workload mix.
