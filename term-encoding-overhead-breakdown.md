# Where Current Term-Encoding Time Goes

## Result

Term encoding is `1.61–1.63x` slower across the current ten-workload suite, but
there is no single dominant cause. The suite mean adds 1.889 seconds over a
3.035-second `off` baseline:

| Mechanism | Mean delta | Share of slowdown |
| --- | ---: | ---: |
| Source-rule execution | +563 ms | 29.8% |
| Equality/rebuild, net | +455 ms | 24.1% |
| Typechecking | +345 ms | 18.2% |
| Other frontend/install | +344 ms | 18.2% |
| Commands | +136 ms | 7.22% |
| Residual | +46.4 ms | 2.46% |

The full generated report is checked in as
[`term-encoding-overhead-benchmark.md`](term-encoding-overhead-benchmark.md).

The important engineering conclusion is that a native or inline rebuild alone
cannot reach the 5–10% target. Making the entire Equality/rebuild bucket as
cheap as the baseline would reduce the suite point ratio only from `1.62x` to
`1.47x`. Removing all measured non-program overhead would still leave `1.20x`
because transformed source rules remain materially different. Reaching `1.10x`
would require removing about 84% of the current added time, including roughly
306 ms, or 54%, of the net Program bucket even after every positive non-program
delta disappeared.

## Measurement

The branch first merged `origin/main` at
`46f69b70d0819b03da110e6e785f91c080d58556`. The measured executable state is
commit `d60202f64424`; the later report-only commit does not change that binary.

```bash
./bench.py \
  --detail rulesets \
  --treatment term \
  --force-run \
  --report /tmp/term-encoding-d60202f.jsonl \
  --format markdown
```

This collected six fresh `off` and six fresh `term` observations for each of
the ten default workloads: 120/120 runs succeeded. Both endpoints used the
same release binary, workload bytes, fact-directory bytes, timeout, and one
execution thread. Endpoint samples are treated as independent because the
JSONL intentionally stores no round-pair identity.

The actual wall-time ratios were:

| Workload | `term / off` (95% CI) |
| --- | ---: |
| Math | 2.01–2.11x |
| eggcc | 1.43–1.48x |
| Pointer analysis | 2.27–2.37x |
| Hardboiled | 1.88–1.94x |
| Luminal | 3.38–3.46x |
| Herbie | 1.96–2.02x |
| Misaal HVX | 2.95–3.07x |
| Churchroad wide multiply | 0.705–0.715x |
| DialEgg NMM40 | 1.64–1.66x |
| SPEQ preserved-reference suite | 3.56–3.61x |

Churchroad is a useful warning against treating every encoding-induced change
as overhead: its `mapping` Search becomes 309 ms faster, more than offsetting
the added frontend and maintenance work.

### Timer-tax control

The extra timers were also measured against a V3-compatible clean control on
the same `5ead0a0` source state. That ten-round, six-workload comparison held
the summary serialization shape fixed while replacing the added timer sites
with zero-valued leaves. The clean suite mean was `1.723830 s`; the instrumented
mean was `1.727558 s`, a `1.00216x` point ratio with a `0.995–1.010x` 95%
interval. This detects no suite-level slowdown and rules out a 5–10% timer tax
for the measured off-mode workload mix. The primary term-versus-off result is
also same-binary, so both of its endpoints pay the retained instrumentation.

## What “inline rebuilding” can mean

The report separates two distinct counterfactuals:

1. **Remove Equality ruleset assembly.** This removes 299 ms of lazy plan
   creation and per-invocation executable-ruleset construction, producing an
   implied `1.52x` suite ratio.
2. **Make net Equality/rebuild baseline-equivalent.** This removes the entire
   455 ms net responsibility, producing an implied `1.47x` ratio.

The second number is the optimistic answer to “what if the relational UF and
rebuild were as cheap as native rebuilding?” It is not the cost of one named
ruleset. Encoded maintenance is collective: `@rebuilding`, `@parent`, cleanup,
and subsumption together replace the native rebuild loop.

Across the suite, generated Equality maintenance adds 863 ms before crediting
the 407 ms of native Rebuild it replaces:

| Equality phase | Mean delta |
| --- | ---: |
| Assembly | +299 ms |
| Search | +375 ms |
| Apply | +77.8 ms |
| Execution | +13.2 ms |
| Merge | +96.9 ms |
| Native Rebuild replaced | −407 ms |
| **Net Equality/rebuild** | **+455 ms** |

So a plan-cache or inline-assembly change attacks a real cost, especially on
eggcc, but it leaves most Equality Search/Apply/Merge work intact. Conversely,
folding the native-rebuild credit into `@rebuilding` would falsely make that
single generated ruleset look cheap and obscure the collective substitution.

## Optimization ceilings

The report now performs the arithmetic directly. Each row removes only the
named positive candidate-minus-baseline deltas, preserves candidate-side
speedups, and holds every other mean fixed.

| Hypothetical change | Time removed | Implied ratio |
| --- | ---: | ---: |
| Remove added typechecking | 345 ms | 1.51x |
| Remove added frontend/install | 344 ms | 1.51x |
| Remove both frontend groups | 689 ms | 1.40x |
| Remove Equality assembly | 299 ms | 1.52x |
| Remove net Equality/rebuild | 455 ms | 1.47x |
| Remove source-rule execution delta | 563 ms | 1.44x |
| Remove every positive non-program delta | 1.28 s | 1.20x |
| Remove every recorded positive mechanism delta | 1.84 s | 1.02x |

These are additive accounting ceilings, not implementation predictions. They
have no confidence intervals and do not model interactions: removing generated
types or identities may also change Program Search, Apply, Merge, or plan
assembly. The `1.02x` final row is primarily an accounting-closure check; it
leaves the 46 ms residual rather than pretending uninstrumented time is freely
removable.

## Workload narratives

- **Math:** Equality/rebuild is 60.6% of the slowdown. Generated maintenance
  costs 395 ms and replaces 135 ms of native rebuild. This is the clearest
  relational-UF target, though changed default-rule Apply and Merge still add
  152 ms.
- **eggcc:** no single mechanism wins. Typecheck plus frontend adds 136 ms,
  source rules add 108 ms, net Equality adds 83 ms, and commands add 35 ms.
  Equality is assembly-heavy: 245 ms of added assembly is almost exactly
  offset by 245 ms of removed native rebuild before Search and execution are
  counted. `always-run` carries 82 ms of the Program delta.
- **Pointer analysis:** net Equality is largest at 29 ms, frontend is 21 ms,
  and Program is 11 ms. Its 9.5 ms residual is large enough that tiny
  sub-mechanism conclusions should remain cautious.
- **Hardboiled:** source rules add 33 ms, while typecheck plus frontend adds
  49 ms. The default ruleset's Search dominates its Program child; check
  evaluation is routed symmetrically under Commands rather than appearing as a
  term-only default ruleset artifact.
- **Luminal:** Program is 403 ms, 46.5% of the slowdown; Equality is only
  39.8 ms, 4.59%. `fusion_grow` and `fusion_pair` add 169 and 147 ms, almost
  entirely Search. Typecheck plus frontend adds another 344 ms. UF work is not
  the limiting explanation here.
- **Herbie:** mixed across Program (26.6%), Equality (22.4%), frontend/typecheck
  (33.1%), and Commands (14.8%).
- **Misaal HVX:** typecheck plus frontend explains 90.6% of the slowdown.
  Program and Equality together explain less than 4%; a UF optimization would
  barely move it.
- **Churchroad:** Program Search improves by 308 ms net, making term encoding
  faster overall despite every other top-level mechanism becoming slower.
- **DialEgg:** Program contributes 57.9%, led by Apply and Merge; net Equality
  contributes 16.3%.
- **SPEQ:** Program contributes 74.5%, mostly assembly in four transform
  rulesets; Equality is below 1%.

## What this answers—and what it does not

The additive report now answers:

- how much slowdown is frontend, source-rule execution, relational
  equality/rebuild, commands, or residual;
- whether Equality cost is assembly or execution;
- which source or maintenance rulesets carry Program and Equality changes; and
- optimistic remaining ratios when selected positive deltas disappear.

It does not identify why a source rule searches or assembles more slowly. For
Luminal, the data localizes the problem to `fusion_grow`/`fusion_pair` Search,
but distinguishing wider tuples, extra identity columns, changed join order,
or greater state churn requires a profiler or a targeted lowering ablation.
Likewise, the counterfactual rows cannot predict cross-mechanism effects.

## Measurement design

Every successful process emits one sorted, open list of exclusive
`path -> nanoseconds` leaves:

- `typecheck/total`;
- `frontend/{parse,other,install}`;
- `program/<phase>/<source ruleset>`;
- `equality/<phase>/<maintenance ruleset>`;
- `equality/rebuild/<source ruleset>` for native rebuild tails; and
- `commands/{actions,check,other}`.

Rulesets receive an explicit Program or Equality-maintenance role at
declaration time; the report never infers semantics from an `@` prefix. Native
Rebuild and encoded maintenance therefore land under one responsibility before
subtraction. Checks use one command path in both modes. Residual is derived as
wall time minus every recorded leaf and remains the additive self-check.

The ruleset panel is a literal expansion of the decomposition's two
ruleset-borne columns:

- `Program rules — own work` excludes source rules' native Rebuild tails;
- `Equality/rebuild — net` contains all maintenance rules and one global
  `Native rebuild replaced` child;
- source children are top five by absolute own-work delta plus an exact
  `Other`; and
- every nonzero maintenance child is shown.

Parent rows exactly equal the Program and Equality cells, and children exactly
sum to their parent. No report-time name heuristic or cross-endpoint rebuild
credit is needed.

## Complexity and minimization

The retained complexity has five responsibilities:

| Layer | Required work | Deliberate simplification |
| --- | --- | --- |
| Engine timing | Exclusive process and six-phase ruleset boundaries | Static path slices and one duration map |
| Semantic routing | Program, maintenance, native rebuild, and check ownership | One two-variant role instead of name-prefix inference |
| Transport | Persist exact leaves for later projections | One open segmented-path list; no fixed phase structs or second ruleset schema |
| Analysis | Align endpoint samples, derive residual, mechanisms, drivers, and ceilings | One generic path-sample ledger; parent/child sums are direct |
| Presentation | Decomposition, suite ceilings, and per-file drivers | One shared catalog and table renderer for Rich, Markdown, and interactive output |

The final reduction pass kept the old execution path recognizable and removed
presentation-only alternatives: there is no global phase-rollup model, no
ten-column ruleset table, no duplicated fixed five-bucket wire record, and no
special report-time native-rebuild credit. The optimization table is derived
from the same means and leaf ledger rather than introducing another recording
shape. Further reduction would either lose the Assembly/Search distinction
that separates plan-cache work from query-shape work or make the signs in the
ruleset panel misleading again.

## Engineering direction

The measurements support parallel, falsifiable tracks rather than one “UF
fix”:

1. eliminate generated parsing, re-typechecking, and installation;
2. cache or fuse Equality assembly, then measure whether Equality execution
   can approach native rebuild;
3. restore source-rule physical shapes, especially Luminal Search and SPEQ
   assembly; and
4. retain the open ledger while each optimization lands so cross-mechanism
   movement remains visible.

A 5–10% always-on target is possible only if these improvements compose. The
current data rejects both “frontend alone” and “relational UF alone” as
sufficient strategies.
