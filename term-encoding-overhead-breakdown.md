# Where Current Term-Encoding Time Goes

## Result

Term encoding is `1.62–1.64x` slower across the current ten-workload suite, but
there is no single dominant cause. The suite mean adds 1.935 seconds over a
3.083-second `off` baseline:

| Mechanism | Mean delta | Share of slowdown |
| --- | ---: | ---: |
| Source-rule execution | +575 ms | 29.7% |
| Equality/rebuild, net | +476 ms | 24.6% |
| Typechecking | +350 ms | 18.1% |
| Other frontend/install | +346 ms | 17.9% |
| Commands | +138 ms | 7.12% |
| Residual | +50.3 ms | 2.60% |

The full generated report is checked in as
[`term-encoding-overhead-benchmark.md`](term-encoding-overhead-benchmark.md).

The important engineering conclusion is that a native or inline rebuild alone
cannot reach the 5–10% target. Making the entire Equality/rebuild bucket as
cheap as the baseline would reduce the suite point ratio only from `1.63x` to
`1.47x`. Removing all measured non-program overhead would still leave `1.20x`
because transformed source rules remain materially different. Reaching `1.10x`
would require removing about 84% of the current added time, including roughly
317 ms, or 55%, of the net Program bucket even after every positive non-program
delta disappeared.

## Measurement

The branch first merged `origin/main` at
`46f69b70d0819b03da110e6e785f91c080d58556`. The measured executable state is
commit `d60202f64424`; the later report-only commit does not change that binary.

```bash
./bench.py \
  --target @d60202f \
  --compare-target @d60202f \
  --detail rulesets \
  --treatment term \
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
| Math | 1.98–2.08x |
| eggcc | 1.45–1.48x |
| Pointer analysis | 2.27–2.35x |
| Hardboiled | 1.91–1.95x |
| Luminal | 3.39–3.43x |
| Herbie | 1.95–2.03x |
| Misaal HVX | 2.97–3.05x |
| Churchroad wide multiply | 0.708–0.720x |
| DialEgg NMM40 | 1.61–1.69x |
| SPEQ preserved-reference suite | 3.55–3.65x |

Churchroad is a useful warning against treating every encoding-induced change
as overhead: its `mapping` Search becomes 305 ms faster, more than offsetting
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

The measured leaves support two distinct interpretations of “inline”:

1. **Remove Equality ruleset assembly.** This removes 307 ms of lazy plan
   creation and per-invocation executable-ruleset construction, producing an
   implied `1.53x` suite ratio.
2. **Make net Equality/rebuild baseline-equivalent.** This removes the entire
   476 ms net responsibility, producing an implied `1.47x` ratio.

The second number is the optimistic answer to “what if the relational UF and
rebuild were as cheap as native rebuilding?” It is not the cost of one named
ruleset. Encoded maintenance is collective: `@rebuilding`, `@parent`, cleanup,
and subsumption together replace the native rebuild loop.

Across the suite, generated Equality maintenance adds 894 ms before crediting
the 417 ms of native Rebuild it replaces:

| Equality phase | Mean delta |
| --- | ---: |
| Assembly | +307 ms |
| Search | +391 ms |
| Apply | +80.5 ms |
| Execution | +14.0 ms |
| Merge | +101 ms |
| Native Rebuild replaced | −417 ms |
| **Net Equality/rebuild** | **+476 ms** |

So a plan-cache or inline-assembly change attacks a real cost, especially on
eggcc, but it leaves most Equality Search/Apply/Merge work intact. Conversely,
folding the native-rebuild credit into `@rebuilding` would falsely make that
single generated ruleset look cheap and obscure the collective substitution.

## Derived bounds for the engineering question

The suite row is a sum of per-file mean deltas, not one process observation.
Its additive cells support simple what-if arithmetic, but that arithmetic is
deliberately not another report table: the combinations are editorial, add no
measurement, and hide that a mechanism can dominate one workload while being
irrelevant to another.

For the specific always-on design question:

- matching the baseline's typechecking cost alone implies `1.51x`; matching
  other frontend/install alone implies `1.52x`, and matching both implies
  `1.40x`;
- eliminating Equality ruleset assembly alone implies `1.53x`, while making
  the entire net Equality/rebuild responsibility baseline-equivalent implies
  `1.47x`;
- eliminating the net source-rule execution delta implies `1.44x`; and
- even eliminating every positive non-program delta while holding the Program
  delta fixed implies about `1.20x`.

These are point-estimate accounting bounds, not implementation predictions.
They have no confidence intervals and do not model interactions: removing
generated types or identities may also change Program Search, Apply, Merge, or
plan assembly. The per-workload rows below are the primary evidence for
choosing an optimization.

## Workload narratives

- **Math:** Equality/rebuild is 62.5% of the slowdown. Generated maintenance
  costs 412 ms and replaces 142 ms of native rebuild. This is the clearest
  relational-UF target, though changed default-rule Apply and Merge still add
  145 ms.
- **eggcc:** no single mechanism wins. Typecheck plus frontend adds 139 ms,
  source rules add 113 ms, net Equality adds 86 ms, and commands add 35 ms.
  Equality is assembly-heavy: 248 ms of added assembly is almost exactly
  offset by 247 ms of removed native rebuild before Search and execution are
  counted. `always-run` carries 86 ms of the Program delta.
- **Pointer analysis:** net Equality is largest at 30 ms, frontend is 21 ms,
  and Program is 11 ms. Its 10.1 ms residual is large enough that tiny
  sub-mechanism conclusions should remain cautious.
- **Hardboiled:** source rules add 35 ms, while typecheck plus frontend adds
  49 ms. The default ruleset's Search dominates its Program child; check
  evaluation is routed symmetrically under Commands rather than appearing as a
  term-only default ruleset artifact.
- **Luminal:** Program is 408 ms, 46.4% of the slowdown; Equality is only
  44.8 ms, 5.10%. `fusion_grow` and `fusion_pair` add 170 and 148 ms, almost
  entirely Search. Typecheck plus frontend adds another 344 ms. UF work is not
  the limiting explanation here.
- **Herbie:** mixed across Program (26.6%), Equality (22.3%), frontend/typecheck
  (32.8%), and Commands (15.4%).
- **Misaal HVX:** typecheck plus frontend explains 90.3% of the slowdown.
  Program and Equality together explain about 4.1%; a UF optimization would
  barely move it.
- **Churchroad:** Program Search improves by 303 ms net, making term encoding
  faster overall despite every other top-level mechanism becoming slower.
- **DialEgg:** Program contributes 57.8%, led by Apply and Merge; net Equality
  contributes 16.3%.
- **SPEQ:** Program contributes 73.9%, mostly assembly in four transform
  rulesets; Equality is below 1%.

## What this answers—and what it does not

The additive report now answers:

- how much slowdown is frontend, source-rule execution, relational
  equality/rebuild, commands, or residual;
- whether Equality cost is assembly or execution;
- which source or maintenance rulesets carry Program and Equality changes; and
- the suite sum and the distinct per-workload mechanism mixes.

It does not identify why a source rule searches or assembles more slowly. For
Luminal, the data localizes the problem to `fusion_grow`/`fusion_pair` Search,
but distinguishing wider tuples, extra identity columns, changed join order,
or greater state churn requires a profiler or a targeted lowering ablation.
Likewise, the derived bounds cannot predict cross-mechanism effects.

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
| Analysis | Align endpoint samples and derive residual, mechanisms, and drivers | One generic path-sample ledger; parent/child sums are direct |
| Presentation | Decomposition and per-file drivers | One shared catalog and table renderer for Rich, Markdown, and interactive output |

The final reduction pass kept the old execution path recognizable and removed
presentation-only alternatives: there is no global phase-rollup model, no
ten-column ruleset table, no duplicated fixed five-bucket wire record, and no
special report-time native-rebuild credit. Counterfactual combinations stay in
the engineering analysis rather than becoming another report model. Further
reduction would either lose the Assembly/Search distinction that separates
plan-cache work from query-shape work or make the signs in the ruleset panel
misleading again.

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
