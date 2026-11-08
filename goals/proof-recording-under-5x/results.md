# Proof recording below 5×

**Complete.** All 127 frozen replays have ten fresh successful off and recording-only observations on one executable. Every per-replay ratio of arithmetic means is below 5× for both runtime and peak RSS. Acceptance uses the mean-ratio criterion; the individual 95% Fieller intervals below retain its measurement uncertainty.

| Original outlier | Metric | Fresh baseline ratio (3 runs) | Final ratio (10 runs) | Final 95% interval |
| --- | --- | ---: | ---: | --- |
| luminal/gemma-call-01.egg | Runtime | 7.072× | 4.979× | [4.9143, 5.0444] |
| luminal/gemma4_moe-call-01.egg | Runtime | 6.305× | 4.599× | [4.5288, 4.6697] |
| dialegg/timer-nmm-80-call-01.egg | Peak RSS | 6.716× | 4.294× | [4.2942, 4.2946] |

These are measured per-replay mean ratios on this host, with independent-sample intervals, rather than a guarantee about future runs or other machines.

## Bottlenecks and changes

- Luminal setup expands into a large generated action program. The baseline Gemma profile spends 42.3% of sampled CPU in typechecking; the profile after adaptive map storage spends 30.35% there. Inclusive shares overlap. Fixed-signature compatibility checks, direct reads of already-bound eq-sort globals, parsing the existing local `(begin ...)` scope directly, removal of unread bare fresh IDs, and lazy canonical-ID interning reduce redundant work. Fresh backend calls omit unreachable panic fallbacks. Adaptive assignment storage uses flat lookup during inference and the original persistent representation after the first branch snapshot, reducing inference/annotation overhead without repeated large-map copies. The known required-variable count reserves initial flat capacity once.
- DialEgg retains 17.1 million hidden recording rows in the baseline diagnostic, including 8.7 million RuleLink rows. Constant-column chunks retain all submitted row values and logical row identities while avoiding contiguous growth/copying and repeating constant values. Final DialEgg recording RSS is about 571 MiB, versus about 892 MiB in the fresh baseline.
- The encoder-wide typed generation conversion and new strongly typed Rust authoring API remain deferred. The current generated text, parser, typechecker and runtime pipeline remain in place.
- Eli’s sequence-container PR stack #974–#985, tip `df7e28de604546c747435eabab89fd935e83e7d1`, conflicts in 13 downstream files across the container API and newer executor. The bounded integration attempt was saved and the experiment checkout restored. Its performance on this encoder is unmeasured; no gain is attributed to that stack.

The retained source changes are `ec8bea0b` (proof-table storage), `81db104d` (generated-action work), `427783b3` (frozen figure cohort), and `915fec1c` plus `c5d94ad8` (adaptive assignment storage), based on `e8a2a58d`. The unconditional flat-map policy in `915fec1c` was rejected: its 869-file-test suite took 147.41 s. The retained snapshot policy restores that suite to about 9.6 s and keeps the existing rollback/inference order. Signature-cache and borrowed-key trials were discarded. The final one-line capacity reservation is committed in `ede9f943`. Native Math correctness runs separately without a memory guard (`c0f9c91f`); its source Math oracle keeps the configured cap. The assignment map’s concrete public field type is now `AssignmentMap`; external callers constructing the old map or using iteration/other map-specific methods through `.0` may need adaptation. Existing get/insert/clone consumers pass the workspace checks.

## Scope and evidence

- Exactly 2,540 new observations, ten per treatment and byte-identical frozen input; no failed, missing, old or extra observations. Both treatments use executable SHA-256 `b9b6cd18c23a141db285c0f5f91864d589023e1abfece0d56a0fe67a9a97c517`.
- The source is pinned at `ede9f94368994e403893e55edf6e35ec66c826b2` and unchanged throughout collection. Timeout is 500 seconds; the allocator cap is 16 GiB with the same startup settings used for the fresh baseline. Original input schedules are unchanged.
- Raw rows mark the checkout dirty because an untracked task checkpoint was present. The captured tracked-source patch is empty and both collection revision pins agree; the checkpoint did not change compiled source.
- Eligibility remains the original frozen 127 identities, regardless of whether a fresh off mean crosses the historical 0.2-second cutoff. No replay is dropped from the final figure.
- The real-data Vega audit matches all 254 plotted ratios against the acceptance dataset, checks 127 unique identities in each metric, full empirical ranks and in-bounds geometry, and confirms that no overview composition remains.
- Local `RUST_TEST_ARGS='--skip paper/' UV_PYTHON=3.12 make check` passes on byte-identical non-goal source. The earlier full paper run passed 510 tests and failed only native Math at its 16 GiB VM guard. The user-requested uncapped-native/capped-source Math rerun passes both tests. The original failed invocation remains explicit; no exclusion was added. See [final validation](final-validation.json) for exact scopes, source comparison and log hashes.

The paired paper branch is `codex/fix-recording-overview` in `/Users/saul/p/wt/extended-egglog-paper/fix-recording-overview`, committed at `3045d9e9cee4ef37181dfea74859337eac95320e`. It contains the recording PDF, numeric macros and per-file table, with a caption/provenance note identifying this optimized implementation. Other figure measurements retain their existing revisions.

The [performance acceptance dataset](final-acceptance.json) contains every mean, interval, identity and audit issue. [Collection provenance](final-cohort-provenance.json) contains exact argv, UTC bounds and revision/hash pins. The [figure audit](figure-audit.json), [experiment ledger](experiments.md), [baseline profile](gemma-profile-inclusive.json), and [adaptive-map profile](gemma-c5-profile-inclusive.json) supply the supporting evidence. The [final handoff](final-handoff.json) pins the verified PDF, numeric exports, paper revision and manuscript-width visual inspection.

Raw reports, grouped snapshots, source patches, diagnostic captures, profiles, public-CLI output and the reproducible task-local collector/checker/figure-audit scripts are retained in ignored `benchmarks/local/proof-recording-under-5x/`. They are intentionally local evidence, outside Cargo’s disposable build cache. The final report is `final-cohort-v3.jsonl`; the passing CI-profile validation log is `make-check-ci-final.log`, and the failed default-profile attempt is `make-check-final.log`; final figure companions are under `final-figure/`.

## Reproduce locally

Use the pinned source revision and the existing locked Python 3.12 environment. The retained task-local collector expands the exact ordered file list from `cohort.json`, checks its hashes, and invokes the public `./bench.py` command. Use a new stem to retain the original evidence:

```sh
.venv/bin/python benchmarks/local/proof-recording-under-5x/collect_cohort.py --rounds 10 --stem recheck-recording
```

On a fresh checkout, restore the four task-local tools with `git apply goals/proof-recording-under-5x/evidence-tools.patch`. The patch has been apply-checked and byte-verified. The collector records the exact public command in its provenance JSON. The following commands audit and render the retained final dataset; for a new collection substitute its report name and provenance’s `started_at`. The figure command reuses the ten observations without collecting more:

```sh
.venv/bin/python -m benchmarks.local.proof-recording-under-5x.check_acceptance \
  --report benchmarks/local/proof-recording-under-5x/final-cohort-v3.jsonl \
  --binary target/release/egglog-experimental --rounds 10 --timeout-sec 500 \
  --since 2026-11-08T10:03:36.910131+00:00 \
  --out benchmarks/local/proof-recording-under-5x/acceptance-rechecked.json
.venv/bin/python benchmarks/local/proof-recording-under-5x/prepare_figure.py
UV_PYTHON=3.12 ./bench.py figures corpus-proof-recording-cdf \
  --config benchmarks/local/proof-recording-under-5x/final-figure/catalog.json \
  --target . --memory-limit \
  --report benchmarks/local/proof-recording-under-5x/final-cohort-v3.jsonl \
  --output-dir benchmarks/local/proof-recording-under-5x/final-figure
npx --yes --package=vega@6.4.0 --package=vega-lite@6.4.3 \
  --package=vega-cli@6.4.0 --package=canvas@3.2.3 \
  node benchmarks/local/proof-recording-under-5x/audit_figure.mjs
```

Prepare the custom catalog with `.venv/bin/python benchmarks/local/proof-recording-under-5x/prepare_figure.py`. It lists only the frozen 127 files, off/proofs treatments, and no extra checking treatment. Its copy of the shared figure spec sets `frozen_cohort=true`. The figure command confirmed 2,540/2,540 observations cached and collected nothing new.

## Per-replay results

Wall times are seconds; RSS is MiB. Ratios and intervals use unrounded data. Each endpoint has n=10.

| Replay | Off → recording wall | Runtime ratio [95% CI] | Off → recording RSS | RSS ratio [95% CI] |
| --- | ---: | --- | ---: | --- |
| eggcc/cordic-statewalk-call-03.egg | 0.3344 → 0.8870 | 2.6526× [2.5716, 2.7350] | 60.71 → 153.98 | 2.5364× [2.5361, 2.5366] |
| eggcc/csrmv-statewalk-call-03.egg | 0.2436 → 0.7020 | 2.8811× [2.7652, 2.9995] | 51.79 → 130.38 | 2.5172× [2.5169, 2.5174] |
| eggcc/gemm-statewalk-call-01.egg | 0.2644 → 0.7194 | 2.7206× [2.5910, 2.8527] | 54.34 → 138.75 | 2.5532× [2.5530, 2.5534] |
| eggcc/gramschmidt-statewalk-call-01.egg | 0.2593 → 0.7004 | 2.7014× [2.5756, 2.8368] | 54.60 → 134.75 | 2.4679× [2.4675, 2.4683] |
| eggcc/gramschmidt-statewalk-call-03.egg | 0.2389 → 0.6725 | 2.8152× [2.6378, 2.9974] | 53.49 → 132.19 | 2.4712× [2.4709, 2.4716] |
| eggcc/nussinov-statewalk-call-03.egg | 0.2714 → 0.7532 | 2.7750× [2.5387, 3.0529] | 52.23 → 128.40 | 2.4584× [2.4581, 2.4587] |
| eggcc/symm-statewalk-call-01.egg | 0.2375 → 0.6791 | 2.8593× [2.7643, 2.9557] | 50.63 → 127.77 | 2.5235× [2.5232, 2.5238] |
| eggcc/symm-statewalk-call-03.egg | 0.2214 → 0.6595 | 2.9793× [2.8370, 3.1247] | 52.57 → 128.73 | 2.4486× [2.4483, 2.4489] |
| eggcc/syr2k-statewalk-call-01.egg | 0.2194 → 0.6257 | 2.8522× [2.7356, 2.9703] | 47.89 → 123.09 | 2.5705× [2.5580, 2.5829] |
| hardboiled/published-conv1d_168-call-01.egg | 0.2353 → 0.3830 | 1.6280× [1.5250, 1.7450] | 28.01 → 63.66 | 2.2727× [2.2721, 2.2733] |
| hardboiled/published-conv1d_176-call-01.egg | 0.2085 → 0.3773 | 1.8099× [1.7772, 1.8429] | 28.72 → 64.47 | 2.2447× [2.2441, 2.2453] |
| hardboiled/published-conv1d_184-call-01.egg | 0.2190 → 0.3992 | 1.8230× [1.7647, 1.8818] | 29.27 → 65.62 | 2.2423× [2.2416, 2.2430] |
| hardboiled/published-conv1d_192-call-01.egg | 0.2292 → 0.4241 | 1.8505× [1.7824, 1.9195] | 29.78 → 66.29 | 2.2257× [2.2252, 2.2263] |
| hardboiled/published-conv1d_200-call-01.egg | 0.2389 → 0.4300 | 1.8000× [1.7549, 1.8458] | 30.34 → 67.43 | 2.2224× [2.2220, 2.2227] |
| hardboiled/published-conv1d_208-call-01.egg | 0.2549 → 0.4478 | 1.7567× [1.7189, 1.7952] | 30.99 → 68.10 | 2.1975× [2.1970, 2.1981] |
| hardboiled/published-conv1d_216-call-01.egg | 0.2605 → 0.4721 | 1.8124× [1.7652, 1.8601] | 30.94 → 69.28 | 2.2395× [2.2389, 2.2401] |
| hardboiled/published-conv1d_224-call-01.egg | 0.2815 → 0.4850 | 1.7227× [1.6715, 1.7747] | 31.18 → 70.06 | 2.2474× [2.2469, 2.2479] |
| hardboiled/published-conv1d_232-call-01.egg | 0.2825 → 0.4986 | 1.7649× [1.7281, 1.8024] | 31.37 → 71.13 | 2.2673× [2.2669, 2.2677] |
| hardboiled/published-conv1d_240-call-01.egg | 0.3016 → 0.5141 | 1.7044× [1.6695, 1.7398] | 31.62 → 72.01 | 2.2773× [2.2769, 2.2777] |
| hardboiled/published-conv1d_248-call-01.egg | 0.3066 → 0.5386 | 1.7570× [1.7196, 1.7947] | 32.12 → 72.88 | 2.2691× [2.2686, 2.2696] |
| hardboiled/published-conv1d_256-call-01.egg | 0.3369 → 0.5579 | 1.6558× [1.5948, 1.7202] | 33.35 → 72.81 | 2.1829× [2.1825, 2.1833] |
| hardboiled/published-matmul-call-01.egg | 0.2526 → 0.3737 | 1.4794× [1.4504, 1.5093] | 24.21 → 54.69 | 2.2593× [2.2587, 2.2598] |
| hardboiled/published-rec_filter-call-01.egg | 0.2545 → 0.6842 | 2.6891× [2.6637, 2.7147] | 30.30 → 81.88 | 2.7020× [2.7013, 2.7027] |
| hardboiled/published-upsample_16-call-01.egg | 0.3164 → 0.5153 | 1.6288× [1.6097, 1.6480] | 28.45 → 64.53 | 2.2678× [2.2676, 2.2680] |
| hardboiled/published-upsample_32-call-01.egg | 1.3743 → 2.0690 | 1.5055× [1.4831, 1.5285] | 44.25 → 104.94 | 2.3717× [2.3713, 2.3721] |
| misaal/arm-add-call-03.egg | 0.2246 → 0.7089 | 3.1560× [3.1135, 3.1989] | 153.25 → 344.36 | 2.2471× [2.2470, 2.2472] |
| misaal/arm-add-call-06.egg | 0.2259 → 0.7049 | 3.1205× [3.0565, 3.1853] | 153.20 → 344.17 | 2.2465× [2.2465, 2.2466] |
| misaal/arm-blur5x5-call-02.egg | 0.2157 → 0.6885 | 3.1921× [3.1410, 3.2444] | 146.35 → 331.01 | 2.2618× [2.2617, 2.2619] |
| misaal/arm-blur5x5-call-04.egg | 0.2187 → 0.6847 | 3.1304× [3.0919, 3.1695] | 146.38 → 330.89 | 2.2605× [2.2604, 2.2605] |
| misaal/arm-blur7x7-call-02.egg | 0.2154 → 0.6930 | 3.2168× [3.1758, 3.2583] | 147.05 → 331.44 | 2.2539× [2.2538, 2.2540] |
| misaal/arm-conv3x3a16-call-01.egg | 0.2409 → 0.7136 | 2.9626× [2.9088, 3.0177] | 155.47 → 346.20 | 2.2268× [2.2268, 2.2269] |
| misaal/arm-conv3x3a16-call-02.egg | 0.2300 → 0.7527 | 3.2725× [2.8274, 3.7203] | 155.45 → 343.03 | 2.2067× [2.1618, 2.2516] |
| misaal/arm-conv_nn-call-05.egg | 0.2619 → 0.7599 | 2.9017× [2.8702, 2.9334] | 182.77 → 398.55 | 2.1806× [2.1805, 2.1807] |
| misaal/arm-conv_nn-call-07.egg | 0.2404 → 0.7166 | 2.9811× [2.9498, 3.0128] | 163.43 → 354.70 | 2.1703× [2.1702, 2.1704] |
| misaal/arm-conv_nn-call-18.egg | 0.2351 → 0.7180 | 3.0536× [3.0049, 3.1036] | 163.44 → 354.75 | 2.1705× [2.1704, 2.1706] |
| misaal/arm-conv_nn-call-19.egg | 0.2610 → 0.7610 | 2.9155× [2.8766, 2.9549] | 182.88 → 398.71 | 2.1801× [2.1800, 2.1802] |
| misaal/arm-depthwise_conv-call-02.egg | 0.2036 → 0.6643 | 3.2629× [3.2283, 3.2978] | 140.30 → 317.32 | 2.2617× [2.2616, 2.2619] |
| misaal/arm-depthwise_conv-call-03.egg | 0.2159 → 0.6911 | 3.2002× [3.1536, 3.2472] | 148.39 → 333.72 | 2.2489× [2.2488, 2.2490] |
| misaal/arm-depthwise_conv-call-05.egg | 0.2056 → 0.6709 | 3.2628× [3.2187, 3.3077] | 140.12 → 317.47 | 2.2658× [2.2657, 2.2659] |
| misaal/arm-depthwise_conv-call-06.egg | 0.2247 → 0.6956 | 3.0962× [3.0600, 3.1330] | 153.68 → 346.38 | 2.2539× [2.2538, 2.2540] |
| misaal/arm-depthwise_conv-call-12.egg | 0.2382 → 0.7009 | 2.9425× [2.8964, 2.9898] | 153.73 → 346.43 | 2.2535× [2.2534, 2.2536] |
| misaal/arm-depthwise_conv-call-14.egg | 0.2170 → 0.6812 | 3.1399× [3.1066, 3.1736] | 140.32 → 317.49 | 2.2625× [2.2625, 2.2626] |
| misaal/arm-depthwise_conv-call-15.egg | 0.2171 → 0.6656 | 3.0659× [3.0350, 3.0972] | 140.15 → 317.53 | 2.2656× [2.2656, 2.2657] |
| misaal/arm-depthwise_conv-call-16.egg | 0.2279 → 0.6949 | 3.0491× [3.0230, 3.0754] | 148.44 → 333.90 | 2.2494× [2.2493, 2.2496] |
| misaal/arm-fully_connected-call-02.egg | 0.2032 → 0.6631 | 3.2630× [3.2219, 3.3045] | 140.38 → 317.39 | 2.2609× [2.2608, 2.2610] |
| misaal/arm-fully_connected-call-08.egg | 0.2184 → 0.6660 | 3.0494× [3.0045, 3.0948] | 140.39 → 317.53 | 2.2618× [2.2618, 2.2619] |
| misaal/arm-gaussian7x7-call-02.egg | 0.2292 → 0.6979 | 3.0450× [3.0024, 3.0884] | 152.41 → 343.60 | 2.2545× [2.2544, 2.2546] |
| misaal/arm-l2norm-call-01.egg | 0.2239 → 0.7045 | 3.1469× [3.1063, 3.1882] | 153.06 → 343.87 | 2.2467× [2.2466, 2.2468] |
| misaal/arm-l2norm-call-02.egg | 0.2185 → 0.6890 | 3.1528× [3.1051, 3.2013] | 148.44 → 333.74 | 2.2484× [2.2482, 2.2485] |
| misaal/arm-matmul_256_32bit_bias_add_add-call-02.egg | 0.2158 → 0.6640 | 3.0765× [3.0119, 3.1427] | 137.05 → 312.76 | 2.2822× [2.2821, 2.2823] |
| misaal/arm-matmul_256_32bit_bias_add_add-call-04.egg | 0.2072 → 0.6816 | 3.2901× [2.9596, 3.6373] | 137.06 → 308.57 | 2.2513× [2.1834, 2.3192] |
| misaal/arm-median3x3-call-01.egg | 0.2203 → 0.7102 | 3.2236× [2.8575, 3.6280] | 136.00 → 300.73 | 2.2112× [2.1137, 2.3086] |
| misaal/arm-median3x3-call-03.egg | 0.2119 → 0.6805 | 3.2108× [3.1866, 3.2353] | 135.62 → 305.86 | 2.2554× [2.2552, 2.2555] |
| misaal/arm-median3x3-call-06.egg | 0.2206 → 0.6907 | 3.1308× [3.1125, 3.1493] | 135.60 → 305.83 | 2.2554× [2.2553, 2.2555] |
| misaal/arm-median3x3-call-07.egg | 0.2144 → 0.6811 | 3.1774× [3.1571, 3.1979] | 136.00 → 306.47 | 2.2536× [2.2535, 2.2537] |
| misaal/arm-mul-call-01.egg | 0.2291 → 0.7068 | 3.0848× [3.0472, 3.1230] | 154.30 → 347.09 | 2.2495× [2.2494, 2.2495] |
| misaal/arm-softmax-call-01.egg | 0.2300 → 0.7030 | 3.0564× [3.0317, 3.0814] | 152.03 → 342.81 | 2.2550× [2.2549, 2.2550] |
| misaal/arm-softmax-call-03.egg | 0.2129 → 0.6827 | 3.2073× [3.1841, 3.2306] | 145.53 → 332.61 | 2.2855× [2.2855, 2.2856] |
| misaal/arm-softmax-call-05.egg | 0.3122 → 0.8452 | 2.7074× [2.6761, 2.7392] | 193.73 → 418.91 | 2.1624× [2.1623, 2.1624] |
| misaal/arm-softmax-call-06.egg | 0.2267 → 0.7001 | 3.0880× [3.0580, 3.1182] | 154.07 → 346.74 | 2.2504× [2.2503, 2.2506] |
| misaal/arm-softmax-call-08.egg | 0.3135 → 0.8439 | 2.6919× [2.6685, 2.7156] | 193.62 → 418.77 | 2.1629× [2.1628, 2.1630] |
| misaal/arm-softmax-call-09.egg | 0.2251 → 0.6968 | 3.0961× [3.0763, 3.1160] | 154.06 → 346.55 | 2.2495× [2.2494, 2.2496] |
| misaal/arm-softmax-call-11.egg | 0.2261 → 0.7049 | 3.1181× [3.0955, 3.1409] | 151.98 → 342.63 | 2.2544× [2.2544, 2.2545] |
| misaal/arm-softmax-call-14.egg | 0.2131 → 0.6815 | 3.1986× [3.1706, 3.2270] | 145.49 → 332.52 | 2.2855× [2.2854, 2.2856] |
| misaal/hexagon-tensor_add-call-01.egg | 1.7209 → 6.6864 | 3.8854× [3.4363, 4.3371] | 1044.12 → 2674.13 | 2.5611× [2.5611, 2.5612] |
| misaal/x86-average_pool-call-01.egg | 0.3076 → 1.0168 | 3.3055× [2.4681, 4.5659] | 185.45 → 419.93 | 2.2644× [2.2644, 2.2645] |
| misaal/x86-average_pool_add-call-01.egg | 0.2787 → 0.9370 | 3.3617× [3.3338, 3.3897] | 185.58 → 419.96 | 2.2630× [2.2629, 2.2630] |
| misaal/x86-batched_matmul_256_32bit-call-01.egg | 0.2351 → 0.8713 | 3.7062× [3.6892, 3.7233] | 158.07 → 371.71 | 2.3515× [2.3514, 2.3516] |
| misaal/x86-blur3x3-call-01.egg | 0.2358 → 0.8785 | 3.7262× [3.7120, 3.7405] | 158.31 → 372.07 | 2.3503× [2.3502, 2.3503] |
| misaal/x86-blur3x3-call-02.egg | 0.2365 → 0.8758 | 3.7025× [3.6811, 3.7241] | 158.25 → 371.89 | 2.3501× [2.3500, 2.3501] |
| misaal/x86-blur5x5-call-01.egg | 0.2369 → 0.8718 | 3.6800× [3.6506, 3.7098] | 158.23 → 372.00 | 2.3510× [2.3509, 2.3512] |
| misaal/x86-blur7x7-call-01.egg | 0.2462 → 0.9317 | 3.7848× [3.3246, 4.2453] | 158.28 → 372.02 | 2.3503× [2.3502, 2.3505] |
| misaal/x86-conv3x3a16-call-01.egg | 0.2958 → 0.9773 | 3.3046× [2.8199, 3.9281] | 187.20 → 422.98 | 2.2595× [2.2594, 2.2596] |
| misaal/x86-conv_nn-call-01.egg | 0.3650 → 1.0532 | 2.8853× [2.4038, 3.5653] | 214.79 → 470.99 | 2.1928× [2.1927, 2.1929] |
| misaal/x86-conv_nn-call-02.egg | 0.3714 → 1.1050 | 2.9755× [2.8086, 3.1575] | 242.21 → 520.42 | 2.1486× [2.1485, 2.1487] |
| misaal/x86-conv_nn-call-03.egg | 0.2371 → 0.8838 | 3.7273× [3.6606, 3.7952] | 158.08 → 371.79 | 2.3519× [2.3518, 2.3520] |
| misaal/x86-conv_nn-call-04.egg | 0.3655 → 1.2037 | 3.2932× [2.5743, 4.0151] | 242.90 → 521.17 | 2.1456× [2.1456, 2.1457] |
| misaal/x86-conv_nn-call-05.egg | 0.2737 → 1.0103 | 3.6919× [2.9949, 4.4009] | 186.31 → 420.40 | 2.2565× [2.2564, 2.2566] |
| misaal/x86-conv_nn-call-06.egg | 0.2873 → 1.0078 | 3.5073× [2.8598, 4.1753] | 187.08 → 421.12 | 2.2511× [2.2511, 2.2511] |
| misaal/x86-depthwise_conv-call-01.egg | 0.2713 → 1.0046 | 3.7032× [3.0440, 4.3643] | 186.26 → 420.27 | 2.2564× [2.2563, 2.2565] |
| misaal/x86-depthwise_conv-call-02.egg | 0.2374 → 0.9510 | 4.0058× [3.3586, 4.6551] | 157.84 → 370.77 | 2.3490× [2.3489, 2.3491] |
| misaal/x86-depthwise_conv-call-03.egg | 0.2381 → 0.8961 | 3.7633× [3.5920, 3.9363] | 158.02 → 371.47 | 2.3509× [2.3508, 2.3510] |
| misaal/x86-depthwise_conv-call-04.egg | 0.2511 → 0.8828 | 3.5163× [3.4238, 3.6107] | 158.53 → 371.79 | 2.3453× [2.3452, 2.3454] |
| misaal/x86-dilate3x3-call-01.egg | 0.2869 → 0.9649 | 3.3637× [3.2695, 3.4607] | 181.96 → 416.45 | 2.2886× [2.2886, 2.2887] |
| misaal/x86-dilate5x5-call-01.egg | 0.2660 → 0.9384 | 3.5275× [3.4484, 3.6084] | 176.04 → 404.39 | 2.2971× [2.2970, 2.2972] |
| misaal/x86-dilate7x7-call-01.egg | 0.2873 → 0.9579 | 3.3343× [3.1994, 3.4736] | 179.28 → 411.09 | 2.2930× [2.2930, 2.2931] |
| misaal/x86-fully_connected-call-01.egg | 0.2870 → 0.9588 | 3.3404× [3.2211, 3.4634] | 190.36 → 428.84 | 2.2528× [2.2527, 2.2528] |
| misaal/x86-gaussian3x3-call-01.egg | 0.2394 → 0.8863 | 3.7019× [3.6076, 3.7987] | 158.61 → 372.46 | 2.3482× [2.3481, 2.3483] |
| misaal/x86-gaussian3x3-call-02.egg | 0.2431 → 0.8864 | 3.6469× [3.5708, 3.7237] | 158.63 → 372.52 | 2.3484× [2.3483, 2.3485] |
| misaal/x86-gaussian5x5-call-01.egg | 0.2460 → 0.8900 | 3.6186× [3.5371, 3.7021] | 158.66 → 372.84 | 2.3499× [2.3498, 2.3500] |
| misaal/x86-gaussian5x5-call-02.egg | 0.2492 → 0.8937 | 3.5865× [3.4797, 3.6953] | 158.39 → 372.19 | 2.3498× [2.3497, 2.3499] |
| misaal/x86-gaussian7x7-call-01.egg | 0.2743 → 0.9448 | 3.4443× [3.3618, 3.5290] | 184.17 → 418.16 | 2.2705× [2.2705, 2.2705] |
| misaal/x86-gaussian7x7-call-02.egg | 0.2391 → 0.8945 | 3.7413× [3.6271, 3.8575] | 159.47 → 374.09 | 2.3459× [2.3458, 2.3459] |
| misaal/x86-gaussian7x7-call-03.egg | 0.2730 → 0.9492 | 3.4772× [3.3731, 3.5853] | 185.22 → 419.55 | 2.2652× [2.2651, 2.2652] |
| misaal/x86-l2norm-call-01.egg | 0.2809 → 0.9486 | 3.3769× [3.2879, 3.4689] | 186.93 → 422.48 | 2.2601× [2.2601, 2.2602] |
| misaal/x86-l2norm-call-02.egg | 0.2839 → 0.9650 | 3.3997× [3.3216, 3.4798] | 188.95 → 426.36 | 2.2565× [2.2565, 2.2566] |
| misaal/x86-l2norm-call-03.egg | 0.2750 → 0.9459 | 3.4401× [3.3507, 3.5327] | 187.52 → 421.84 | 2.2495× [2.2495, 2.2496] |
| misaal/x86-matmul_256_32bit_bias_add_gelu-call-01.egg | 0.2349 → 0.8852 | 3.7686× [3.6726, 3.8675] | 157.43 → 370.32 | 2.3523× [2.3522, 2.3524] |
| misaal/x86-matmul_256_32bit_bias_add_gelu-call-03.egg | 0.2430 → 0.8897 | 3.6613× [3.5675, 3.7567] | 158.20 → 371.58 | 2.3488× [2.3487, 2.3489] |
| misaal/x86-matmul_256_32bit_bias_add_relu-call-02.egg | 0.2498 → 0.8996 | 3.6014× [3.5381, 3.6658] | 167.31 → 387.44 | 2.3157× [2.3156, 2.3158] |
| misaal/x86-matmul_bias_relu_matmul-call-01.egg | 0.2376 → 0.8796 | 3.7023× [3.6359, 3.7704] | 158.16 → 371.65 | 2.3499× [2.3498, 2.3500] |
| misaal/x86-max_pool-call-01.egg | 0.2495 → 0.9200 | 3.6866× [3.6354, 3.7382] | 166.88 → 387.75 | 2.3235× [2.3234, 2.3236] |
| misaal/x86-max_pool-call-02.egg | 0.2666 → 0.9494 | 3.5613× [3.4367, 3.6877] | 180.26 → 410.31 | 2.2762× [2.2761, 2.2763] |
| misaal/x86-max_pool_add-call-02.egg | 0.2764 → 0.9529 | 3.4477× [3.2264, 3.6894] | 180.26 → 410.33 | 2.2763× [2.2762, 2.2764] |
| misaal/x86-median3x3-call-01.egg | 0.3734 → 1.1344 | 3.0382× [2.8820, 3.2006] | 223.15 → 487.22 | 2.1834× [2.1833, 2.1835] |
| misaal/x86-median3x3-call-02.egg | 0.3198 → 1.0241 | 3.2021× [3.0986, 3.3082] | 201.59 → 451.12 | 2.2378× [2.2377, 2.2379] |
| misaal/x86-median3x3-call-03.egg | 0.3874 → 1.1839 | 3.0560× [2.9716, 3.1429] | 224.39 → 505.21 | 2.2515× [2.2514, 2.2515] |
| misaal/x86-median3x3-call-04.egg | 0.2962 → 0.9818 | 3.3144× [3.2584, 3.3713] | 194.67 → 437.48 | 2.2473× [2.2473, 2.2474] |
| misaal/x86-mul-call-01.egg | 0.2799 → 0.9428 | 3.3677× [3.3195, 3.4166] | 186.97 → 422.44 | 2.2594× [2.2593, 2.2594] |
| misaal/x86-mul-call-02.egg | 0.2388 → 0.8878 | 3.7173× [3.6605, 3.7747] | 158.50 → 372.05 | 2.3473× [2.3472, 2.3474] |
| misaal/x86-mul-call-03.egg | 0.2793 → 0.9511 | 3.4048× [3.3191, 3.4930] | 185.50 → 420.08 | 2.2646× [2.2646, 2.2647] |
| misaal/x86-mul-call-04.egg | 0.2368 → 0.8838 | 3.7321× [3.6817, 3.7831] | 157.97 → 370.95 | 2.3483× [2.3482, 2.3484] |
| misaal/x86-mul-call-05.egg | 0.2889 → 0.9651 | 3.3403× [3.2939, 3.3873] | 190.14 → 428.44 | 2.2533× [2.2533, 2.2534] |
| misaal/x86-sobel3x3-call-01.egg | 0.3431 → 1.0687 | 3.1152× [3.0555, 3.1757] | 216.05 → 475.26 | 2.1997× [2.1996, 2.1998] |
| misaal/x86-sobel5x5-call-01.egg | 0.2400 → 0.8827 | 3.6777× [3.6066, 3.7505] | 158.56 → 372.22 | 2.3475× [2.3473, 2.3476] |
| misaal/x86-sobel5x5-call-02.egg | 0.4124 → 1.2027 | 2.9161× [2.8760, 2.9568] | 243.98 → 526.18 | 2.1566× [2.1566, 2.1566] |
| misaal/x86-softmax-call-01.egg | 0.2349 → 0.8774 | 3.7348× [3.6771, 3.7933] | 157.40 → 370.30 | 2.3526× [2.3525, 2.3527] |
| misaal/x86-softmax-call-03.egg | 0.2851 → 0.9411 | 3.3007× [3.2550, 3.3470] | 187.72 → 422.50 | 2.2507× [2.2506, 2.2508] |
| misaal/x86-softmax-call-04.egg | 0.2400 → 0.8838 | 3.6821× [3.6361, 3.7288] | 158.28 → 371.97 | 2.3501× [2.3500, 2.3502] |
| misaal/x86-softmax-call-05.egg | 0.2368 → 0.8788 | 3.7104× [3.6701, 3.7511] | 158.63 → 372.44 | 2.3479× [2.3478, 2.3480] |
| misaal/x86-softmax-call-06.egg | 0.2812 → 0.9507 | 3.3806× [3.3200, 3.4424] | 187.24 → 422.96 | 2.2589× [2.2588, 2.2590] |
| misaal/x86-softmax-call-07.egg | 0.2330 → 0.8869 | 3.8072× [3.7520, 3.8631] | 157.44 → 370.33 | 2.3521× [2.3520, 2.3523] |
| misaal/x86-softmax-call-08.egg | 0.2729 → 0.9422 | 3.4523× [3.3970, 3.5086] | 185.80 → 420.38 | 2.2625× [2.2625, 2.2626] |
| misaal/x86-tensor_shr-call-01.egg | 0.2383 → 0.8854 | 3.7160× [3.6567, 3.7762] | 158.26 → 372.03 | 2.3507× [2.3506, 2.3508] |
| dialegg/timer-nmm-80-call-01.egg | 1.4810 → 2.7805 | 1.8774× [1.8277, 1.9282] | 132.88 → 570.64 | 4.2944× [4.2942, 4.2946] |
| luminal/gemma-call-01.egg | 0.3216 → 1.6015 | 4.9789× [4.9143, 5.0444] | 56.64 → 159.78 | 2.8210× [2.8209, 2.8211] |
| luminal/gemma4_moe-call-01.egg | 0.6794 → 3.1241 | 4.5986× [4.5288, 4.6697] | 79.56 → 222.38 | 2.7951× [2.7949, 2.7952] |
