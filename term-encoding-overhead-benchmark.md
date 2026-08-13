# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | d60202f64424 | d60202f64424 | off |
| Candidate | d60202f64424 | d60202f64424 | term |

*10 file(s): math-microbenchmark-rational.egg, eggcc-2mm-pass1.egg, pointer-analysis-initdb.egg (facts: /Users/saul/p/wt/egglog-encoding/term-encoding-always-on/egglog/tests/pointer-analysis-initdb), hardboiled_conv1d_32.egg, luminal-llama.egg, herbie.egg, misaal-hvx-dot-product.egg, churchroad-wide-multiply.egg, dialegg-nmm40.egg, speq-preserved-reference-suite.egg · 6 round(s) per endpoint/file · 120 s timeout per run · Report: /private/tmp/term-encoding-d60202f.jsonl*

## Summary — d60202f64424 term vs d60202f64424 off

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 1.61–1.63x | slower |
| Wall time | Lowest-ratio file | churchroad-wide-multiply.egg | 0.705–0.715x | faster |
| Wall time | Highest-ratio file | speq-preserved-reference-suite.egg | 3.56–3.61x | slower |
| Peak RSS | Lowest-ratio file | churchroad-wide-multiply.egg | 1.10–1.11x | higher RSS |
| Peak RSS | Highest-ratio file | pointer-analysis-initdb.egg | 3.59–3.65x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| math-microbenchmark-rational.egg | 393–412 ms | 825–836 ms | 2.01–2.11x | slower |
| eggcc-2mm-pass1.egg | 799–812 ms | 1.16–1.19 s | 1.43–1.48x | slower |
| pointer-analysis-initdb.egg | 57.1–58.4 ms | 132–137 ms | 2.27–2.37x | slower |
| hardboiled_conv1d_32.egg | 110–112 ms | 210–215 ms | 1.88–1.94x | slower |
| luminal-llama.egg | 355–363 ms | 1.23–1.23 s | 3.38–3.46x | slower |
| herbie.egg | 51.7–52.4 ms | 102–105 ms | 1.96–2.02x | slower |
| misaal-hvx-dot-product.egg | 33.2–33.9 ms | 99.3–103 ms | 2.95–3.07x | slower |
| churchroad-wide-multiply.egg | 1.00–1.02 s | 715–717 ms | 0.705–0.715x | faster |
| dialegg-nmm40.egg | 158–160 ms | 261–263 ms | 1.64–1.66x | slower |
| speq-preserved-reference-suite.egg | 45.7–46.0 ms | 163–165 ms | 3.56–3.61x | slower |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| math-microbenchmark-rational.egg | 287.1–287.3 MiB | 494.0–494.6 MiB | 1.72–1.72x | higher RSS |
| eggcc-2mm-pass1.egg | 109.4–110.8 MiB | 248.2–250.2 MiB | 2.25–2.28x | higher RSS |
| pointer-analysis-initdb.egg | 41.7–42.4 MiB | 152.1–152.7 MiB | 3.59–3.65x | higher RSS |
| hardboiled_conv1d_32.egg | 41.6–41.9 MiB | 68.1–68.6 MiB | 1.63–1.64x | higher RSS |
| luminal-llama.egg | 118.1–119.4 MiB | 256.4–259.8 MiB | 2.15–2.19x | higher RSS |
| herbie.egg | 19.9–20.1 MiB | 34.0–34.2 MiB | 1.69–1.71x | higher RSS |
| misaal-hvx-dot-product.egg | 31.7–31.9 MiB | 65.5–65.9 MiB | 2.06–2.07x | higher RSS |
| churchroad-wide-multiply.egg | 20.5–20.6 MiB | 22.6–22.8 MiB | 1.10–1.11x | higher RSS |
| dialegg-nmm40.egg | 30.6–30.8 MiB | 97.8–98.0 MiB | 3.17–3.20x | higher RSS |
| speq-preserved-reference-suite.egg | 16.8–17.1 MiB | 35.2–35.7 MiB | 2.07–2.11x | higher RSS |

## Slowdown decomposition

| File | Wall Δ | Typecheck | Frontend | Program | Equality | Commands | Residual |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Suite total | +1889 ms | +18.2%  +345 ms | +18.2%  +344 ms | ◆ +29.8%  +563 ms | +24.1%  +455 ms | +7.22%  +136 ms | +2.46%  +46.4 ms |
| math-microbenchmark-rational.egg | +428 ms | +0.369%  +1.58 ms | +0.387%  +1.65 ms | +35.5%  +152 ms | ◆ +60.6%  +259 ms | +2.76%  +11.8 ms | +0.397%  +1.70 ms |
| eggcc-2mm-pass1.egg | +368 ms | +18.0%  +66.2 ms | +18.9%  +69.4 ms | ◆ +29.4%  +108 ms | +22.7%  +83.4 ms | +9.37%  +34.5 ms | +1.68%  +6.18 ms |
| pointer-analysis-initdb.egg | +76.4 ms | +2.88%  +2.20 ms | +27.0%  +20.7 ms | +14.9%  +11.4 ms | ◆ +38.4%  +29.3 ms | +4.36%  +3.34 ms | +12.5%  +9.53 ms |
| hardboiled_conv1d_32.egg | +101 ms | +24.6%  +24.9 ms | +23.4%  +23.7 ms | ◆ +32.9%  +33.3 ms | +10.6%  +10.7 ms | +5.65%  +5.72 ms | +2.83%  +2.86 ms |
| luminal-llama.egg | +868 ms | +21.0%  +183 ms | +18.6%  +162 ms | ◆ +46.5%  +403 ms | +4.59%  +39.8 ms | +7.43%  +64.5 ms | +1.83%  +15.9 ms |
| herbie.egg | +51.6 ms | +15.4%  +7.96 ms | +17.7%  +9.12 ms | ◆ +26.6%  +13.7 ms | +22.4%  +11.5 ms | +14.8%  +7.62 ms | +3.23%  +1.67 ms |
| misaal-hvx-dot-product.egg | +67.4 ms | +45.1%  +30.4 ms | ◆ +45.5%  +30.7 ms | +1.07%  +0.724 ms | +2.81%  +1.90 ms | +0.702%  +0.473 ms | +4.86%  +3.28 ms |
| churchroad-wide-multiply.egg | -292 ms | -1.90%  +5.56 ms | -2.11%  +6.18 ms | ◆ +105%  -308 ms | -0.552%  +1.61 ms | -0.150%  +0.439 ms | -0.496%  +1.45 ms |
| dialegg-nmm40.egg | +103 ms | +11.1%  +11.4 ms | +9.85%  +10.1 ms | ◆ +57.9%  +59.5 ms | +16.3%  +16.8 ms | +2.71%  +2.78 ms | +2.11%  +2.17 ms |
| speq-preserved-reference-suite.egg | +118 ms | +9.95%  +11.8 ms | +9.13%  +10.8 ms | ◆ +74.5%  +88.2 ms | +0.660%  +0.782 ms | +4.37%  +5.18 ms | +1.41%  +1.67 ms |

*Each mechanism cell is its share of the wall-time slowdown followed by candidate − baseline mean time. Frontend includes parsing, other lowering, and declaration/install commands. Program rules includes every phase of source-origin rulesets except rebuild. Equality/rebuild combines encoded maintenance rulesets with native rebuild tails. Commands includes actions/input, checks, and other schedules. Shares may be negative or exceed 100% when mechanisms offset. ◆ and bold type mark each row's largest absolute share; contributions below 5% are dimmed and improvements are green in Rich and interactive reports. Signed values carry the same information without styling. Residual is wall time minus every recorded leaf; ! means an endpoint's mean residual is negative.*

### Optimization ceilings

| Hypothetical change | Time removed | Remaining wall Δ | Implied ratio |
| --- | ---: | ---: | ---: |
| Remove added typechecking time | +345 ms | +1545 ms | 1.51x |
| Remove added frontend/install time | +344 ms | +1545 ms | 1.51x |
| Remove added typechecking + frontend time | +689 ms | +1201 ms | 1.40x |
| Remove added Equality assembly time | +299 ms | +1590 ms | 1.52x |
| Remove added net Equality/rebuild time | +455 ms | +1434 ms | 1.47x |
| Remove added source-rule execution time | +563 ms | +1327 ms | 1.44x |
| Remove every added non-program mechanism | +1.28 s | +609 ms | 1.20x |
| Remove every recorded added mechanism | +1.84 s | +46.4 ms | 1.02x |

*Each row mechanically removes the named positive candidate − baseline timing deltas while holding every other measured mean fixed; candidate advantages are retained. Equality assembly removes only ruleset assembly, while net Equality/rebuild removes the whole positive Equality bucket. These are optimistic additive accounting bounds, not implementation predictions; point ratios have no confidence intervals and interactions can invalidate them. Residual is never removed.*

## Ruleset drivers

*Each panel unfolds the Program and Equality cells from the decomposition. Parent rows exactly match those cells and alone show wall share. Program children contain only source-rule Assembly, Search, Apply, Execution, and Merge; Equality children contain every encoded maintenance ruleset plus one global Native rebuild replaced row. ↳ marks children in every format. Zero children are hidden. Source children are ranked by absolute own-work Δ (top 5 plus an exact per-group Other); every nonzero maintenance child is shown. Important phases include every \|phase Δ\| ≥ max(1 ms, 10% of \|row Δ\|), always include the dominant phase (◆), and appear in Assembly, Search, Apply, Execution, Merge, Rebuild order; … marks omitted nonzero phases.*

### Ruleset drivers — math-microbenchmark-rational.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +152 ms | +35.5% | ◆ Apply +80.8 ms; Merge +69.9 ms; … |
| ↳ <default ruleset> | +152 ms |  | ◆ Apply +80.8 ms; Merge +69.9 ms; … |
| Equality/rebuild — net | +259 ms | +60.6% | ◆ Search +267 ms; Apply +57.6 ms; Merge +69.4 ms; Rebuild -135 ms; … |
| ↳ @rebuilding | +354 ms |  | ◆ Search +233 ms; Apply +57.2 ms; Merge +62.8 ms; … |
| ↳ @parent | +41.0 ms |  | ◆ Search +33.9 ms; Merge +6.60 ms; … |
| ↳ @rebuilding_cleanup | +855 ns |  | ◆ Assembly +855 ns |
| ↳ @subsume_ruleset | +209 ns |  | ◆ Assembly +209 ns |
| ↳ Native rebuild replaced | -135 ms |  | ◆ Rebuild -135 ms |

*Program + Equality account for +96.1% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — eggcc-2mm-pass1.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +108 ms | +29.4% | Assembly +11.1 ms; ◆ Search +54.5 ms; Apply +24.5 ms; Merge +17.7 ms; … |
| ↳ always-run | +82.2 ms |  | Assembly +8.52 ms; ◆ Search +43.2 ms; Apply +18.1 ms; Merge +12.0 ms; … |
| ↳ type-analysis | +7.08 ms |  | Search +1.53 ms; ◆ Apply +2.84 ms; Merge +2.39 ms; … |
| ↳ is-resolved | +4.99 ms |  | ◆ Search +4.01 ms; … |
| ↳ terms | +3.52 ms |  | ◆ Search +1.46 ms; … |
| ↳ terms-helpers | +3.48 ms |  | ◆ Search +1.86 ms; … |
| ↳ Other (23 more source rulesets) | +7.06 ms |  | Assembly +1.47 ms; ◆ Search +2.44 ms; Apply +1.35 ms; Merge +1.68 ms; … |
| Equality/rebuild — net | +83.4 ms | +22.7% | ◆ Assembly +245 ms; Search +55.5 ms; Execution +10.8 ms; Merge +10.6 ms; Rebuild -245 ms; … |
| ↳ @rebuilding | +277 ms |  | ◆ Assembly +201 ms; Search +50.1 ms; … |
| ↳ @parent | +48.6 ms |  | ◆ Assembly +41.6 ms; Search +5.31 ms; … |
| ↳ @subsume_ruleset | +2.78 ms |  | ◆ Assembly +2.68 ms; … |
| ↳ @rebuilding_cleanup | +65.8 us |  | ◆ Assembly +65.8 us |
| ↳ Native rebuild replaced | -245 ms |  | ◆ Rebuild -245 ms |

*Program + Equality account for +52.1% of this file's wall-time change. Source rules shown: 5/28 plus exact Other. Maintenance rules shown: 4/4.*

### Ruleset drivers — pointer-analysis-initdb.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +11.4 ms | +14.9% | Apply +3.88 ms; ◆ Merge +7.28 ms; … |
| ↳ <default ruleset> | +11.4 ms |  | Apply +3.88 ms; ◆ Merge +7.28 ms; … |
| Equality/rebuild — net | +29.3 ms | +38.4% | ◆ Search +19.9 ms; Apply +3.84 ms; Merge +9.41 ms; Rebuild -4.56 ms; … |
| ↳ @rebuilding | +18.9 ms |  | ◆ Search +12.7 ms; Apply +3.25 ms; Merge +2.63 ms; … |
| ↳ @parent | +15.0 ms |  | ◆ Search +7.19 ms; Merge +6.78 ms; … |
| ↳ @rebuilding_cleanup | +1.29 us |  | ◆ Assembly +1.29 us |
| ↳ @subsume_ruleset | +770 ns |  | ◆ Assembly +770 ns |
| ↳ Native rebuild replaced | -4.56 ms |  | ◆ Rebuild -4.56 ms |

*Program + Equality account for +53.3% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — hardboiled_conv1d_32.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +33.3 ms | +32.9% | ◆ Search +23.6 ms; Apply +4.44 ms; … |
| ↳ <default ruleset> | +31.8 ms |  | ◆ Search +23.6 ms; Apply +3.85 ms; … |
| ↳ typechecking | +967 us |  | ◆ Apply +590 us; … |
| ↳ amx | +497 us |  | ◆ Assembly +497 us |
| Equality/rebuild — net | +10.7 ms | +10.6% | Assembly +4.74 ms; ◆ Search +5.76 ms; Apply +2.32 ms; Rebuild -3.73 ms; … |
| ↳ @rebuilding | +12.4 ms |  | Assembly +3.87 ms; ◆ Search +4.82 ms; Apply +2.29 ms; … |
| ↳ @parent | +2.02 ms |  | ◆ Search +943 us; … |
| ↳ @subsume_ruleset | +21.1 us |  | ◆ Assembly +21.1 us |
| ↳ @rebuilding_cleanup | +2.68 us |  | ◆ Assembly +2.68 us |
| ↳ Native rebuild replaced | -3.73 ms |  | ◆ Rebuild -3.73 ms |

*Program + Equality account for +43.5% of this file's wall-time change. Source rules shown: 3/3. Maintenance rules shown: 4/4.*

### Ruleset drivers — luminal-llama.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +403 ms | +46.5% | Assembly +87.7 ms; ◆ Search +311 ms; … |
| ↳ fusion_grow | +169 ms |  | ◆ Search +168 ms; … |
| ↳ fusion_pair | +147 ms |  | ◆ Search +145 ms; … |
| ↳ direct_kernel | +36.3 ms |  | ◆ Search +36.1 ms; … |
| ↳ matmul_backend | +29.9 ms |  | ◆ Assembly +75.1 ms; Search -45.5 ms; … |
| ↳ fusion_merge | +14.7 ms |  | ◆ Search +14.2 ms; … |
| ↳ Other (11 more source rulesets) | +7.04 ms |  | ◆ Assembly +11.4 ms; Search -5.95 ms; … |
| Equality/rebuild — net | +39.8 ms | +4.59% | ◆ Assembly +42.3 ms; Rebuild -5.66 ms; … |
| ↳ @rebuilding | +44.7 ms |  | ◆ Assembly +41.6 ms; … |
| ↳ @parent | +565 us |  | ◆ Assembly +514 us; … |
| ↳ @subsume_ruleset | +217 us |  | ◆ Assembly +133 us; … |
| ↳ @rebuilding_cleanup | +3.66 us |  | ◆ Assembly +3.66 us |
| ↳ Native rebuild replaced | -5.66 ms |  | ◆ Rebuild -5.66 ms |

*Program + Equality account for +51.1% of this file's wall-time change. Source rules shown: 5/16 plus exact Other. Maintenance rules shown: 4/4.*

### Ruleset drivers — herbie.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +13.7 ms | +26.6% | ◆ Assembly +8.06 ms; Apply +3.05 ms; Merge +1.98 ms; … |
| ↳ <default ruleset> | +13.7 ms |  | ◆ Assembly +8.06 ms; Apply +3.05 ms; Merge +1.98 ms; … |
| Equality/rebuild — net | +11.5 ms | +22.4% | ◆ Search +8.05 ms; Apply +1.88 ms; Merge +2.25 ms; Rebuild -1.98 ms; … |
| ↳ @rebuilding | +11.3 ms |  | ◆ Search +6.58 ms; Apply +1.80 ms; Merge +1.76 ms; … |
| ↳ @parent | +2.20 ms |  | ◆ Search +1.47 ms; … |
| ↳ @rebuilding_cleanup | +2.40 us |  | ◆ Assembly +2.40 us |
| ↳ @subsume_ruleset | +1.55 us |  | ◆ Assembly +1.55 us |
| ↳ Native rebuild replaced | -1.98 ms |  | ◆ Rebuild -1.98 ms |

*Program + Equality account for +48.9% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — misaal-hvx-dot-product.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +724 us | +1.07% | ◆ Assembly +623 us; … |
| ↳ <default ruleset> | +724 us |  | ◆ Assembly +623 us; … |
| Equality/rebuild — net | +1.90 ms | +2.81% | ◆ Assembly +1.49 ms; … |
| ↳ @rebuilding | +2.03 ms |  | ◆ Assembly +1.48 ms; … |
| ↳ @parent | +48.1 us |  | ◆ Search +24.3 us; … |
| ↳ @rebuilding_cleanup | +230 ns |  | ◆ Assembly +230 ns |
| ↳ @subsume_ruleset | +90.2 ns |  | ◆ Assembly +90.2 ns |
| ↳ Native rebuild replaced | -180 us |  | ◆ Rebuild -180 us |

*Program + Equality account for +3.89% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — churchroad-wide-multiply.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | -308 ms | +105% | ◆ Search -309 ms; … |
| ↳ mapping | -309 ms |  | ◆ Search -309 ms; … |
| ↳ transform | +899 us |  | ◆ Apply +641 us; … |
| ↳ typing | +699 us |  | ◆ Apply +437 us; … |
| ↳ misc | +6.33 us |  | ◆ Assembly +6.33 us |
| Equality/rebuild — net | +1.61 ms | -0.552% | ◆ Assembly +1.21 ms; … |
| ↳ @rebuilding | +1.43 ms |  | ◆ Assembly +1.02 ms; … |
| ↳ @parent | +187 us |  | ◆ Assembly +178 us; … |
| ↳ @rebuilding_cleanup | +1.31 us |  | ◆ Assembly +1.31 us |
| ↳ @subsume_ruleset | +1.22 us |  | ◆ Assembly +1.22 us |

*Program + Equality account for +105% of this file's wall-time change. Source rules shown: 4/4. Maintenance rules shown: 4/4.*

### Ruleset drivers — dialegg-nmm40.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +59.5 ms | +57.9% | ◆ Apply +40.4 ms; Merge +22.8 ms; … |
| ↳ rules | +59.5 ms |  | ◆ Apply +40.4 ms; Merge +22.8 ms; … |
| Equality/rebuild — net | +16.8 ms | +16.3% | Assembly +1.73 ms; ◆ Search +15.4 ms; Apply +6.26 ms; Merge +4.05 ms; Rebuild -11.1 ms; … |
| ↳ @rebuilding | +26.9 ms |  | ◆ Search +14.6 ms; Apply +6.25 ms; Merge +3.95 ms; … |
| ↳ @parent | +950 us |  | ◆ Search +747 us; … |
| ↳ @rebuilding_cleanup | +701 ns |  | ◆ Assembly +701 ns |
| ↳ @subsume_ruleset | +334 ns |  | ◆ Assembly +334 ns |
| ↳ Native rebuild replaced | -11.1 ms |  | ◆ Rebuild -11.1 ms |

*Program + Equality account for +74.2% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — speq-preserved-reference-suite.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +88.2 ms | +74.5% | ◆ Assembly +71.8 ms; Search +9.67 ms; … |
| ↳ parseIR.transform-taco-spmv-csc | +27.8 ms |  | ◆ Assembly +19.7 ms; Search +4.84 ms; Execution +3.23 ms; … |
| ↳ parseIR.transform-csparse-spmv-csc-nostruct | +27.4 ms |  | ◆ Assembly +19.4 ms; Search +4.74 ms; Execution +3.20 ms; … |
| ↳ parseIR.transform-parboil-hist | +16.5 ms |  | ◆ Assembly +16.3 ms; … |
| ↳ parseIR.transform-npb-is-hist | +16.3 ms |  | ◆ Assembly +16.2 ms; … |
| ↳ parseIR.expand-parboil-hist | +49.8 us |  | ◆ Assembly +25.3 us; … |
| ↳ Other (3 more source rulesets) | +117 us |  | ◆ Assembly +73.8 us; … |
| Equality/rebuild — net | +782 us | +0.660% | ◆ Assembly +478 us; … |
| ↳ @rebuilding | +783 us |  | ◆ Assembly +440 us; … |
| ↳ @parent | +53.3 us |  | ◆ Assembly +35.5 us; … |
| ↳ @subsume_ruleset | +1.27 us |  | ◆ Assembly +1.27 us |
| ↳ @rebuilding_cleanup | +1.26 us |  | ◆ Assembly +1.26 us |
| ↳ Native rebuild replaced | -56.5 us |  | ◆ Rebuild -56.5 us |

*Program + Equality account for +75.1% of this file's wall-time change. Source rules shown: 5/8 plus exact Other. Maintenance rules shown: 4/4.*
