# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | d60202f644249ef565de0ca7c51871fe497440a2 | d60202f64424 | off |
| Candidate | d60202f644249ef565de0ca7c51871fe497440a2 | d60202f64424 | term |

*10 file(s): math-microbenchmark-rational.egg, eggcc-2mm-pass1.egg, pointer-analysis-initdb.egg (facts: /Users/saul/p/wt/egglog-encoding/term-encoding-always-on/egglog/tests/pointer-analysis-initdb), hardboiled_conv1d_32.egg, luminal-llama.egg, herbie.egg, misaal-hvx-dot-product.egg, churchroad-wide-multiply.egg, dialegg-nmm40.egg, speq-preserved-reference-suite.egg · 6 round(s) per endpoint/file · 120 s timeout per run · Report: /private/tmp/term-encoding-d60202f.jsonl*

## Summary — d60202f644249ef565de0ca7c51871fe497440a2 term vs d60202f644249ef565de0ca7c51871fe497440a2 off

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 1.62–1.64x | slower |
| Wall time | Lowest-ratio file | churchroad-wide-multiply.egg | 0.708–0.720x | faster |
| Wall time | Highest-ratio file | speq-preserved-reference-suite.egg | 3.55–3.65x | slower |
| Peak RSS | Lowest-ratio file | churchroad-wide-multiply.egg | 1.11–1.13x | higher RSS |
| Peak RSS | Highest-ratio file | pointer-analysis-initdb.egg | 3.78–3.80x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| math-microbenchmark-rational.egg | 413–431 ms | 844–865 ms | 1.98–2.08x | slower |
| eggcc-2mm-pass1.egg | 819–824 ms | 1.19–1.21 s | 1.45–1.48x | slower |
| pointer-analysis-initdb.egg | 58.0–59.8 ms | 135–137 ms | 2.27–2.35x | slower |
| hardboiled_conv1d_32.egg | 112–113 ms | 215–218 ms | 1.91–1.95x | slower |
| luminal-llama.egg | 363–366 ms | 1.24–1.25 s | 3.39–3.43x | slower |
| herbie.egg | 52.7–54.3 ms | 105–108 ms | 1.95–2.03x | slower |
| misaal-hvx-dot-product.egg | 33.9–34.5 ms | 102–104 ms | 2.97–3.05x | slower |
| churchroad-wide-multiply.egg | 1.00–1.01 s | 714–724 ms | 0.708–0.720x | faster |
| dialegg-nmm40.egg | 158–165 ms | 263–270 ms | 1.61–1.69x | slower |
| speq-preserved-reference-suite.egg | 46.6–47.6 ms | 168–171 ms | 3.55–3.65x | slower |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| math-microbenchmark-rational.egg | 287.4–287.6 MiB | 470.3–470.5 MiB | 1.64–1.64x | higher RSS |
| eggcc-2mm-pass1.egg | 106.6–110.5 MiB | 242.9–248.6 MiB | 2.22–2.31x | higher RSS |
| pointer-analysis-initdb.egg | 40.2–40.3 MiB | 152.2–152.7 MiB | 3.78–3.80x | higher RSS |
| hardboiled_conv1d_32.egg | 41.4–41.8 MiB | 68.0–68.3 MiB | 1.63–1.65x | higher RSS |
| luminal-llama.egg | 117.1–119.9 MiB | 258.4–261.0 MiB | 2.16–2.22x | higher RSS |
| herbie.egg | 20.0–20.1 MiB | 33.7–33.9 MiB | 1.68–1.69x | higher RSS |
| misaal-hvx-dot-product.egg | 31.5–32.1 MiB | 64.9–66.2 MiB | 2.03–2.09x | higher RSS |
| churchroad-wide-multiply.egg | 20.1–20.5 MiB | 22.6–22.8 MiB | 1.11–1.13x | higher RSS |
| dialegg-nmm40.egg | 30.7–31.0 MiB | 98.1–98.3 MiB | 3.17–3.20x | higher RSS |
| speq-preserved-reference-suite.egg | 16.7–17.1 MiB | 35.2–35.4 MiB | 2.07–2.11x | higher RSS |

## Slowdown decomposition

| File | Wall Δ | Typecheck | Frontend | Program | Equality | Commands | Residual |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Suite total (10 files) | +1935 ms | +18.1%  +350 ms | +17.9%  +346 ms | ◆ +29.7%  +575 ms | +24.6%  +476 ms | +7.12%  +138 ms | +2.60%  +50.3 ms |
| math-microbenchmark-rational.egg | +433 ms | +0.385%  +1.66 ms | +0.417%  +1.80 ms | +33.6%  +145 ms | ◆ +62.5%  +270 ms | +2.64%  +11.4 ms | +0.464%  +2.01 ms |
| eggcc-2mm-pass1.egg | +380 ms | +17.9%  +68.2 ms | +18.6%  +70.7 ms | ◆ +29.8%  +113 ms | +22.7%  +86.3 ms | +9.15%  +34.8 ms | +1.80%  +6.84 ms |
| pointer-analysis-initdb.egg | +77.3 ms | +2.90%  +2.25 ms | +26.9%  +20.8 ms | +14.8%  +11.4 ms | ◆ +38.7%  +29.9 ms | +3.66%  +2.83 ms | +13.0%  +10.1 ms |
| hardboiled_conv1d_32.egg | +104 ms | +24.2%  +25.2 ms | +23.1%  +24.1 ms | ◆ +33.2%  +34.7 ms | +10.8%  +11.3 ms | +5.77%  +6.02 ms | +2.83%  +2.96 ms |
| luminal-llama.egg | +879 ms | +21.0%  +185 ms | +18.1%  +159 ms | ◆ +46.4%  +408 ms | +5.10%  +44.8 ms | +7.40%  +65.1 ms | +2.01%  +17.7 ms |
| herbie.egg | +53.0 ms | +15.3%  +8.11 ms | +17.5%  +9.29 ms | ◆ +26.6%  +14.1 ms | +22.3%  +11.8 ms | +15.4%  +8.16 ms | +2.86%  +1.52 ms |
| misaal-hvx-dot-product.egg | +68.6 ms | +44.6%  +30.6 ms | ◆ +45.7%  +31.4 ms | +1.16%  +0.794 ms | +2.90%  +1.99 ms | +0.709%  +0.487 ms | +4.93%  +3.39 ms |
| churchroad-wide-multiply.egg | -288 ms | -1.97%  +5.67 ms | -2.21%  +6.36 ms | ◆ +105%  -303 ms | -0.606%  +1.74 ms | -0.163%  +0.469 ms | -0.496%  +1.43 ms |
| dialegg-nmm40.egg | +105 ms | +11.0%  +11.5 ms | +9.93%  +10.4 ms | ◆ +57.8%  +60.5 ms | +16.3%  +17.1 ms | +2.75%  +2.88 ms | +2.20%  +2.30 ms |
| speq-preserved-reference-suite.egg | +122 ms | +9.89%  +12.1 ms | +9.27%  +11.3 ms | ◆ +73.9%  +90.4 ms | +0.691%  +0.846 ms | +4.52%  +5.52 ms | +1.76%  +2.15 ms |

*The Suite total row sums each selected file's candidate − baseline mean; file rows are per-file mean deltas. Each mechanism cell is its share of that row's wall-time change followed by its signed mean time change. Frontend includes parsing, other lowering, and declaration/install commands. Program rules includes every phase of source-origin rulesets except rebuild. Equality/rebuild combines encoded maintenance rulesets with native rebuild tails. Commands includes actions/input, checks, and other schedules. Shares may be negative or exceed 100% when mechanisms offset. ◆ and bold type mark each row's largest absolute share; contributions below 5% are dimmed and improvements are green in Rich and interactive reports. Signed values carry the same information without styling. Residual is wall time minus every recorded leaf; ! means an endpoint's mean residual is negative.*

## Ruleset drivers

*Each panel unfolds the Program and Equality cells from the decomposition. Parent rows exactly match those cells and alone show wall share. Program children contain only source-rule Assembly, Search, Apply, Execution, and Merge; Equality children contain every encoded maintenance ruleset plus one global Native rebuild replaced row. ↳ marks children in every format. Zero children are hidden. Source children are ranked by absolute own-work Δ (top 5 plus an exact per-group Other); every nonzero maintenance child is shown. Important phases include every \|phase Δ\| ≥ max(1 ms, 10% of \|row Δ\|), always include the dominant phase (◆), and appear in Assembly, Search, Apply, Execution, Merge, Rebuild order; … marks omitted nonzero phases.*

### Ruleset drivers — math-microbenchmark-rational.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +145 ms | +33.6% | ◆ Apply +73.1 ms; Merge +71.1 ms; … |
| ↳ <default ruleset> | +145 ms |  | ◆ Apply +73.1 ms; Merge +71.1 ms; … |
| Equality/rebuild — net | +270 ms | +62.5% | ◆ Search +280 ms; Apply +59.9 ms; Merge +72.1 ms; Rebuild -142 ms; … |
| ↳ @rebuilding | +371 ms |  | ◆ Search +246 ms; Apply +59.4 ms; Merge +65.3 ms; … |
| ↳ @parent | +41.2 ms |  | ◆ Search +33.8 ms; Merge +6.83 ms; … |
| ↳ @rebuilding_cleanup | +908 ns |  | ◆ Assembly +908 ns |
| ↳ @subsume_ruleset | +223 ns |  | ◆ Assembly +223 ns |
| ↳ Native rebuild replaced | -142 ms |  | ◆ Rebuild -142 ms |

*Program + Equality account for +96.1% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — eggcc-2mm-pass1.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +113 ms | +29.8% | Assembly +11.6 ms; ◆ Search +56.8 ms; Apply +25.5 ms; Merge +18.8 ms; … |
| ↳ always-run | +85.6 ms |  | Assembly +8.73 ms; ◆ Search +44.5 ms; Apply +19.1 ms; Merge +12.9 ms; … |
| ↳ type-analysis | +8.36 ms |  | Search +2.43 ms; ◆ Apply +2.93 ms; Merge +2.47 ms; … |
| ↳ is-resolved | +5.00 ms |  | ◆ Search +4.02 ms; … |
| ↳ terms | +3.65 ms |  | ◆ Search +1.46 ms; … |
| ↳ terms-helpers | +3.61 ms |  | ◆ Search +1.90 ms; … |
| ↳ Other (23 more source rulesets) | +7.11 ms |  | Assembly +1.49 ms; ◆ Search +2.46 ms; Apply +1.34 ms; Merge +1.73 ms; … |
| Equality/rebuild — net | +86.3 ms | +22.7% | ◆ Assembly +248 ms; Search +57.6 ms; Execution +11.4 ms; Merge +11.2 ms; Rebuild -247 ms; … |
| ↳ @rebuilding | +282 ms |  | ◆ Assembly +203 ms; Search +52.0 ms; … |
| ↳ @parent | +49.3 ms |  | ◆ Assembly +42.0 ms; Search +5.56 ms; … |
| ↳ @subsume_ruleset | +2.83 ms |  | ◆ Assembly +2.73 ms; … |
| ↳ @rebuilding_cleanup | +67.2 us |  | ◆ Assembly +67.2 us |
| ↳ Native rebuild replaced | -247 ms |  | ◆ Rebuild -247 ms |

*Program + Equality account for +52.5% of this file's wall-time change. Source rules shown: 5/28 plus exact Other. Maintenance rules shown: 4/4.*

### Ruleset drivers — pointer-analysis-initdb.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +11.4 ms | +14.8% | Apply +3.91 ms; ◆ Merge +7.45 ms; … |
| ↳ <default ruleset> | +11.4 ms |  | Apply +3.91 ms; ◆ Merge +7.45 ms; … |
| Equality/rebuild — net | +29.9 ms | +38.7% | ◆ Search +20.2 ms; Apply +3.89 ms; Merge +9.65 ms; Rebuild -4.66 ms; … |
| ↳ @rebuilding | +19.2 ms |  | ◆ Search +12.8 ms; Apply +3.29 ms; Merge +2.69 ms; … |
| ↳ @parent | +15.4 ms |  | ◆ Search +7.39 ms; Merge +6.96 ms; … |
| ↳ @rebuilding_cleanup | +1.19 us |  | ◆ Assembly +1.19 us |
| ↳ @subsume_ruleset | +785 ns |  | ◆ Assembly +785 ns |
| ↳ Native rebuild replaced | -4.66 ms |  | ◆ Rebuild -4.66 ms |

*Program + Equality account for +53.4% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — hardboiled_conv1d_32.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +34.7 ms | +33.2% | ◆ Search +24.2 ms; Apply +4.64 ms; … |
| ↳ <default ruleset> | +33.1 ms |  | ◆ Search +24.2 ms; Apply +4.02 ms; … |
| ↳ typechecking | +1.06 ms |  | ◆ Apply +616 us; … |
| ↳ amx | +531 us |  | ◆ Assembly +531 us |
| Equality/rebuild — net | +11.3 ms | +10.8% | Assembly +4.99 ms; ◆ Search +5.96 ms; Apply +2.38 ms; Rebuild -3.75 ms; … |
| ↳ @rebuilding | +12.9 ms |  | Assembly +4.07 ms; ◆ Search +4.97 ms; Apply +2.34 ms; … |
| ↳ @parent | +2.12 ms |  | ◆ Search +984 us; … |
| ↳ @subsume_ruleset | +22.1 us |  | ◆ Assembly +22.1 us |
| ↳ @rebuilding_cleanup | +2.88 us |  | ◆ Assembly +2.88 us |
| ↳ Native rebuild replaced | -3.75 ms |  | ◆ Rebuild -3.75 ms |

*Program + Equality account for +44.1% of this file's wall-time change. Source rules shown: 3/3. Maintenance rules shown: 4/4.*

### Ruleset drivers — luminal-llama.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +408 ms | +46.4% | Assembly +89.0 ms; ◆ Search +314 ms; … |
| ↳ fusion_grow | +170 ms |  | ◆ Search +168 ms; … |
| ↳ fusion_pair | +148 ms |  | ◆ Search +146 ms; … |
| ↳ direct_kernel | +36.9 ms |  | ◆ Search +36.7 ms; … |
| ↳ matmul_backend | +30.5 ms |  | ◆ Assembly +76.1 ms; Search -45.9 ms; … |
| ↳ fusion_merge | +14.9 ms |  | ◆ Search +14.3 ms; … |
| ↳ Other (11 more source rulesets) | +7.62 ms |  | ◆ Assembly +11.8 ms; Search -5.93 ms; … |
| Equality/rebuild — net | +44.8 ms | +5.10% | ◆ Assembly +47.3 ms; Rebuild -5.74 ms; … |
| ↳ @rebuilding | +49.7 ms |  | ◆ Assembly +46.5 ms; … |
| ↳ @parent | +627 us |  | ◆ Assembly +574 us; … |
| ↳ @subsume_ruleset | +238 us |  | ◆ Assembly +147 us; … |
| ↳ @rebuilding_cleanup | +3.58 us |  | ◆ Assembly +3.58 us |
| ↳ Native rebuild replaced | -5.74 ms |  | ◆ Rebuild -5.74 ms |

*Program + Equality account for +51.5% of this file's wall-time change. Source rules shown: 5/16 plus exact Other. Maintenance rules shown: 4/4.*

### Ruleset drivers — herbie.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +14.1 ms | +26.6% | ◆ Assembly +8.33 ms; Apply +3.13 ms; Merge +2.02 ms; … |
| ↳ <default ruleset> | +14.1 ms |  | ◆ Assembly +8.33 ms; Apply +3.13 ms; Merge +2.02 ms; … |
| Equality/rebuild — net | +11.8 ms | +22.3% | ◆ Search +8.17 ms; Apply +1.92 ms; Merge +2.32 ms; Rebuild -2.01 ms; … |
| ↳ @rebuilding | +11.6 ms |  | ◆ Search +6.68 ms; Apply +1.83 ms; Merge +1.82 ms; … |
| ↳ @parent | +2.24 ms |  | ◆ Search +1.49 ms; … |
| ↳ @rebuilding_cleanup | +2.48 us |  | ◆ Assembly +2.48 us |
| ↳ @subsume_ruleset | +1.60 us |  | ◆ Assembly +1.60 us |
| ↳ Native rebuild replaced | -2.01 ms |  | ◆ Rebuild -2.01 ms |

*Program + Equality account for +48.9% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — misaal-hvx-dot-product.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +794 us | +1.16% | ◆ Assembly +675 us; … |
| ↳ <default ruleset> | +794 us |  | ◆ Assembly +675 us; … |
| Equality/rebuild — net | +1.99 ms | +2.90% | ◆ Assembly +1.57 ms; … |
| ↳ @rebuilding | +2.13 ms |  | ◆ Assembly +1.56 ms; … |
| ↳ @parent | +48.8 us |  | ◆ Search +25.0 us; … |
| ↳ @rebuilding_cleanup | +223 ns |  | ◆ Assembly +223 ns |
| ↳ @subsume_ruleset | +180 ns |  | ◆ Assembly +180 ns |
| ↳ Native rebuild replaced | -185 us |  | ◆ Rebuild -185 us |

*Program + Equality account for +4.06% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — churchroad-wide-multiply.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | -303 ms | +105% | ◆ Search -305 ms; … |
| ↳ mapping | -305 ms |  | ◆ Search -305 ms; … |
| ↳ transform | +923 us |  | ◆ Apply +668 us; … |
| ↳ typing | +741 us |  | ◆ Apply +466 us; … |
| ↳ misc | +7.69 us |  | ◆ Assembly +7.69 us |
| Equality/rebuild — net | +1.74 ms | -0.606% | ◆ Assembly +1.30 ms; … |
| ↳ @rebuilding | +1.53 ms |  | ◆ Assembly +1.09 ms; … |
| ↳ @parent | +213 us |  | ◆ Assembly +203 us; … |
| ↳ @rebuilding_cleanup | +1.48 us |  | ◆ Assembly +1.48 us |
| ↳ @subsume_ruleset | +1.10 us |  | ◆ Assembly +1.10 us |

*Program + Equality account for +105% of this file's wall-time change. Source rules shown: 4/4. Maintenance rules shown: 4/4.*

### Ruleset drivers — dialegg-nmm40.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +60.5 ms | +57.8% | ◆ Apply +40.8 ms; Merge +23.5 ms; … |
| ↳ rules | +60.5 ms |  | ◆ Apply +40.8 ms; Merge +23.5 ms; … |
| Equality/rebuild — net | +17.1 ms | +16.3% | Assembly +1.93 ms; ◆ Search +15.6 ms; Apply +6.35 ms; Merge +4.13 ms; Rebuild -11.4 ms; … |
| ↳ @rebuilding | +27.5 ms |  | ◆ Search +14.9 ms; Apply +6.33 ms; Merge +4.03 ms; … |
| ↳ @parent | +996 us |  | ◆ Search +776 us; … |
| ↳ @rebuilding_cleanup | +784 ns |  | ◆ Assembly +784 ns |
| ↳ @subsume_ruleset | +319 ns |  | ◆ Assembly +319 ns |
| ↳ Native rebuild replaced | -11.4 ms |  | ◆ Rebuild -11.4 ms |

*Program + Equality account for +74.1% of this file's wall-time change. Source rules shown: 1/1. Maintenance rules shown: 4/4.*

### Ruleset drivers — speq-preserved-reference-suite.egg

| Driver | Δ | Wall share | Important phase changes |
| --- | ---: | ---: | --- |
| Program rules — own work | +90.4 ms | +73.9% | ◆ Assembly +73.5 ms; Search +9.92 ms; … |
| ↳ parseIR.transform-taco-spmv-csc | +28.5 ms |  | ◆ Assembly +20.2 ms; Search +4.92 ms; Execution +3.28 ms; … |
| ↳ parseIR.transform-csparse-spmv-csc-nostruct | +28.1 ms |  | ◆ Assembly +19.9 ms; Search +4.88 ms; Execution +3.26 ms; … |
| ↳ parseIR.transform-parboil-hist | +17.0 ms |  | ◆ Assembly +16.7 ms; … |
| ↳ parseIR.transform-npb-is-hist | +16.7 ms |  | ◆ Assembly +16.6 ms; … |
| ↳ parseIR.expand-parboil-hist | +52.7 us |  | ◆ Assembly +29.4 us; … |
| ↳ Other (3 more source rulesets) | +132 us |  | ◆ Assembly +81.7 us; … |
| Equality/rebuild — net | +846 us | +0.691% | ◆ Assembly +520 us; … |
| ↳ @rebuilding | +844 us |  | ◆ Assembly +477 us; … |
| ↳ @parent | +59.9 us |  | ◆ Assembly +41.1 us; … |
| ↳ @rebuilding_cleanup | +1.27 us |  | ◆ Assembly +1.27 us |
| ↳ @subsume_ruleset | +1.10 us |  | ◆ Assembly +1.10 us |
| ↳ Native rebuild replaced | -61.0 us |  | ◆ Rebuild -61.0 us |

*Program + Equality account for +74.6% of this file's wall-time change. Source rules shown: 5/8 plus exact Other. Maintenance rules shown: 4/4.*
