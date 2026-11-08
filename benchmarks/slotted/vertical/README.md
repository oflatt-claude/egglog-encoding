# SDQL vertical fusion

This probe uses all five **unmodified second-phase inputs** from the slotted
paper's SDQL artifact, pinned at `83f2e5bee2b3aa45bf97ef1e3a8abe953790c735`.
The input files and published baseline extractions are in
[the SDQL fixture directory](../../reproduction/slotted/fixtures/sdql/README.md).
It isolates three rules, rather than reproducing the full 44-rule experiment.

```sh
./bench.py sdql-vertical --output-dir /tmp/sdql-vertical \
  --rounds 10 --rewrite-rounds 64 --cpu 16
```

`--kernels` selects from `mmm_sum mttkrp mmm ttm batax`. `--target` selects the
optimizer checkout. `--report` selects the shared runner's JSONL cache; its default
is `OUTPUT/optimizer.jsonl`. Status goes to stderr; result JSON goes to stdout.

## Rules and extraction

[rules.egg](rules.egg) contains the artifact's key-preserving and unique-key
vertical-fusion rules and beta reduction. The tests compare
these rules with the existing SDQL rule library. Schematically, fusion replaces

```text
Sum(Sum(R, k, v, {key: producer}), x, y, consumer)
```

with one scan of `R` whose body is `let x = key in let y = producer in consumer`.
The producer must preserve its input key or carry the artifact's `Unique`
annotation; arbitrary grouping cannot be fused this way. Beta reduction performs
capture-avoiding substitution through nested binders.

`Unique` stays intact during optimization. Equating `Unique(x)` with `x` lets a
uniqueness marker justify fusion at other occurrences, including ones with
colliding keys. The frozen regression includes an independently valid annotation
and a non-injective value-keyed producer in the same egraph. The interpreter
treats the retained marker as a runtime identity.

[debruijn.egg](debruijn.egg) is the ordinary control. `Sum` binds key at index 1
and value at index 0. Its fusion rule shifts the consumer's free variables by two
and the producer's value by one when introducing the two `Let`s. `Shift` and
`Subst` remain active so later body alternatives can be processed. These files
are rule sources, not generated copies requiring a separate rule generator.

Both extractors minimize source AST size: constructors and variable occurrences
cost one, binder declarations and primitive payloads cost zero. Ordinary payload
constructors therefore have zero head cost to compensate for its extractor's
primitive cost. Unresolved scope helpers and escaping variables are rejected.
This cost does not model materialization, loop frequency or DAG sharing.

## Measurements and checks

Each encoding runs with and without vertical fusion. The shared runner collects
optimizer process time and peak RSS. Untimed runs extract programs, export graph
sizes and measure native peak RSS through GNU `/usr/bin/time`, avoiding an
inherited Python-launcher RSS floor. That native RSS value is one observation.
Logical counts omit implementation machinery and explicit scope helpers;
serialized counts include both. The substitution strategies differ (slotted
uses representatives; ordinary rewriting explores alternatives), so these graphs
are not claimed to be isomorphic or to isolate alpha-equivalence alone.

The exact interpreter checks each selected program, the original first/second
phase inputs, and the published baseline extraction against independent dense
formulas. It uses 15 generated sparse cases per kernel, including empty inputs,
negative values and fractions. CSR/CSF arrays use one-based indices; pointer
sentinels are accessible to `Get` but excluded from CSR row iteration.
Singleton-construction and loop counts on size-four cases are diagnostics, not
compiled execution timings. Published targets never seed optimization.

`result.json` records source/binary hashes, selections, graph sizes, measurements
and correctness diagnostics. `*-selected.sexp` contains the readable extracted
programs. Results stay outside the repository. Rust tests consume the frozen
`checks-*.egg` files, covering the actual TTM input, delayed substitution updates,
shadowing and rejection of fusion across colliding dictionary keys.
