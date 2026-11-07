Scope-aware covariance kernels
==============================

These follow-up probes use the pinned LMFAO Favorita covariance workload.
They isolate hoisting and multi-output fusion over prepared join bags. They are
not end-to-end comparisons with LMFAO, which already performs these optimizations.

  ./bench.py lmfao-hoist --case fusion \
    --data /tmp/LMFAO/data/favorita-small --output-dir /tmp/lmfao-fusion \
    --rounds 10 --inner-repeats 100 --cpu 16

--case hoist (the default) runs q20: SUM(unit_sales * oilprize). Its source is:

  Sum(oil rows, oil,
    Sum(other five relations joined on oil.date, sale,
      oil.oilprize * sale.unit_sales))

rules.egg moves an independent factor outside the inner sum, using ScaleSum
for factor * Sum(rows, binder, body). Ordinary egglog uses stable names and the
free-variable analysis in free-vars.egg; this rule does not introduce binders.

--case fusion runs all ten ungrouped queries from the pinned frontend export:
count; sums and squares of unit_sales, oilprize and transactions; and their three
pairwise products. Each query starts with its own oil and sale binders. Scalar
frontend functions become lambda applications. fusion.egg adds these rules:

  App(Lambda(x, body), value) = body[x := value]
  Pair(Sum(rows, x, a), Sum(rows, y, b))
    = Sum(rows, z, Pair(a[x := z], b[y := z]))

The fusion rule matches both sums and their parent Pair in a common slot frame,
then binds that slot in one sum. Slotted matching aligns their bodies directly;
beta reduction performs substitution when inlining scalar functions. Hoisting
remains available. The ordinary control uses de Bruijn indices with explicit
Shift and Subst rewrites (debruijn.egg), including binder-depth changes during
hoisting.
Resolved scope helpers are subsumed to avoid redundant rewriting. Fusion aligns
its two bodies directly because both use index zero. Both encodings also run
with fusion disabled to isolate the effect of that rule.

Both use the existing minimum-AST-size extractor. This favors fewer Sum nodes;
it is not a general runtime model. No optimized target seeds search. Conversion
to de Bruijn indices happens before optimization; post-extraction renaming only
compares outputs and names C++ locals. Unresolved Shift/Subst terms are rejected.

Preparation loads the six original relations, materializes the five-relation
sales bag and indexes it by date. Duplicate rows and separate oil rows are
retained, including oil rows with empty bags. Decimal SQL aggregates independently
check every output. Code generation emits the selected loops and scalar calls;
it does not fuse or hoist them. The C++ harness checks answers (rtol=1e-9,
atol=1e-7), warms up and times repeated executions. Identical C++ shares build
and execution samples; process order rotates/reverses across samples. Preparation,
data loading, checking and compilation are outside kernel timing.

--target selects the optimizer checkout through the shared benchmark runner.
--report selects its append-only JSONL cache (default OUTPUT/optimizer.jsonl).
Optimizer process time includes parsing, graph construction, rewriting and
extraction, with budgets of 16 rounds for hoist and 64 for fusion. Peak RSS is
measured on those processes. Cached wait4 RSS can include the launcher's footprint
at fork. A separate extraction run through GNU /usr/bin/time records
fresh_exec_max_rss_bytes, with that launcher overhead removed. This is a single
memory observation, outside the timing samples. Graph export is also untimed:

- source_nodes/classes count source-language constructors and variables, omitting
  ordinary Shift/Subst helpers and slotted implementation machinery;
- explicit_scope_helper_nodes counts ordinary Shift/Subst nodes separately,
  including retained subsumed rows;
- serialized_nodes/classes include all serialized implementation functions,
  relations and primitive values, including subsumed rows. Truncated exports
  fail the diagnostic.

These are encoding comparisons, not graph-isomorphism results. Slotted's built-in
substitution uses an extracted representative; ordinary Subst rewrites explore
alternatives explicitly. Their closures can differ. Logical graph compactness
alone does not establish lower memory use: consult whole-process peak RSS and
the implementation counts too.

result.json records selected expressions, timings, memory, graph counts, data
and binary hashes, and execution samples. Status goes to stderr; JSON goes to
stdout. Results remain generated artifacts, outside the source tree.
