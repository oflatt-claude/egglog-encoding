Scope-aware hoisting probe
=========================

This follow-up isolates partial-product hoisting from LMFAO section 3.5 using
q20 of the pinned Favorita covariance workload: SUM(unit_sales * oilprize).
It is a kernel experiment, not a replacement for LMFAO's multi-output optimizer
or an end-to-end LMFAO performance comparison. Upstream already performs this
kind of hoisting.

  Sum(oil rows, oil,
    Sum(other five relations joined on oil.date, sale,
      oil.oilprize * sale.unit_sales))

The multipattern rule in rules.egg recognizes the sum and its product, requires
that the factor is independent of the inner binder, and constructs ScaleSum:
factor * Sum(rows, binder, body). The binder scopes only over body; factor and
rows remain outside it. This explicit operator fuses scale and reduction. The
existing minimum-AST-size extractor favors it over separate Sum and Mul nodes;
we do not claim that AST size predicts general loop runtime.

Both treatments use that rule. Ordinary egglog represents binder names as data
and computes free-variable sets inside the egraph using free-vars.egg. Stable
input names suffice here because hoisting neither introduces binders nor changes
which binder a surviving variable refers to. Slotted supplies its built-in scope
machinery. Post-extraction alpha-normalization only compares outputs and names
C++ locals; it does not affect either search. No optimized target seeds search.

Run from the repository root:

  ./bench.py lmfao-hoist --data /tmp/LMFAO/data/favorita-small \
    --output-dir /tmp/lmfao-hoist --rounds 10 --inner-repeats 100 --cpu 16

--target selects a checkout to build through the shared benchmark runner.
Optimizer process timings include parsing, graph construction, 16 rewrite rounds
and extraction. --report selects its append-only JSONL cache; by default it is
OUTPUT/optimizer.jsonl. Status goes to stderr and result JSON to stdout.

Preparation reads the six original relations with the existing pinned-data
loader, materializes the five-relation sales bag, and indexes it by date. It
retains duplicate rows and separate oil rows, including dates with empty bags.
A decimal aggregate over the joined bags is the independent expected answer.
This preparation is outside the kernel measurements and is reported separately.

Code generation translates the extracted expression directly, without moving
arithmetic. The C++ harness validates the answer, warms up, and measures repeated
query executions over those prepared bags. It uses the same compiler flags for
the unhoisted input and both extracted programs. Identical C++ shares compilation
and execution samples. Process order rotates/reverses across samples; loading,
checking, compilation and bag preparation are excluded from kernel timings.
Floating answers use the existing rtol=1e-9 and atol=1e-7 bounds.

result.json records selected expressions, optimizer observations, execution
samples, compilation time, data/binary hashes and timing scope. Its comparison
can establish whether these two encodings choose different kernels. It cannot
establish an execution improvement over the original LMFAO backend.
