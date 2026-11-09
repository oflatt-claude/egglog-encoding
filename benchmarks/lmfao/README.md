# LMFAO covariance case study

This uses an egraph to optimize all of LMFAO's aggregate queries together. A DAG
extractor chooses which views to compute and share between queries. The workload
is the artifact's 140 covariance queries over six
Favorita relations: counts, sums, squares and pairwise products, with categorical
features as grouping keys. We run the public fragment with 2,000,000 Sales rows.
This reproduces the workload and compiler pipeline, not the paper's full
127M-row experiment or model training.

```text
LMFAO query generation
  → original logical optimizer OR egraph + DAG extraction
  → LMFAO views → upstream grouping/code generation → C++ execution
```

## Rules and extraction

[`logical.egg`](logical.egg) is the single handwritten rule source.
[`program.py`](../../benchmarking/lmfao/program.py) reads LMFAO's frontend export
and translates each query into nested bag sums for the six roots of its supplied
join tree. It supplies schema metadata and unoptimized traversals, never selected
views. Arbitrary join trees are outside the search space.

The rules optimize those sums and lower them to executable views:

- **Hoisting** moves a factor out of a sum when it does not depend on the bound
  row. **Loop interchange** exchanges independent sums. This lets a query
  aggregate a child table before joining it, while preserving duplicate rows.
- **Tuple fusion** combines sums over the same rows. Multipatterns find
  compatible reductions across queries and intermediate results; fused bodies
  derive columns of a common `SharedView`.
- **Lowering** translates local scalar functions, grouping keys and already
  derived child views into views that LMFAO can execute. Schema masks and function
  vectors are evaluated by rules too.

For example, the fusion rule matches both reductions in a tuple:

```lisp
(rewrite pair (Reduce rows $row (Tuple a b)) :name "scoped-fuse"
  :when ((= pair (Tuple left right))
         (= left (Reduce rows $row a)) (= right (Reduce rows $row b))))
```

Slotted egglog handles binding and alpha-equivalence. The ordinary egglog control
uses de Bruijn indices, explicit shift/swap rules and free-variable analyses,
with the same query alternatives, transformations and rewrite budget.

The Rust [`lmfao-extract`](src/lib.rs) crate reads executable alternatives directly
from the live egraph. Its HiGHS-backed [DAG extractor](src/dag.rs) selects roots,
columns and shared producers jointly across all 140 outputs. A producer costs
`1 + incoming regions + grouping columns`; a column costs
`2 + local scalar functions`. Each selected producer and column is charged once.
The solver reports its objective, bound and optimality status. Optimality refers
to this structural objective over available alternatives, not execution time.

The serializer validates and writes the selected views and their dependencies.
LMFAO's physical grouping, loops and data structures remain in its backend.
Scalar functions are immutable frontend kernels identified by vector position.

## Reproduce

Prepare sources explicitly. CMake, a C++ compiler, libclang and Boost are required;
Cargo.lock pins the Rust solver and bundled HiGHS source.

```sh
git clone https://github.com/fdbresearch/LMFAO /tmp/LMFAO
git -C /tmp/LMFAO checkout df6a5f59d597e9d7dd5984f268700223553789d0
uv run --locked python -m benchmarks.reproduction.lmfao.prepare \
  --source /tmp/LMFAO --output benchmarks/local/lmfao
./bench.py figures lmfao --rounds 3 --timeout-sec 300
```

The default paper catalog includes this experiment, so `./bench.py figures`
runs it along with the other paper figures. The command above selects only
LMFAO. `--lmfao-data` and `--lmfao-backend` can select another prepared directory.
Neither command downloads sources or prepares the external backend implicitly.

The experiment compares shipped LMFAO roots, our implementation of the paper's
section 3.3 root heuristic, slotted egglog, and ordinary egglog. Every generated
program uses the same corrected backend and compiler flags. All 140 answers are
checked against independent DECIMAL queries before timing: keys and counts must
match exactly; floating moments use `rtol=1e-9`, `atol=1e-7`.

Preparation uses a separate checkout of the exact commit, checks both patches
before applying them, and records commit, adapter and executable hashes.
Evaluation rejects mismatched provenance. An adapter change requires a new
prepared directory; preparation preserves the source checkout.

`--boost PREFIX` supports unpacked Boost. Generated programs also need its include
path; `--lmfao-cxxflags` replaces all defaults, so retain the optimization flags:

```sh
--lmfao-cxxflags '-std=c++11 -O3 -pthread -mtune=native -ftree-vectorize -fopenmp -I/PREFIX/include'
```

`--rounds` sets measured repetitions; the paper experiment uses a 192-round
egraph budget, not a claim of saturation. Optimizers and generated programs use
one thread. The focused `./bench.py lmfao --data PATH --backend PATH --output-dir PATH`
command retains advanced options: `--rewrite-rounds` changes that budget,
`--cpu N` pins the experiment, `--jobs` controls compilation, and `--cxxflags`
sets generated-program flags.
`--dag-timeout` bounds extraction; `--build-timeout` bounds backend builds and
checks. The shared timeout and 16 GiB allocator/address-space cap apply to egraph
runs, including extraction. `--memory-limit-gib` and `--no-memory-limit` override
the cap; peak RSS is measured separately. Generated C++ execution has a timeout
but no allocator cap.

## Results and timing

Egraph measurements join the paper invocation's collector, resource limits and
append-only JSONL cache. `--report PATH` selects that cache (default `.reports.jsonl`;
the focused `./bench.py lmfao` command defaults to `OUTPUT/optimizer.jsonl`).
Successful observations are reused; a resource failure stops repetition at
unchanged bounds and remains visible. Query executions are fresh, with rotating
and reversing method order after correctness checking has warmed each program.
The C++ preparation and execution records are case-specific outputs; they do not
use the shared egraph cache or its interactive reports.

- **Egraph time/RSS:** separate processes measuring parsing and rewriting,
  excluding DAG extraction.
- **Optimization + generation:** the full preparation run. For egraph plans this
  includes LMFAO query export, translation, rewriting, DAG extraction, and a
  second LMFAO invocation that imports the plan and generates C++. Both frontend
  invocations are charged. The controls use one normal LMFAO invocation.
- **C++ compilation:** one separate observation per distinct program.
- **Computation:** median of warm executions, excluding loading/sorting and
  checking, matching the paper's computation scope. Whole-process execution is
  also retained.

The separate egraph measurements are not added to the preparation time.
Identical plans share compilation/execution observations, recorded as aliases.
For repeated use, preparation plus N executions is an amortization estimate.

The paper command writes `lmfao.table.tex`, `lmfao.caption.tex`, `lmfao.md` and
`lmfao.results.json` to the common paper output directory. Its `lmfao/` subdirectory
contains `pipeline.json`, `comparison.md`, `execution.jsonl`, validation records
and per-method `plan.json`/`plan.txt`/generated C++. Status and artifact paths go
to stderr. The focused command prints Markdown to stdout (`--format json` selects
JSON). Results are generated, not checked in.

On the measured machine, a fresh three-repetition evaluation takes about 25
minutes once tools are built, or about 12 minutes with compatible egraph
measurements cached. Ten repetitions are estimated at about 40 minutes. Most
time goes to rewriting and C++ compilation; query computation takes less than
one second. Initial source/dependency setup is additional.

## Comparison with the paper

The [paper](https://arxiv.org/abs/1906.08687) describes a batch coverage heuristic
for choosing roots. The released covariance frontend instead uses configured
roots. Our `paper` control implements that heuristic and runs the original
logical optimizer afterward; it is not another released upstream mode.

The public configuration yields 140 final aggregates, 46 intermediate aggregates
and 125 views, matching the Favorita counts in Table 2. The paper's experiment
scripts refer to an unavailable feature configuration, so matching counts do
not establish identical roots or reproduce the published timings. Compare query
execution with both root policies, and assess the egraph representations using
the same input, rules, budget and resource cap. A failure of the ordinary encoding
is evidence about this implementation; different encodings or rule schedules
can behave differently.

## Ownership and tests

Upstream [LMFAO](https://github.com/fdbresearch/LMFAO) is pinned to
`df6a5f59d597e9d7dd5984f268700223553789d0`. We reuse its query generation,
schema parsing, view grouping, multi-output loops, data structures and C++
generator. `features.conf`, `treedecomposition.conf` and `LICENSE` are unchanged
upstream files. LMFAO reads the configuration in the data directory; our copies
verify that it matches this experiment. `treedecomposition.conf` gives the table
schemas and join edges, while `features.conf` selects the model's features.

`workload.json` records LMFAO's unoptimized queries, function definitions and
schema. It supplies routine tests without requiring an external LMFAO build or
dataset. Each live frontend export must match it; selected plans are separate
`plan.json` outputs.

The [adapter](../reproduction/lmfao/) contains one header and two patches.
`OptimizerBridge.hpp` exports queries/plans, imports selected views and implements
the paper-root control. `optimizer-bridge.patch` adds export-only and plan-import
paths to `QueryCompiler::compile()`. Python runs the Rust optimizer between these
two LMFAO invocations; C++ does not launch Python or parse optimizer settings.
`dependent-output.patch` fixes accumulation across terminal output keys and is
applied to every compared method. The rules, translator, Rust extractor and
Python evaluation/checking code are new.

`make check` discovers the Python integration/semantic tests and Rust solver tests
through the normal workspace configuration. Small exact bag-semantics tests run
both representations with duplicates, fractional/negative weights and empty
relations. Controls require hoisting for executable lowering and fusion for
shared producers. Solver tests compare DAG choices with exhaustive enumeration;
backend tests cover timeout cleanup, patch drift and provenance rejection.
