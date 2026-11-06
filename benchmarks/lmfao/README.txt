LMFAO logical optimization case study
====================================

This runs the public LMFAO Favorita covariance workload: 140 aggregate queries
on six relations and 16 features, using the artifact's 2,000,000-row Sales
fragment. Egraph rules choose join-tree roots, push aggregates into directional
views, and expose compatible views for sharing. A joint cost-based DAG extractor
selects the implementations of all 140 outputs. LMFAO generates the input queries
and calls our optimizer as a subprocess, then imports the selected DAG and
continues through its C++ backend.

This reproduces the artifact's query workload and compares logical optimization
on the same execution backend. It does not reproduce the paper's full 127M-row
Favorita experiment, its other datasets/models, or parallel execution. The
extractor minimizes a fixed structural cost. An optimum for that cost does not
imply the fastest executable plan.

"Covariance" names the query workload, not a dataset. The queries compute a
non-centered covariance (Gram) matrix: counts, sums, squares and pairwise
products over the joined data. Categorical features become grouping keys, so
the workload includes counts by city and sales sums by city. These are reusable
inputs to linear-regression training; this case study does not train a model.

Provenance:
  Paper: https://arxiv.org/abs/1906.08687
  Artifact: https://github.com/fdbresearch/LMFAO
  Commit: df6a5f59d597e9d7dd5984f268700223553789d0

features.conf, treedecomposition.conf and LICENSE come from that commit.
workload.json is a frozen export from its CovarianceMatrix frontend, including
function IDs, queries and parsed join tree. Python reads this export; it does not
reimplement query enumeration or configuration parsing. The engine comparison
uses egglog's slotted encoding and the native slotted-egraphs MultiPattern matcher
with snapshot substitution.

Code ownership:
  Reused upstream: query generation, schema/configuration parsing, view grouping,
    multi-output loops, execution data structures and C++ code generation.
  Optimizer bridge: optimizer-bridge.patch hooks QueryCompiler::compile();
    OptimizerBridge.hpp exports queries/plans and invokes a subprocess;
    ImportPlan.hpp validates and imports the selected views.
  Backend correction: dependent-output.patch, applied to both pipelines.
  New Python/rules: translation, egraph rules, decoding, structural cost, DAG
    extraction, benchmark orchestration/reporting and independent checking.

All Python files are new code. The two C++ adapter headers are additions to the
pinned checkout; the patches are kept separately from those headers.

Run
---
Prepare the pinned backend explicitly; collection never acquires sources or
regenerates inputs. CMake, a C++ compiler and Boost are required.

  git clone https://github.com/fdbresearch/LMFAO /tmp/LMFAO
  git -C /tmp/LMFAO checkout df6a5f59d597e9d7dd5984f268700223553789d0
  uv run --locked python -m benchmarks.reproduction.lmfao.prepare \
    --source /tmp/LMFAO --output /tmp/lmfao-backend
  ./bench.py lmfao --data /tmp/LMFAO/data/favorita-small \
    --backend /tmp/lmfao-backend/build/multifaq \
    --output-dir /tmp/lmfao-results --rounds 5 --timeout-sec 900

The preparation command creates a separate checkout. --boost PREFIX supports
an unpacked Boost installation; supply its include path through --cxxflags when
compiling generated programs if it is not on the compiler's default path.

--rounds/--samples specifies measured repetitions; frozen rewrite budgets are
64 rounds. A budget does not establish saturation. --cpu N pins the experiment;
extraction and generated executables use one thread. --jobs controls
C++ compilation, --build-timeout bounds each build/diagnostic subprocess, and
--dag-timeout bounds the joint solver. Compiler flags are identical for controls
and extracted plans. --report PATH selects the shared append-only optimizer
cache (default OUTPUT/optimizer.jsonl). Execution samples are fresh.
--treatment and --variant restrict the selected engines and ablations; both may
be repeated. For the full logical optimizer against LMFAO without the additional
engine comparison, use --treatment slotted --variant shared. Original LMFAO
remains the control in every invocation. A single-engine run does not establish
graph equivalence between engines.

--timeout-sec and --memory-limit-gib/--no-memory-limit bound optimizer processes;
the timeout also bounds timed generated executables. The memory limit does not
cover extraction or C++ execution. Status goes to stderr; the final
pipeline JSON goes to stdout.

Optimizer-only comparisons need no data or backend:

  ./bench.py benchmarks/lmfao/inputs/shared.egg \
    --treatment slotted --compare-treatment slotted-ref-multi \
    --rounds 5 --timeout-sec 900 --report /tmp/lmfao-engines.jsonl --format markdown

Rules and extraction
--------------------
logical.egg contains three IRs: AggregateQuery, directional ComputeView, and
ViewColumn with an explicit SharedView producer. Input terms contain original
queries and query-independent orientations of the supplied tree, never optimized
target plans. All six relation roots are candidates; there is no arbitrary
join-order search. Scalar functions are closed lambdas with fresh source binder
names. Their alpha-equivalence permits common aggregate kernels to share.

The main multipattern rules, in abbreviated form, are:

  query = AggregateQuery(domain, keys, weights), TreeRoot(domain, region)
    => query = ViewRequest(region, keys, weights)

  request = ViewRequest(region, keys, weights), region = Region(...)
    => request = ComputeView(region, keys, weights,
                             SelectWeights(local, weights), ChildRequests(...))

  a = ComputeView(region, keys, wa, la, ca)
  b = ComputeView(region, keys, wb, lb, cb), wa != wb
    => a = ViewColumn(SharedView(region, keys), wa, la, ca)

For each child, rules retain the separator keys and required query keys in that
subtree, and send it the corresponding scalar functions. Balanced mask/vector
operations and the distinct-weight test are themselves normalized by rewrites.
Views retain bag multiplicities; they do not assume dimension keys are unique.

A column owns its incoming aggregate dependencies. Compatible selected columns
reference the same explicit SharedView node. Extraction pays for that producer
once, plus each selected column's work. The backend adapter serializes those
selected identities; it does not discover or merge compatible views. This avoids
enumerating all possible column subsets in the graph.

HiGHS selects one acyclic DAG jointly across all required outputs; the report
includes its bound, gap and time limit. Decoder validation rejects plans that
change a query's keys/functions or violate directional pushdown semantics.

Cost model
----------
Each selected producer costs 1 + C + K, where C is its number of incoming
regions and K its number of grouping columns. Each selected aggregate column
costs 2 + F, where F is its number of local scalar functions. ComputeView pays
both costs; ViewColumn pays the column cost and references a shared producer.
The joint DAG objective charges each selected producer and column once.

Coefficients are fixed unit weights, not fitted to execution times. The objective
favors fewer shared intermediates and fewer carried grouping columns. It uses
only the exported graph, without reading data or using the configured per-feature
root preferences. This is joint DAG selection, not an implementation of the
paper's root-assignment heuristic.

Controls and backend
--------------------
  single-root  Sales root only, pushdown and sharing enabled
  roots        All six roots, pushdown enabled, shared producers disabled
  shared       All six roots, pushdown and sharing enabled
  original     LMFAO's original query/root/decomposition/view-merging logic

A root is the relation where an aggregate's traversal ends; partial aggregates
flow toward it. Sharing lets several aggregate columns use one intermediate
producer. These ablations keep the queries fixed: compare single-root with
shared to test root choice, and roots with shared to test shared producers.
Identical-subexpression reuse and the backend's multi-output optimization remain
enabled in every variant; roots does not disable all forms of sharing.

The first three are frozen egraph workloads run on both engines. The original
control runs the same backend executable without an optimizer subprocess. All
variants retain LMFAO's view grouping, multi-output loops, data structures and
C++ compilation. The bridge exports the original queries before logical optimization. For egraph
runs, it invokes optimize.py, which translates that actual export, runs the
selected engine, extracts a DAG and writes the imported plan. Each invocation
checks the frontend export against the frozen benchmark workload. A mismatch
requires explicit regeneration. An unpatched executable is rejected.

The original control also exports its selected views. Each variant gets a
plan.json and a readable plan.txt with view equations and output references.
These show actual plans; printing does not choose roots or combine producers.

Preparation also applies dependent-output.patch to the code generator for every
variant, including original. Arbitrary root choices exposed an upstream running-
total error: a terminal loop over an output key accumulated a register across
keys before writing each result. On the public data, a query grouped by store
and holiday_type returned 3158 instead of 1989 for (1, 2). The patch evaluates a
product per output tuple when all enclosing loops are output loops and no nested
aggregate remains. It preserves accumulation for loops that are reduced. This
is a backend correctness correction, not an egraph optimization. Reports must
identify this patched-backend comparison; it is not an untouched artifact run.

Each generated plan is checked against an independent DECIMAL computation of
all 140 original queries. Keys and counts must match exactly; floating moments
use rtol=1e-9 and atol=1e-7. Checking uses a separate executable with 17-digit
diagnostic output. Timed executables omit output dumping and checking.

Reports and validation
----------------------
  comparison.md       computation-time table, ablation caption and preparation costs
  pipeline.json       phase summaries, failures, plans, builds and validation
  optimizer.jsonl     shared cache with input/binary hashes and peak RSS
  *-graph.json        diagnostic graphs from the frozen engine comparison
  *-isomorphism.json  full comparison verdict; limits/timeouts are inconclusive
  VARIANT/workload.json  actual LMFAO frontend export
  VARIANT/graph.json     graph produced by the optimizer subprocess
  VARIANT/extraction.json selected enodes, costs, solver bound/gap and graph hash
  VARIANT/plan.json      serialized views, aggregate columns and query references
  VARIANT/plan.txt       readable view equations and query references
  metadata.json       dataset hashes, versions, CPU affinity and timing scopes
  builds.json         generation/compilation times, flags and binary hashes
  execution.jsonl     fresh C++ process-wall and computation samples
  validation.json    independent output checks

comparison.md leads with aggregate computation time, excluding loading/sorting,
optimization and compilation. Shared versus single-root isolates root choice;
shared versus roots isolates shared-producer merging. Missing results appear as
unavailable. The comparison with original LMFAO measures plan quality against its
logical optimizer; the ablations test which choices help within the egraph.

A separate table reports optimization/generation and C++ compilation. Generation
measures the complete LMFAO compiler process: frontend, optimizer subprocess and
C++ generation. The subprocess's translation, rewriting/export, decoding,
extraction and serialization breakdown remains in extraction.json and is not
added to generation again. Preparation phases are observed once; their sum is
not a measured end-to-end runtime. For N executions of a reused plan, estimate
total time as preparation + N times execution, specifying whether execution
includes loading/sorting.

Identical serialized plans reuse compilation and execution observations, charged
in full to each variant and identified by execution_aliases. Tool builds, graph
isomorphism, diagnostic graph exports and independent correctness checks are
excluded for both pipelines. validation_preparation_seconds records the oracle's
loading/computation. Every plan is selected before the Python checker reads data.

Separate optimizer-only samples include startup, parsing/frontend, graph
construction and rewriting. Egglog's ruleset_work_seconds measures exclusive
ruleset work, not rewrite-loop wall time. These samples and their diagnostic
export reruns are not added to generation. The live optimizer subprocess runs
the same frozen translation, verified against LMFAO's actual frontend export.
Validation provides a warmup; subsequent executions rotate/reverse plan order.

The paper's Table 3 excludes compilation and data loading, uses sorted inputs,
and reports the mean of four runs after a warmup (Section 4.1 and Appendix B).
Our primary table follows that computation scope but reports medians.

Read logical.egg, logical.py (decoding/costs/serialization), and dag.py (joint
extraction). optimize.py implements the subprocess; backend.py handles the
upstream compiler and generated executables. optimizer.py adapts the shared
benchmark collector; cli.py joins the stages.

make check includes live two-engine count checks and Python tests of joint
sharing, cycles, every root orientation, bag duplicates, negative weights,
squares and cross-relation products. Full graph isomorphism is checked separately
by the CLI; matching counts alone are not proof. Real-data C++ validation is part
of the explicit CLI experiment, not ordinary tests.

Regeneration is explicit. After building the bridge, export the upstream input:

  mkdir -p /tmp/lmfao-export
  (cd /tmp/lmfao-export && \
    LMFAO_WORKLOAD_FILE=/tmp/lmfao-export/workload.json \
    /tmp/lmfao-backend/build/multifaq --path /tmp/LMFAO/data/favorita-small \
      --model covar --parallel none --mo 1 --compress 1 --out /tmp/lmfao-export)
  cp /tmp/lmfao-export/workload.json benchmarks/lmfao/workload.json

Then freeze the engine inputs and correctness graphs:

  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --check
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --fixtures
  cargo build --locked --release -p egglog-experimental
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --graphs
