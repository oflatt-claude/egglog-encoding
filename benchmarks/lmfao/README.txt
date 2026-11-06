LMFAO aggregate batching case study
==================================

This is a workload port and batching experiment. It uses the public LMFAO
Favorita covariance configuration: 140 aggregates over six relations and
16 features (three numerical, 13 categorical). Categorical features are
grouping keys; numerical features are aggregate weights. The public
favorita-small fragment has 2,000,000 Sales rows.

LMFAO decomposes queries into partial aggregates along join trees, shares views
across queries, and generates specialized C++. This case study materializes the
join and batches aggregates in DuckDB. It does not reproduce the full paper's
scale, multi-root optimization, C++ backend or performance comparisons.

Provenance:
  Paper: https://arxiv.org/abs/1906.08687
  Artifact: https://github.com/fdbresearch/LMFAO
  Commit: df6a5f59d597e9d7dd5984f268700223553789d0

features.conf, treedecomposition.conf and LICENSE come from that commit.
model.py follows src/application/CovarianceMatrix.cpp's query enumeration.
The engine comparison uses egglog's slotted encoding and the native
slotted-egraphs MultiPattern matcher with snapshot substitution.

Run
---
From the repository root:

  git clone https://github.com/fdbresearch/LMFAO /tmp/LMFAO
  git -C /tmp/LMFAO checkout df6a5f59d597e9d7dd5984f268700223553789d0
  ./bench.py lmfao --data /tmp/LMFAO/data/favorita-small \
    --output-dir /tmp/lmfao-results --rounds 5

--rounds (also --samples) sets measured repetitions. Rewrite budgets are fixed
in the inputs: zero for independent, 12 for fuse and grouping. A rewrite budget
does not establish saturation. --cpu N pins an available logical CPU; DuckDB
and the DAG solver use one thread.

--report PATH selects the shared append-only optimizer cache (default:
OUTPUT/optimizer.jsonl). SQL execution samples are always fresh. --timeout-sec
and --memory-limit-gib/--no-memory-limit bound optimizer processes, not DuckDB.
--dag-timeout bounds the solver; zero selects the feasible heuristic. Status
and builds go to stderr; pipeline.json is also printed to stdout.

Optimizer-only comparisons need no dataset or extraction:

  ./bench.py benchmarks/lmfao/inputs/grouping.egg \
    --treatment slotted --compare-treatment slotted-ref-multi \
    --rounds 5 --report /tmp/lmfao-engines.jsonl --format markdown

Rules and execution
-------------------
The input is a Pair tree of independent named SDQL sums, with no optimized
target supplied. batch.egg contains four rules:

  Output(name, Sum(input, row, count, body))
    = Batch(input, Task(name, lambda row. lambda count. body))

  program = Pair(left, right), left = Batch(input, a), right = Batch(input, b)
    => program = Batch(input, TaskPair(a, b))

  Batch(input, tasks) = FusedBatch(input, tasks)
  Batch(input, tasks) = GroupingBatch(input, tasks)

The first rule closes the aggregate body over its binders. The merge rule
joins three patterns with a common source eclass. Existing Pair subtrees bound
the candidates. FusedBatch shares scans for equal grouping keys; GroupingBatch
also permits GROUPING SETS for compatible weights.

The egraph produces these alternatives. The remaining steps are external:
  1. Export each graph and compare the complete graphs with the Rust
     isomorphism checker. Timeouts are inconclusive; counts alone are not proof.
  2. Load the data and compute independent DECIMAL answers and exact source/
     output cardinalities. These statistics are supplied to extraction.
  3. Decode exported nodes and slot renamings. A HiGHS DAG extractor charges
     shared producers once and chooses acyclic representatives. Its objective
     counts scans, aggregate updates and output cells. Solver optimality refers
     to that proxy within the graph, not minimum execution time.
  4. Compile selected operators into SQL. Python partitions compatible
     keys/weights and emits materialized aggregates; DuckDB plans and runs SQL.
  5. Check all 140 outputs after every warmup and measured execution. Keys/counts
     match exactly; DOUBLE moments use rtol=1e-9/atol=1e-7 against the oracle.

What the controls establish
---------------------------
sql-grouping-sets compiles the query definitions directly using the same SQL
batching helper. independent-slotted-lowering-control enables that helper across
the zero-round program's output boundaries. For example, SUM(x) and SUM(x*x)
grouped by k can become one SELECT containing both sums without egraph search.

A gain over independent outputs shows the benefit of batching. Matching the
compiler-only control does not show an advantage from egraph search. Identical
SQL shares execution samples, with aliases recorded in identical-sql.json;
optimizer/extraction observations remain separate. This CLI does not execute
the original LMFAO C++ artifact.

Reports and timing
------------------
  pipeline.json       phase summaries, optimizer failures and graph verdicts
  optimizer.jsonl     shared cache with binary/input hashes and peak RSS
  *-graph.json        annotated exports from each engine
  *-isomorphism.json  full verdict and witness, when available
  *-plan.json         selected enodes, costs, solver status/bound and operators
  *.sql               executable programs exposing every named output
  execution.jsonl     execution samples and correctness results
  metadata.json       data hashes/rows, versions, CPU affinity and timing scopes
  statistics.json     cardinalities supplied to extraction

Optimizer process time includes startup, parsing/frontend, graph construction
and rewriting. Export is a separate rerun. Egglog's ruleset_work_seconds reports
exclusive ruleset work, not rewrite-loop wall time; the native reference has no
such breakdown. Extraction and Python SQL generation have one observation per
graph. SQL timing includes planning, join and aggregate materialization, with
one warmup followed by rotating/reversed measurement order. Loading, statistics,
result fetching/checking and cleanup are excluded. Separate phase medians are
not a measured end-to-end runtime.

Review and validation
---------------------
Read batch.egg, then benchmarking/lmfao/batch.py (graph interpretation/costs),
dag.py (extraction), sql.py (lowering), and data.py (execution/oracle).
optimizer.py adapts the shared collector; cli.py assembles the experiment.

make check runs the live two-engine rule/goal/count checks in
benchmarks/paper-tests/tests/lmfao.rs and the Python DAG/SQL tests. Cases cover
wrong-source merges, empty/duplicate/nullable inputs, negative weights,
reordered/repeated/three-column keys, nonlinear multiplicity, and cyclic or
shared DAG choices. Real-data correctness is checked by the CLI.

Collection/tests read frozen fixtures. Regeneration and acquisition are explicit:

  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --check
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao
  cargo build --locked --release -p egglog-experimental
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --graphs

--check verifies frozen input bytes; --graphs refreshes the small SQL test
exports and their hashes using the built release binary.
