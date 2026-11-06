LMFAO aggregate batching case study
==================================

This case study starts with the 140 covariance aggregates from the public
LMFAO Favorita configuration: six relations and 16 features (three numerical,
13 categorical). Categorical features become grouping keys; numerical features
become aggregate weights. There are ten scalar, 52 one-key, and 78 two-key
outputs. The public favorita-small input has 2,000,000 Sales rows. It is a real
fragment of the dataset, not the full-scale experiment reported in the paper.

Sources:
  Paper: https://arxiv.org/abs/1906.08687
  Artifact: https://github.com/fdbresearch/LMFAO
  Pinned commit: df6a5f59d597e9d7dd5984f268700223553789d0

features.conf, treedecomposition.conf and LICENSE are copied from that commit.
The query enumeration follows the artifact's covariance generator. This ports
its workload, not its complete optimizer: multi-root factorization, generated
C++ and parallel execution are outside this experiment. The native comparison
is slotted-egraphs MultiPattern with snapshot substitution, not ordinary egg.

Run
---
From the repository root, acquire the data explicitly, then run the public CLI:

  git clone https://github.com/fdbresearch/LMFAO /tmp/LMFAO
  git -C /tmp/LMFAO checkout df6a5f59d597e9d7dd5984f268700223553789d0
  ./bench.py lmfao --data /tmp/LMFAO/data/favorita-small \
    --output-dir /tmp/lmfao-results --rounds 5

Choose an available logical CPU with --cpu N to pin the run. DuckDB and the DAG
solver use one thread. --rounds (also --samples) means measured repetitions,
not rewrite rounds. The frozen independent input has a zero-round rewrite
budget; fuse and grouping each have a 12-round budget. A budget does not certify
that all rounds ran or that saturation was reached.

The command uses the existing target builder, treatment definitions, resource
guards, collection planner and append-only ReportStore. --report PATH selects
the optimizer cache (default OUTPUT/optimizer.jsonl). Compatible observations
are reused. --timeout-sec and --memory-limit-gib/--no-memory-limit control the
optimizer processes; they do not bound DuckDB execution. --dag-timeout controls
the solver; zero uses its feasible heuristic incumbent. Builds/status go to
stderr; the final pipeline JSON goes to stdout and OUTPUT/pipeline.json.

Optimizer-only comparisons also work directly with the normal benchmark CLI,
without acquiring the data or running extraction:

  ./bench.py benchmarks/lmfao/inputs/grouping.egg \
    --treatment slotted --compare-treatment slotted-ref-multi \
    --rounds 5 --report /tmp/lmfao-engines.jsonl --format markdown

What happens in the egraph
-------------------------
The frozen program contains only independent named SDQL sums in a balanced
Pair tree. There is no optimized target in the benchmark input. batch.egg has
four general rules, with no workload-specific relation or feature names:

  Output(name, Sum(input, row, count, body))
    = Batch(input, Task(name, lambda row. lambda count. body))

  program = Pair(left, right), left = Batch(input, a), right = Batch(input, b)
    => program = Batch(input, TaskPair(a, b))

  Batch(input, tasks) = FusedBatch(input, tasks)
  Batch(input, tasks) = GroupingBatch(input, tasks)

The first rule joins the output and aggregate patterns and closes the body
over its two binders. The second joins three roots and requires the SAME source
eclass on both sides. Existing Pair subtrees bound the batch candidates; the
rules do not enumerate arbitrary subsets. Original and batched alternatives
remain available for extraction. FusedBatch requests shared scans for equal
grouping keys. GroupingBatch also permits GROUPING SETS for compatible weights.

Pipeline and interpretation
---------------------------
1. Both engines read frozen, self-contained inputs. The shared collector times
   fresh optimizer processes. Separate export reruns produce annotated graphs;
   the existing Rust isomorphism checker compares the complete graphs. A search
   timeout is inconclusive; equal counts alone are not an isomorphism proof.
2. DuckDB loads the data. Independently generated DECIMAL queries compute all
   expected results. Exact source/output cardinalities supply the cost model.
   This untimed preparation is not a production cardinality estimator.
3. Python decodes actual exported source/task nodes, including slot renamings.
   A joint HiGHS DAG MILP selects representatives, charging shared producers
   once and excluding cyclic choices. It starts with a feasible heuristic and
   retains it if necessary. The objective counts scans, aggregate updates and
   output cells. An optimal solver result certifies only this proxy within the
   exported graph, not minimum runtime.
4. The SQL backend compiles the selected operators. It partitions compatible
   keys/weights and chooses materialized aggregate tables. This compatibility
   grouping and SQL generation happen outside the egraph. DuckDB then plans
   and executes the resulting SQL.
5. Every warmup and measured execution checks all 140 outputs. Keys and counts
   must match exactly; floating moments use rtol=1e-9 and atol=1e-7 against the
   DECIMAL oracle. Timed weights are DOUBLE. Each distinct SQL program receives
   one warmup and rotating/reversed measurement order.

Two controls distinguish rewrite discovery from SQL lowering:
  - sql-grouping-sets: a strong SQL program built directly from the pinned
    query definitions, using the same backend and physical batching helper.
  - independent-slotted-lowering-control: the zero-round extracted program
    with batching explicitly enabled across its output boundaries in Python.

"Direct batching" means the compiler groups compatible aggregates itself. For
example, SUM(x) and SUM(x*x) grouped by k can become one SELECT with both sums.
If that control equals the extracted GroupingBatch SQL, the rewrite system has
found the same useful plan; it has not beaten direct batching. Identical SQL is
timed once per sample and aliases are recorded in identical-sql.json. Both
selected plans and their own optimization/extraction timings are retained.
The CLI does not run the original LMFAO C++ compiler. Its SQL control is not an
LMFAO runtime replication or a comparison of generated-code backends.

Review the results
------------------
  pipeline.json            phase summaries, optimizer failures and parity status
  optimizer.jsonl          shared append-only cache, binary/input hashes and RSS
  *-graph.json             actual annotated exports from each engine
  *-isomorphism.json       full comparison verdict and witness, when available
  *-plan.json              selected enodes, cost, solver bound/status and operators
  *.sql                    complete executable programs and named output views
  execution.jsonl          fresh per-program execution samples and validation
  metadata.json            input hashes/rows, versions, CPU affinity, timing scopes
  statistics.json          exact cardinalities supplied to extraction

Optimizer process time includes startup, parsing/frontend, graph construction
and rewriting; it excludes builds, export, extraction and SQL. Egglog's separate
ruleset_work_seconds is engine-reported exclusive work, not rewrite-loop wall
time. The native reference has no such breakdown. Graph collection is a separate
rerun. Extraction and Python SQL generation are single observations per graph.
SQL execution includes planning, the join and aggregate materialization;
loading, statistics, result fetching/checking and cleanup are outside its timer.
Separate phase medians must not be added and called a measured end-to-end run.
SQL measurements are always fresh; only optimizer observations use the cache.

Code and validation
-------------------
Read batch.egg first, then benchmarking/lmfao/batch.py for graph interpretation
and costs, dag.py for extraction, sql.py for physical lowering, and cli.py for
the experiment. optimizer.py is the adapter to the existing benchmark collector;
data.py contains execution/oracles and model.py the pinned query definitions.

make check discovers all tests through the normal Python and Rust suites.
benchmarks/paper-tests/tests/lmfao.rs executes six small frozen programs in both
engines, checking rewrite goals and annotated graph counts, including rejection
of merges across different sources. Python tests exercise the exported plans on
empty/duplicate/nullable data, negative weights and cancellation, reversed,
repeated and three-column grouping keys, plus nonlinear-multiplicity rejection.
DAG tests compare the MILP with exhaustive small examples, including cycles and
shared optional producers. These small tests do not replace real-data validation.

Routine collection/tests do not regenerate fixtures or acquire sources.
Explicit reproduction commands, after intentional source changes:

  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --check
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao
  cargo build --locked --release -p egglog-experimental
  uv run --locked python -m benchmarks.reproduction.slotted.lmfao --graphs

The last command refreshes the small Python graph fixtures and their hashes.
