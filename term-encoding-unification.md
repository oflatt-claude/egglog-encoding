# One execution path for equality and proofs

- Status: feasibility brief, not an implementation plan yet
- Date: 2026-08-12
- Baseline: `origin/main` at `5ead0a0cacf847a129294a870de13503f2d7f9c4`
- Paper/engineering companion: [`encoding-architecture-bridge.md`](encoding-architecture-bridge.md)
- Incremental implementation sequence:
  [`incremental-unification-pr-roadmap.md`](incremental-unification-pr-roadmap.md)
- Current overhead decomposition:
  [`term-encoding-overhead-breakdown.md`](term-encoding-overhead-breakdown.md)

## Question

Can egglog remove the independent normal and term/proof execution paths, make
one path universal, and keep the proof-disabled cost within roughly 5-10% of
today's normal mode?

There are two materially different versions of that goal:

1. **One proof-capable execution path, with evidence disabled by default.**
   This looks feasible. Its disabled mode can be based on today's native
   representation and should be held to a near-zero overhead gate.
2. **Always collect enough evidence to extract arbitrary proofs, within 5-10%.**
   This is not supported by current measurements. It needs a separate,
   deliberately optimistic lower-bound experiment before becoming a design
   constraint.

## Short answer

Do not try to make the current generated term program the sole production
representation. On current `main`, term-only mode is **2.01-2.12x** normal wall
time across the six-workload suite and uses **1.59-2.26x** peak RSS. The gap is
not one removable proof feature: term-only already carries `Unit` rather than
real proofs. It comes from the physical representation and compiler pipeline:
extra term/view/UF tables, wider rows, rewritten queries, generated maintenance
rules and schedules, and a second desugar/typecheck pass.

A single path is still a good complexity goal, but the likely destination is:

```text
source
  -> one parse/desugar/typecheck pipeline
  -> typed e-graph operations
  -> one equality kernel
       - native/fused storage and rebuild
       - NoEvidence or ProofEvidence sidecar
  -> one rule engine
```

The current term encoding is valuable as an executable specification of
equality and proof semantics during migration. Once the typed kernel has parity,
its literal output should stop being a production execution mode. A printer
derived from the same typed encoding artifact can remain for the paper,
differential tests, and debugging without remaining an independently maintained
execution path.

Calling that destination "term encoding" is reasonable if term encoding means
the semantic decomposition -- stable terms, interning, equivalence, congruence,
and justifications. It should not mean materializing that decomposition as
ordinary user-language tables and rules on the main backend.

## What is duplicated today

### Normal path

```text
parse -> desugar -> typecheck -> remove globals -> typed commands
      -> constructor/function tables + native Union actions
      -> backend union-find + native rebuild
```

### Term/proof path

```text
parse -> desugar -> typecheck in a cloned EGraph -> proof-normal-form checks
      -> remove globals
      -> generate new source AST:
           term relations + FD views + @UF tables + indexes
           rewritten bodies/actions + maintenance rules/schedules
      -> desugar again -> typecheck again -> remove generated globals again
      -> generic table/rule execution
      -> (proof mode) retain the original typed program for checking
```

The second path is not a small option around the first. It independently models:

- constructor creation and interning;
- explicit union and congruence;
- rule-body matching and rule-head construction;
- globals and top-level actions;
- custom functions and merge expressions;
- delete and subsume;
- path compression and rebuilding;
- container canonicalization;
- input loading and extraction;
- proof premises, proof nodes, extraction, simplification, and checking.

The `egglog/src/proofs` directory currently has about 11,949 lines of
production Rust, excluding `proof_tests.rs`. Roughly 6,999 of those lines are in
the encoding-facing modules (`proof_encoding*`, `proof_head`, `proof_fresh`, and
`proof_container_rebuild`), in addition to an 877-line encoding design document.
Not all of those lines would disappear under a native proof path, but this shows
where the representational duplication lives; the checker, proof algebra, and
proof format are separate assets worth preserving.

## Current measurements

All benchmark comparisons used the same release binary at the baseline SHA,
four fresh rounds per endpoint/file, one thread, and a 120-second per-process
timeout. The exact cache is
`/tmp/term-encoding-always-on-bd4752e.jsonl`.

### Execution and memory

| Comparison | Suite wall-time ratio (95% CI) | Notable range | Peak-RSS range |
| --- | ---: | ---: | ---: |
| term vs off | 2.01-2.12x | 1.37-1.51x eggcc; 3.28-3.50x Luminal | 1.59-2.26x |
| proofs vs term | 1.48-1.59x | 1.26-1.37x eggcc; 1.70-1.78x Math | 1.37-1.78x |
| proofs vs off | 3.04-3.30x | 1.79-2.00x eggcc; 5.04-5.98x Luminal | 2.19-3.94x |

`proofs` here means proof data generation for workloads ending in ordinary
`check`s. It does not include automatic proof extraction and verification.

Per-workload term-only wall time:

| Workload | Off | Term | Ratio (95% CI) |
| --- | ---: | ---: | ---: |
| Math | 357-395 ms | 817-835 ms | 2.09-2.32x |
| eggcc 2mm pass 1 | 813-885 ms | 1.20-1.25 s | 1.37-1.51x |
| Pointer small | 7.48-8.82 ms | 14.8-17.6 ms | 1.76-2.24x |
| Hardboiled conv1d | 113-121 ms | 218-227 ms | 1.83-1.98x |
| Luminal Llama | 369-391 ms | 1.27-1.30 s | 3.28-3.50x |
| Herbie | 53.7-55.2 ms | 107-111 ms | 1.95-2.05x |

### Generated-program expansion

`--mode desugar` exposes the extra compiler and representation work.

| Workload | Normal output | Term output | Structural change |
| --- | ---: | ---: | --- |
| Math mini | 98 lines / 5,068 bytes | 521 / 29,974 | 24 -> 38 rules; 1 -> 6 schedules; 13 indexes added |
| eggcc 2mm pass 1 | 11,901 / 570,604 | 28,429 / 1,733,236 | 660 -> 1,203 rules; 2 -> 55 schedules; 417 indexes added |
| Luminal Llama | 7,058 / 515,895 | 69,607 / 4,274,991 | 491 -> 2,429 rules; 6 -> 29 schedules; 1,899 indexes added |

For eggcc, 238 constructors plus 17 functions become 611 generated functions.
For Luminal, 117 constructors plus 1,646 functions become 3,548 functions;
the large static graph's nullary globals are a major contributor.

Frontend-only `hyperfine` measurements (`--mode desugar`, two warmups, ten
runs, output discarded) were:

| Workload | Normal mean | Term mean | Ratio |
| --- | ---: | ---: | ---: |
| eggcc 2mm pass 1 | 50.6 +/- 0.4 ms | 207.5 +/- 1.8 ms | 4.10x |
| Luminal Llama | 78.7 +/- 2.8 ms | 505.1 +/- 9.4 ms | 6.42x |

### Runtime mechanisms

The phase/ruleset data shows that deleting only the second frontend pass would
not reach the target:

- On Math, generated `@rebuilding` costs 382-397 ms and `@parent` costs
  43.1-47.6 ms. Native rebuilding is faster even though its 135-179 ms appears
  as an explicit cost that term mode reports as zero.
- On Luminal, transformed user-rule search rises from about 5.3-5.7 ms to
  475-477 ms. Generated maintenance is only a few milliseconds there; the
  view-based query shape itself is the dominant runtime problem.
- On eggcc, the term frontend adds about 157 ms before execution, while the
  full wall-time delta is roughly 0.37 s. Both compiler expansion and runtime
  representation matter.

### Language coverage

The current support gate has 17 distinct unsupported-reason variants. The
checked-in unsupported snapshot contains 48 files out of 162 non-header,
non-`fail-typecheck` `.egg` corpus files. An always-on path cannot ship until
those are either supported by the common semantics or intentionally removed
from the language.

Several restrictions are artifacts of the encoding rather than intentional
language semantics: function lookups in actions, tuple outputs, user-written
`begin`, merge action blocks, eq-sort `:no-merge`, user indexes, custom sorts,
and some primitive/container result shapes. A single native proof-capable path
should explain evidence for the underlying operation instead of rejecting the
surface syntax because a generated program cannot express it.

### Experiment ledger

| Hypothesis | Distinguishing prediction | Observation | Status |
| --- | --- | --- | --- |
| The second compiler pass explains most term overhead | Recorded runtime phases should be close to normal once outside-of-ruleset time is excluded | Math still spends about 434 ms in generated maintenance; Luminal search rises by about 471 ms | Rejected as a sufficient explanation |
| Generated maintenance is the dominant runtime cost | `@rebuilding` and `@parent` should explain most of every file's delta | True for much of Math, false for Luminal, where transformed user queries dominate | Workload-specific, not sufficient |
| Proof-node construction is the main reason term mode is slow | Term-only, with `Unit` proof columns, should be near normal | Term-only is 2.01-2.12x and 1.59-2.26x RSS | Rejected |
| A fused equality kernel can provide one path near normal cost | A no-evidence seam over native effects should benchmark within 1.05-1.10x | Not yet tested | Active; E1 is the next probe |

Exact benchmark commands:

```bash
./bench.py \
  --target . --compare-target . \
  --treatment term --compare-treatment off \
  --rounds 4 --timeout-sec 120 \
  --report /tmp/term-encoding-always-on-bd4752e.jsonl \
  --format markdown --detail rulesets

./bench.py \
  --target . --compare-target . \
  --treatment proofs --compare-treatment term \
  --rounds 4 --timeout-sec 120 \
  --report /tmp/term-encoding-always-on-bd4752e.jsonl \
  --format markdown --detail phases
```

Representative frontend probe:

```bash
hyperfine --warmup 2 --runs 10 --shell=zsh \
  'target/release/egglog-experimental --mode desugar benchmarks/luminal-llama.egg >/dev/null 2>&1' \
  'target/release/egglog-experimental --term-encoding --mode desugar benchmarks/luminal-llama.egg >/dev/null 2>&1'
```

## Why the current relational representation misses 5-10%

The normal backend already implements the same semantic jobs in specialized
data structures:

- one constructor/function table is both lookup structure and canonical view;
- one native union-find stores equivalence compactly;
- native rebuild uses occurrence information without running user-level rules;
- queries match the original, narrower rows;
- construction does not need a persistent term row, view row, and `Unit` proof
  column for every application;
- schedules do not need maintenance spliced after user rulesets;
- source commands are not generated, parsed, and typechecked a second time.

To bring the current term path near normal, all of those differences would
need to be fused away. At that point the physical implementation would be the
native equality kernel again, preferably behind a cleaner typed interface.

Backend peepholes that recognize generated names such as `@UF_*` and
`@*View` would demonstrate a performance floor, but they are a poor final
architecture: they preserve the large compiler, couple the backend to generated
syntax, and create a hidden third execution path.

## Recommended destination

Use one typed semantic path with two evidence policies, not two programs.

### 1. A typed equality kernel

The frontend should lower every language construct once into a small set of
operations with explicit invariants, for example:

- intern a constructor application and return its e-class;
- read or write a custom function row;
- union two e-classes with a cause;
- commit a batch and rebuild canonical columns;
- apply delete/subsume;
- run a typed rule firing with its substitution.

The one production engine should implement these with today's fused tables,
union-find, and rebuild indexes. With the alternate backends being removed,
this interface should be chosen for clear semantics and useful compiler
staging, not as a lowest common denominator. `Backend::requires_term_encoding()`
should disappear with the backend split rather than be replaced by another
permanent execution-mode switch.

### 2. Optional evidence attached to the same effects

Each equality-producing effect should optionally return/store a compact receipt:

- top-level or input fact (`Fiat`);
- rule firing and the matched row witnesses;
- explicit union/rewrite;
- constructor interning and congruence collision;
- custom-function merge result;
- rebuild/path-compression edge;
- container rebuild and normalization.

The disabled policy should allocate nothing and avoid per-row dynamic dispatch.
The enabled policy should write compact IDs into a side arena, not ordinary
egglog relations. Proof expressions should be materialized root-first only when
requested.

This makes proof availability a property of one runtime, while keeping the hot
representation specialized.

### 3. Stable terms without a second e-graph

Proofs need immutable syntactic identity even after rows are canonicalized,
deleted, or subsumed. Preserve that invariant in a compact `TermArena` or row
sidecar:

```text
TermId -> constructor + child TermIds
row/eclass -> witness TermId
union edge -> CauseId
CauseId -> rule/merge/congruence receipt
```

This replaces the persistent term relations and proof-node relations without
losing the information the checker needs.

### 4. A rule catalog instead of `proof_check_program`

The checker needs normalized rule definitions, merge definitions, global facts,
and primitive validators. Store those once in an immutable typed `RuleCatalog`
shared by execution and checking. Do not retain a second full command stream
whose shape must stay synchronized with the encoded one.

### 5. Keep proof semantics, remove encoding mechanics

Likely keep and adapt:

- the proof algebra and proof term format;
- `ProofStore`, simplification, and the independent checker;
- deterministic extraction policy;
- immutable term identity and typed primitive validators;
- proof snapshot tests.

Likely delete or replace:

- `ProofInstrumentor::add_term_encoding` and command-by-command AST rewriting;
- the cloned `original_typechecking` `EGraph` and second typecheck pass;
- generated term/view/`@UF` tables and `Unit` proof columns;
- generated occurrence-index declarations and maintenance schedules;
- generated path-compression, rebuild, cleanup, and subsume rules;
- proof nodes represented as normal e-graph function rows;
- support rejections caused only by the generated representation;
- `proof_check_program` as a duplicate program;
- the production `--term-encoding` execution mode after migration.

### Likely implementation seams

Current source already concentrates several equality effects at useful
boundaries:

- `EGraph::resolve_command` in `egglog/src/lib.rs` is the frontend split that
  should collapse back to one typed pipeline.
- `EGraph::declare_function` chooses constructor `MergeFn::UnionId`; this is
  where a common constructor/interner contract can replace proof-specific view
  declarations.
- `UnionAction::union` in `egglog/egglog-bridge/src/lib.rs` is the direct native
  union write.
- `EGraph::rebuild` in the bridge owns container-first canonicalization and
  table rebuild; it needs to report congruence/rebuild causes through the same
  optional evidence policy.
- `InPlaceActionBuffer::push_bindings` and its scoped counterpart in
  `core-relations/src/free_join/execute.rs` are where a successful rule match
  becomes an action batch.

The last item is probably the hardest design boundary. Native joins currently
need variable values to execute a head; proof reconstruction also needs stable
identities for the body rows that witnessed the match. Widening every binding
with row provenance would damage the disabled hot path. E3 therefore needs to
test a representation that is absent under `NoEvidence` and carries compact row
or receipt identities only under `ProofEvidence`.

## How incremental desugaring fits

Term encoding is a useful semantic decomposition of the language, but its
pieces should lower into typed internal operators, not recursively back into
egglog source.

The migration can therefore be incremental:

1. Normalize globals, nested expressions, and rule heads once into common typed
   IR.
2. Give construction/interning one operator and route both normal and proof
   behavior through it.
3. Give union, congruence, custom merge, and rebuild explicit cause-bearing
   operators.
4. Move input, containers, delete/subsume, and extraction onto those operators.
5. Add the proof evidence policy and reconstruct the current proof format from
   receipts.
6. Retain literal encoded output as a parity oracle while each family moves,
   generated from the same typed artifact that feeds the fused lowerer.
7. Delete the old production mode once coverage, proof validity, and
   performance gates pass; retain the derived printer only as a test/paper
   asset if it remains useful.

This is a strangler migration around semantic operations, not a flag-day
rewrite and not permanent coexistence of two execution semantics.

## Options

| Option | Complexity outcome | Performance outlook | Main risk |
| --- | --- | --- | --- |
| Make today's generated term program universal | Deletes native UF/rebuild, retains the large encoder | Poor without fusing away its defining representation | More compiler/backend pattern coupling; incomplete language |
| Native single path plus optional proof sidecar | Deletes the source encoder and support split | Disabled mode can be close to current normal; enabled cost unknown | Capturing sound merge/rebuild/rule causes in the native engine |
| Typed encoding IR plus one fused physical lowering | One language semantics, one engine, and a derived reference printer | Fused lowering can retain current native speed | Designing a stable semantic/fusion boundary without building another framework |
| Keep both paths but isolate/shared utilities | Smaller near-term refactor | No forced regression | Does not remove semantic duplication or support drift |

The recommendation is the second and third options together: a common typed
encoding IR, one fused native kernel, an optional proof-evidence policy, and a
reference printer derived from that same IR. The companion architecture note
explains how slotted then proof encoding can compose at this boundary.

## Falsifying experiment ladder

Large production edits should wait until these floors are measured in order.

### E0: frozen reference matrix

Keep the current off/term/proofs measurements and add exact output parity for
the six benchmark files. This is the immutable comparison set.

### E1: `NoEvidence` seam

Route native construction, union, merge, and rebuild through the proposed
evidence interface, with a zero-sized disabled implementation. Record nothing.

Gate:

- no semantic or snapshot delta;
- <=1.05x suite wall time and <=1.10x on every file;
- <=1.05x peak RSS;
- no per-row allocation and no dynamic dispatch in the hot loop.

If this fails, the interface boundary is wrong before proof design begins.

### E2: immutable-term floor

Record only the stable `TermId`/witness arena needed by any native proof design.
Do not record union causes or build proof nodes.

This isolates the irreducible cost of keeping syntactic identity. If it already
exceeds 1.10x, reuse existing row IDs more aggressively or abandon an
always-recording 5-10% target.

### E3: receipt-only floor

Record the smallest sound cause for native rule firings, unions, congruence,
merge, and rebuild. Do not extract, simplify, or verify a proof.

This is the decisive optimistic lower bound for "proofs always available at
5-10%." If it misses the gate, selector or extractor work cannot rescue the
capture cost.

### E4: one end-to-end witness

On a tiny fixture containing construction, a rewrite, congruence, and a custom
merge, reconstruct the existing proof format from receipts and validate it with
the independent checker. Compare exact propositions, not necessarily exact
pretty-print shape.

### E5: semantic expansion

Add containers, globals/scopes, input, delete/subsume, action lookups, tuple
outputs, and user indexes one family at a time. Every accepted family must flip
its current unsupported canary while preserving the existing normal corpus.

### E6: deletion gate

Delete the old source encoding only after:

- every non-failing corpus file uses the common path;
- all explicit proof fixtures validate;
- the six-file disabled-evidence suite stays within the agreed wall/RSS gate;
- proof-enabled overhead is reported separately from disabled overhead;
- the printed reference encoding, if retained, is not callable as a separate
  production execution mode.

## Decision

The current source-to-source term encoding cannot plausibly be tuned from
2.01-2.12x to 1.05-1.10x by deleting a few proof features. Reaching that band
requires removing the generated physical representation: duplicate tables,
query expansion, maintenance rules, schedule injection, and the second compiler
pass.

One execution path is nevertheless plausible and likely the best way to reduce
repo complexity. Build it from the native fast path, make equality/provenance
explicit in a typed encoding IR, and make evidence an optional sidecar. Use the
literal term encoding as the semantic oracle during migration, then delete its
production path while retaining a derived reference printer if the paper and
tests still need it.
