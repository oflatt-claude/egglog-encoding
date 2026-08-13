# Incremental PR roadmap to one engine

- Status: proposed sequence; no runtime implementation has started
- Date: 2026-08-12
- Baseline: `origin/main` at `5ead0a0cacf847a129294a870de13503f2d7f9c4`
- Architecture companions: [`term-encoding-unification.md`](term-encoding-unification.md)
  and [`encoding-architecture-bridge.md`](encoding-architecture-bridge.md)
- Current-main performance companion:
  [`term-encoding-overhead-breakdown.md`](term-encoding-overhead-breakdown.md)

## Outcome

There is a credible incremental route to one production engine with optional
proof evidence. It should not begin by replacing the native union-find with
today's ordinary-table `@UF` encoding. It should proceed in this order:

1. remove the second generated-program frontend;
2. erase proof-only data from the evidence-disabled plan;
3. make the evidence-disabled encoded operations lower to the existing native
   tables, relational union-find, and rebuild driver;
4. delete term-only as an independently executed production mode;
5. move proof evidence onto optional sidecars of those same operations;
6. delete the remaining source-generated proof executor one semantic family at
   a time.

The destination has one union-find, not a native UF plus a relational UF:

```text
logical Equivalence operation
        |
        v
EquivalenceTable                         one Table implementation
  parents: UnionFind<Value>              the only canonicalizer
  displaced: (child, epoch)              relational change stream
  reasons?: (left, right, cause, epoch)  optional proof sidecar
```

`DisplacedTable` already establishes the important precedent: it is relational
at the database boundary and specialized underneath. A proof reason sidecar is
not a second equivalence structure. It explains effective unions made by the
one structure.

The 5-10% target applies first to **evidence erased**. Full proof capture,
extraction, simplification, and checking must be measured separately. One
engine does not require proofs to be always recorded.

The current-main decomposition shows that the performance work cannot be one
serial "optimize UF" campaign. Math is maintenance-dominated, Pointer is
frontend-dominated, and Luminal is dominated by transformed user-rule
planning/search plus the generated frontend. The dependency order below still
removes the generated frontend before deleting an executor, but focused
performance PRs should proceed against the discriminator for their own cost
family rather than treating suite aggregate as one mechanism.

## What the two session investigations change

### The `single codebase` Claude session

The local Claude session
`7fd2857d-167e-48c1-9f0c-c3c5f42f97c6` correctly identifies the central
reframe:

- keep the encoding as the definition of logical semantics;
- treat specialized tables, union-find, and rebuild as a certified physical
  implementation of that encoding;
- do not equate "encoded" with "execute every administrative relation and
  maintenance rule literally";
- use a literal form as a differential oracle and paper artifact rather than a
  separately maintained production engine.

It also identifies useful current costs: term relations and `mint-*` have no
proofs-off reader, `Unit` payloads are dead in term-only mode, and the ordinary
table `@UF` duplicates the existing relational `DisplacedTable` facade.

However, the session's claimed pure-encoding floor of roughly 1.3-1.6x is not a
measurement. Its own adversarial critique calls that number a prior, observes
that Luminal's transformed-search regression had not been explained, and shows
that some proposed pre-frontend performance gates were arithmetically
unreachable while the second frontend remained. This roadmap therefore uses
the session for hypotheses and architecture, not as proof of a floor.

### The Luminal-overhead Codex session

The Codex session
`019ff6c4-f93d-70e0-9440-c2f3e97bc4fa` supplies two decisive corrections.

First, native Luminal's original "outside rulesets" number was partly an
accounting bug. PR
[#61](https://github.com/saulshanabrook/egglog-encoding/pull/61) records direct
experimental scheduler runs. Its six-round comparison left wall time unchanged
while changing the report from 6 to 16 recorded rulesets and reducing the
unattributed share from 97.39% to 55.45%.

Second, the remaining proof/term frontend cost is real and measured:

| Luminal typechecking component | Term-only | Proof generation |
| --- | ---: | ---: |
| All generated typechecking | about 187 ms | about 421 ms |
| Standalone actions and lets | about 104 ms | about 283 ms |
| Rules | about 66 ms | about 120 ms |
| Constraint solving | about 52 ms | about 135 ms |
| Primitive overload validation | about 32 ms | about 86 ms |

Source typechecking itself was only about 34 ms. The generated program's 1,634
large top-level lets accounted for about 69% of proof-mode typechecking and its
491 rules for another 24%. About 48% of typechecking leaf CPU was allocator or
memory-library work; `PrimitiveWithId::accept` appeared below about 20.5% of
the samples.

This changes the PR order. The first architectural performance PR should emit
typed generated actions, not optimize the UF. It both removes measured cost
and collapses a duplicated compiler path. Optimizing the general constraint
solver first would tune a path that the typed lowering is intended to delete.

Proof extraction has a separate small win: actual Luminal spent about 54 ms
gathering 1,634 globals while constructing `ProofStore`, then about 53 ms
gathering them again during `remove_globals`. Reusing that map should remove
one scan. The eggcc fixture instead needs later work on its large proof DAG;
its dominant extraction cost was proof-store conversion, not globals.

## Sequencing rules

Every production PR in the critical path should satisfy these rules:

1. **Name a deletion.** A new type or hook must identify the old parse,
   generated relation, maintenance rule, runtime branch, or proof row it
   replaces.
2. **Improve a live mode.** Except for the already-open accounting prerequisite
   and one paper-composition checkpoint, every PR must either produce a
   statistically supported runtime/RSS improvement or delete a production
   execution branch with identical performance.
3. **Keep exact mode labels.** Measure `off`, `term`, `proofs`,
   `proof-extraction`, and `proof-testing` separately. `proofs` means capture
   without automatic extraction or validation.
4. **One variable per benchmark.** Compare the same binary protocol, fixture,
   thread count, rounds, and report schema. Preserve anomalous samples.
5. **No generated-name peepholes.** Fusion consumes typed operations or origin
   metadata, never names such as `@UF_Math`.
6. **No generic recorder.** Proof capture records only the dynamic holes of a
   static proof skeleton. The causal-slicing recorder's optimistic Math floor
   was already 2.213x and its campaign added a large amount of code.
7. **Protect the disabled path.** Any proof infrastructure that makes `off`
   measurably slower has the wrong layout. A disabled policy should allocate
   nothing and should not add dynamic dispatch to row or union hot paths.
8. **Recheck parallelism before deletion.** The current evidence is
   single-threaded. The final evidence-erased path must preserve correctness
   and performance under the supported multithreaded configuration.

Each performance PR should carry a small ledger in its description:

| Item | Required entry |
| --- | --- |
| Baseline | exact base and candidate SHAs |
| Modes | exact treatment names |
| Workloads | focused discriminator plus six-file suite |
| Effect | wall ratio, RSS ratio, and relevant phase/ruleset delta |
| Semantics | proof/corpus parity result |
| Complexity | production lines added, replaced, and deleted |
| Decision | proceed, revise attribution, or stop |

## Recommended PR queue

The queue is deliberately front-loaded with changes that improve today's
encoded proof path even if the later fusion design changes.

| PR | Scope | Current overhead removed | Named deletion or replacement |
| --- | --- | --- | --- |
| P0a | Merge ruleset-accounting PR #61 (complete in `5ead0a0`) | none; makes direct scheduler attribution sound | old outer-only report accumulation |
| P0b | Report rule assembly and disjoint frontend/command stages | none; prevents the remaining residual from being misdiagnosed | wall-minus-rules inference as the primary diagnosis |
| P1 | Reuse proof globals during extraction | one roughly 53 ms Luminal global scan | second `gather_globals` traversal |
| P2 | Emit typed top-level generated actions | largest measured Luminal generated-typecheck bucket | action string generation, reparse, re-desugar, re-typecheck, and generated-global removal for that family |
| P3 | Emit typed generated rules, facts, and schedules | second-largest generated-typecheck bucket and repeated plan setup | corresponding source-string and untyped-command path |
| P4 | Emit typed declarations/merges and remove the second frontend | remaining generated parsing/typechecking and cloned-e-graph bookkeeping | cloned `original_typechecking` `EGraph` and the generated-program frontend loop |
| P5 | Erase proof-only storage under `NoEvidence` | term-row double writes, mint calls, and dead payload width | proofs-off term relations, `mint-*`, and `Unit` proof columns |
| P6 | Make evidence-erased functions/globals identity-lowered | Luminal program/query expansion and plan-construction work | duplicate views, rewritten user queries, and nullary-global view expansion under `NoEvidence` |
| P7 | Route evidence-erased equality through one relational UF | generic-table UF merges and about 43-48 ms Math path compression | per-sort ordinary `@UF` merge programs and `@parent` rules under `NoEvidence` |
| P8 | Route evidence-erased canonicalization through fused rebuild; retire term-only mode | about 382-397 ms Math encoded rebuild plus schedule overhead | generated rebuild/cleanup/subsume schedules and the independently executed term treatment |
| P9 | Add proof reasons to the same `EquivalenceTable` and migrate equality proofs | proof-valued UF rows, eager path proof composition | proof-mode ordinary `@UF`, compression proof rules, and equality proof-node rows |
| P10 | Replace proof term relations with an immutable `TermArena` | append-only per-derivation term rows and mint traffic | constructor/custom term relations and their mint primitives in proof mode |
| P11 | Attach static proof skeletons to the one typed rule plan | duplicated proof-instrumented rules and dynamic proof-node construction | proof rule copy and most proof-node relations |
| P12 | Migrate remaining semantic families and delete the source proof executor | family-specific encoded maintenance and support gates | `ProofInstrumentor` production execution, `proof_check_program`, and representation-only rejections |

P0 and a later minimal slotted-plus-proof composition test are the only planned
PRs that do not directly reduce overhead or delete an execution branch.

## PR details and gates

### P0a: merge accurate direct-ruleset accounting

PR #61 merged in `5ead0a0cacf847a129294a870de13503f2d7f9c4`. It is an
observability prerequisite, not a performance result.

The corrected Luminal benchmark is the canary: wall time should remain
statistically unchanged while all 16 native rulesets remain visible and no
ordinary schedule is double-counted.

### P0b: make the remaining overhead additive

Add per-ruleset Assembly before Search and split outside-ruleset time into
exclusive leaves under Lowering (Parse, total Typecheck, Other) and Commands
(Install, Actions/input, Other/schedules), plus a derived residual. Total
Typecheck intentionally combines source and generated checking so the
off-versus-encoded delta answers how much checking the encoding added. The
source pass performed in the separate original-typechecker e-graph must still
be charged to that outer total rather than leaking into Lowering / Other.

The acceptance artifact is the additive six-file table in
[`term-encoding-overhead-breakdown.md`](term-encoding-overhead-breakdown.md):
the named buckets plus residual must reconstruct process wall time, and the
instrumentation itself must have no detected material tax. Keep this PR scoped
to timing; do not combine it with the shared-globals behavior change from the
larger phase-timer prototype.

### P1: reuse globals during proof extraction

Compute the globals environment once for the requested proof and pass or own it
through proof-store construction and global removal. The ownership boundary
should make staleness impossible; this should not become a general cache keyed
by program identity.

Gate:

- actual Luminal `proof-extraction` loses one roughly 50 ms scan;
- `proofs` is unchanged, because it performs no extraction;
- eggcc proof-extraction does not regress;
- all proof snapshots and strict proof tests pass.

This is a useful warm-up but is not on the core unification dependency chain.

### P2: typed top-level actions first

Introduce the smallest private generated-program builder needed to construct
resolved variables, calls, expressions, and `ResolvedNCommand::CoreActions`.
Keep declarations on the old path temporarily, but let declaration processing
return the `FuncType` and resolved primitive handles the typed action builder
needs.

Do not introduce a public general-purpose IR yet. A transitional mixed command
enum is acceptable only if P4 names and deletes it. The invariant owned by the
builder is meaningful: every generated declaration is registered exactly once,
and every emitted call refers to that registered typed object.

Gate:

- the 1,634-action Luminal category no longer enters the general constraint
  typechecker a second time;
- the proof-generation wall-time CI shows a real improvement;
- term-only also improves;
- emitted behavior and proof propositions are unchanged;
- the PR deletes the old top-level action parse path at its converted call
  sites.

The observed bucket suggests a large win, but no percentage should be promised
until the branch is measured. If the improvement is much smaller than the
removed 104/283 ms typecheck buckets, profile before P3 rather than optimizing
the constraint solver by assumption.

### P3: typed rules, facts, and schedules

Construct `ResolvedRule`, resolved facts, and resolved schedules directly.
Preserve rule name, ruleset, evaluation mode, `no_decomp`,
`include_subsumed`, source origin, and the existing proof-head/skeleton layout.
Continue to feed the existing typed-to-core rule machinery so groundedness,
canonicalization, duplicate-variable removal, and rule installation are not
reimplemented.

Gate:

- the 491-rule Luminal category no longer runs the second general typechecker;
- generated rule typechecking falls by approximately the measured category,
  subject to a fresh profile;
- rule plans and canonical database results match;
- the converted rule/fact/schedule string builders are deleted.

### P4: typed declarations and deletion of the second frontend

Finish typed emission for sorts, functions, indexes, merge bodies, and
remaining commands. Separate source type information from target declaration
registration, but do not retain a cloned `EGraph` just to hold the source type
environment.

At the end, the pipeline should be:

```text
source parse/desugar/typecheck once
  -> typed encoding artifact
  -> typed declarations/rules/actions registered and run directly
```

Delete the loop in `EGraph::resolve_command` that turns each generated command
back into an unresolved command, desugars it, typechecks it, and removes globals
again. Delete the cloned typechecking-e-graph chain once callers use the typed
artifact.

Gate:

- no generated command is reparsed or passed through the general typechecker;
- normal source diagnostics remain source-oriented;
- Luminal and eggcc frontend time falls materially;
- the full support/proof corpus and `make check` pass;
- net production LoC for the frontend split is down, not merely moved.

### P5: evidence-erased storage diet

Make proof evidence an explicit compile-time plan policy. Under `NoEvidence`:

- do not declare or populate immutable term-node relations;
- do not register or call `mint-*` row primitives;
- do not add a `Unit` proof column to views or UF relations;
- let a view/table allocate its default e-class with the same `FreshId`
  mechanism used by native constructors.

Under `ProofEvidence`, preserve current behavior until P9/P10 replace it. This
temporary policy split is acceptable because it is a staged erasure in one
typed artifact, not two source frontends.

Focused gates:

- Herbie and Hardboiled wall/RSS, where per-firing build cost should be visible;
- eggcc RSS and total term rows;
- Luminal user-rule search, to test whether row/schema width contributes to its
  expansion cost;
- no change to proof generation or checking.

If build-heavy workloads barely move, revise the overhead ledger before adding
new storage features.

### P6: evidence-erased identity lowering

Under `NoEvidence`, one source function should use one physical function table.
The logical term relation and canonical view may remain distinct in the typed
reference artifact, but fusion maps them to the same table. User rule bodies
must therefore keep the original narrow atom shape. Source globals should use
the common `remove_globals` lowering rather than gaining an additional term
relation, FD view, index, and rebuild rule.

This is the decisive Luminal PR. The current transformed user search is about
475-477 ms versus about 5.3-5.7 ms in `off`, while generated maintenance is only
a few milliseconds. A successful identity lowering should make the same user
rules compile to the same physical query shape.

Gate:

- compare ruleset-by-ruleset search, not only whole wall time;
- the evidence-erased user rules are physically shape-equivalent to normal;
- generated rule/index counts for globals disappear;
- if Luminal user search remains more than 2x native, stop and inspect the
  remaining plan difference before touching the UF.

### P7: one relational UF for evidence-erased execution

Introduce a typed `Equivalence` operation and lower it to the existing
`DisplacedTable`/`UnionFind<Value>` implementation. The database continues to
see a table-shaped interface and a displaced-value change stream. The encoder
no longer emits an interpreted ordering merge or a path-compression rule under
`NoEvidence`.

This PR should prepare, but not prematurely implement, the proof contract:
`union(left, right, optional cause)` and an effective-union event. It must not
add a second parent forest or allocate reasons when evidence is disabled.

Gate:

- `@parent` disappears from evidence-erased reports;
- Math improves from removal of its roughly 43-48 ms path-compression ruleset
  plus interpreted UF merge overhead;
- min-id leader, push/pop, extraction, and update semantics match;
- off-mode code generation and performance remain unchanged.

### P8: fused rebuild and retirement of term-only execution

Lower the typed canonicalization operation to the existing container-first
bulk rebuild/fixpoint driver. Under `NoEvidence`, delete generated occurrence
declarations, row-rewrite rules, cleanup/subsume schedules, and trailing
maintenance schedules. The literal typed artifact can still print those
logical operations for the paper or differential oracle.

At this point evidence-erased encoding should be physically identical to the
current normal path. Make `term` an alias temporarily only if needed to prove
that identity, then delete it as a production treatment and CLI execution
choice. Retain a test-only literal interpreter configuration if it pays for its
maintenance through the differential oracle.

Deletion gate:

- evidence-erased wall and RSS are within 1.05x on every suite file and the
  aggregate CI contains 1.0;
- canonical database parity holds for the corpus;
- multithreaded parity and performance pass;
- no production command dispatcher chooses between normal and term-only
  programs;
- the PR deletes more production path code than it adds.

If this gate fails despite supposedly identical physical operations, another
hidden path remains. Do not loosen the target to bless it.

### P9: proof-capable relational UF, without a second UF

Extend the same `EquivalenceTable` with a `ProofEvidence` policy. On an
effective union, append a compact reason event naming the two pre-union leaders,
the chosen leader, a `CauseId`, and the epoch. Canonical `find` still consults
the one native UF. Path compression is a storage optimization and does not
create proof nodes.

Reconstruct equality explanations lazily from the reason forest and lower them
to the existing `ProofStore`/checker format. The first acceptance case is:

```text
insert a, b, f(a), f(b)
record a = b by a source rule or fiat
derive f(a) = f(b) by congruence
materialize the explanation
accept it with the current independent checker
```

Then migrate the current proof `@UF` users and delete proof-valued parent rows,
`Trans`/`Sym` nodes created solely for compression, and the encoded parent
rules.

Gate:

- one physical `UnionFind<Value>` exists;
- `NoEvidence` remains binary/performance neutral;
- all equality and congruence proof fixtures validate;
- proof-generation Math improves before proceeding to term storage.

### P10: immutable terms as an arena, not ordinary rows

Proofs need stable syntactic identity after e-classes move or rows are deleted.
They do not require one append-only database row per derivation attempt. Add an
immutable, hash-consed `TermArena` used only by `ProofEvidence`:

```text
TermId -> constructor and child TermIds
row/eclass -> witness TermId
CauseId -> source rule, merge, congruence, or fiat receipt
```

Move constructor and custom-row proof reconstruction onto this arena, then
delete proof-mode term relations and `mint-*` primitives.

Gate on proof-generation and proof-extraction separately. Eggcc wall/RSS is the
important discriminator because its large proof DAG, not global scanning,
dominates extraction.

### P11: one rule plan with an optional proof skeleton

Preserve the current good idea: the static proof shape is known when a typed
rule is compiled. Attach that skeleton and source origin to the one normalized
rule plan. Under `ProofEvidence`, a successful firing records only the stable
row/term/cause IDs needed to fill its holes. Under `NoEvidence`, the plan has no
holes and emits no receipt.

This is deliberately not a general causal journal. It does not record arbitrary
history and later search for a proof; the proof compiler specifies exactly
which dynamic values are needed.

Delete the duplicate proof-instrumented rule, proof-node relations replaced by
the skeleton/receipt pair, and eventually the duplicated command stream used
only by checking.

Gate:

- exact proof propositions check even if pretty-printed proof shape changes;
- full eggcc 2mm proof-validating performance is reported distinctly from
  capture-only and extraction-only results;
- disabled execution remains unchanged;
- net production LoC trends downward against the frozen encoder baseline.

### P12: family-by-family migration and final deletion

Do not put the long tail in one PR. Use separate deletion-backed PRs for:

1. custom functions and merge bodies;
2. containers and normalization receipts;
3. input, globals, scopes, push/pop, and the Rust API;
4. delete, subsume, user indexes, and extraction;
5. remaining primitive and tuple-output cases.

Each family PR must remove its old encoder branch and at least one
representation-only unsupported reason. Once the corpus and proof gates pass,
delete production execution through `ProofInstrumentor`,
`proof_check_program`, the cloned proof program, and the proof/term dispatcher.

The surviving proof assets should be the proof algebra, `ProofStore`,
simplifier, extractor/materializer, independent checker, typed skeletons,
origin maps, and the derived reference printer.

## Slotted composition checkpoint

After P11 proves that one typed rule plan can carry a source origin and proof
skeleton, add a narrow paper checkpoint before broad P12 migration:

1. lower one slotted rule requiring a non-identity renaming;
2. run the proof pass after the slotted pass;
3. execute the fused plan;
4. extract a proof whose interpretation names the source slotted rule and
   substitution;
5. compare it with the literal typed encoding and validate it.

This PR may not improve runtime. Its purpose is to prevent a fast proof-only
architecture from invalidating the paper's actual composition claim. It should
not grow a second interpreter or generic provenance framework.

## Why this order is preferable to the alternatives

### Do not start with the UF

UF work is important for Math, but it cannot explain Luminal's dominant
transformed user search or the generated frontend. Starting there would improve
one component while leaving the two largest cross-workload sources intact.

### Do not start by optimizing the constraint solver

The solver and primitive overload validation are hot, but almost all of their
proof/term delta comes from typechecking generated commands a second time. Typed
emission removes that work and reduces code. Solver caching is a fallback only
if source-program typechecking remains material afterward.

### Do not tune the literal source encoding all the way to 10%

P5 is a useful measured erasure experiment. P6-P8 intentionally stop treating
the literal tables and maintenance rules as the production representation.
Specialized relational storage is not a betrayal of the encoding; it is the
physical lowering that makes the encoding viable.

### Do not revive the slicing recorder for proofs

The slicing campaign showed both the code and capture cost of a broad execution
journal. P9-P11 instead record local, typed causes and only the holes required
by known proof skeletons.

## Complexity ledger

Freeze these current baselines before P2:

- encoder-facing production modules
  (`proof_encoding*`, `proof_head`, `proof_fresh`, and
  `proof_container_rebuild`): about 6,999 lines;
- the full `egglog/src/proofs` production directory excluding
  `proof_tests.rs`: about 11,949 lines;
- `DisplacedTable`: 517 lines, much of which remains as the one physical UF;
- current unsupported-reason count and excluded corpus files;
- command-dispatch branches and benchmark/test treatments.

Do not score moved native UF/rebuild code as deletion merely because it gets a
more general name. The meaningful complexity wins are:

- one source typecheck and one target registration path;
- one physical function table per source function when evidence is erased;
- one physical UF and rebuild implementation;
- one normalized rule plan;
- no production execution of generated source;
- fewer support gates and test-matrix axes;
- net production LoC reduction by the final P12 gate.

## Stop rules

1. If P2 does not recover a substantial portion of the measured generated
   action typecheck bucket, stop and re-profile before P3.
2. If P6 does not collapse Luminal's transformed user search, do not infer that
   UF or rebuild work will rescue the 10% target.
3. If P8 cannot make evidence-erased execution physically and measurably
   equivalent to normal, do not delete the normal dispatcher.
4. If P9-P11 proof capture misses the accepted proof-enabled gate, keep
   evidence optional. This does not invalidate the one-engine design.
5. If any evidence hook taxes `off`, move the policy choice to plan
   construction/monomorphization or a separate build; do not accept a permanent
   5-10% tax merely because it is inside the target band.
6. If a new abstraction grows faster than the old family it replaces, stop the
   broad migration and retain the typed reference artifact plus current native
   lowering.

## Recommended immediate next action

Land **P0b, additive phase reporting**, next. Then make **P2, typed top-level
action emission**, the first architectural PR. P1 can land independently as a
small extraction cleanup.

P2 is the best first commitment because it is simultaneously:

- supported by a clean profile;
- useful to term and proof modes;
- a reduction in compiler duplication;
- required by any typed encoding/fusion paper story;
- independent of the unresolved proof-storage design;
- a way to establish the builder and measurement discipline needed for every
  later PR.

In parallel, use eggcc as the discriminator for a narrowly scoped
ruleset-assembly experiment: generated `@rebuilding`/`@parent` assembly is
about 253 ms there. Do not assume typed emission alone removes that
per-invocation assembly cost.

Only after P2-P4 should the project choose exact Rust APIs for the relational
UF sidecar. That keeps the UF design grounded in the typed artifact that will
actually call it, instead of preserving assumptions forced by today's
generated source schema.

## Source basis

- Current source at the pinned baseline, especially `EGraph::resolve_command`,
  `ProofInstrumentor`, `DisplacedTable`, the bridge rebuild driver, and the
  typed/core rule lowering.
- Local Claude session `7fd2857d-167e-48c1-9f0c-c3c5f42f97c6`, titled
  `single codebase`, including its research workflow output
  `wvkzpajc3.output`.
- Local Codex session `019ff6c4-f93d-70e0-9440-c2f3e97bc4fa`, including the
  Luminal phase/typechecking profile and PR #61.
- `/tmp/term-encoding-always-on-bd4752e.jsonl`, the same-binary current-main
  benchmark cache described in `term-encoding-unification.md`.
- `/Users/saul/Downloads/egglog encoding project.md`, for the paper's directed
  slotted-then-proof composition goal.
- `/Users/saul/p/wt/egglog-encoding/pr42-agent-causal-slice-logical-v1/SLICING-CAMPAIGN-REPORT.md`,
  for the generic-recorder complexity and capture-floor stop evidence.
