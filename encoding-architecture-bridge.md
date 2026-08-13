# Encodings as semantics, fusion as engineering

- Status: draft architecture note for paper and maintainer review
- Date: 2026-08-12
- Audience: egglog maintainers and the encoding-paper authors
- Baseline: `origin/main` at `5ead0a0cacf847a129294a870de13503f2d7f9c4`
- Implementation permission: none; this document proposes experiments and gates
- Companion: [`term-encoding-unification.md`](term-encoding-unification.md)
- Incremental PR sequence:
  [`incremental-unification-pr-roadmap.md`](incremental-unification-pr-roadmap.md)
- Current overhead decomposition:
  [`term-encoding-overhead-breakdown.md`](term-encoding-overhead-breakdown.md)

## Executive decision

Do not choose between the paper's encoding story and a fast, single-path
implementation. Separate two things that the current implementation conflates:

1. An **encoding is a semantic compiler pass**. It translates a program in an
   extended language to a smaller logical language, carries an origin map, and
   has a correctness argument. Proofs and slotted e-graphs remain encodings in
   this sense and compose in a specified order.
2. A **literal encoded program is only one physical implementation** of that
   pass. Production egglog should stage and fuse the encoded operations into
   its native tables, union-find, rebuild indexes, and compact evidence arenas.
   It should not materialize every administrative relation and then execute the
   generated maintenance rules as ordinary user rules.

The proposed end state is therefore:

```text
surface program
    |
    | E_slot (when slotted semantics are requested)
    v
typed core program + slot interpretation
    |
    | E_proof (when proof production is requested)
    v
typed encoded program + origin map + optional proof skeletons
    |
    | normalize, erase unused decorations, and fuse
    v
one native physical plan
    |
    v
one execution engine
```

For the paper, the typed encoded program can be printed as ordinary core
egglog and run as a reference semantics. For production, the same artifact is
lowered to a fused plan. The printer is not a separately maintained executor or
a second frontend.

This permits an honest use of the word *encoding*: the logical translation is
always the source of semantics, while compiler correctness justifies executing
an optimized implementation of it. Compilers do not stop being compilers when
they fuse intermediate allocations away.

## What should be deleted, and what should survive

The goal is not to delete the idea of term, proof, or slotted encoding. It is to
delete independent implementations of the same language semantics.

### Delete from the production path

- the cloned typechecking `EGraph` and second desugar/typecheck pipeline;
- source-string or source-AST expansion as a prerequisite for execution;
- term-only and proof modes as separately executed egglog programs;
- proof-disabled `Unit` columns threaded through all generated tables;
- generated term/view/`@UF` tables when the native table and union-find already
  store the same logical information;
- generated occurrence indexes, path-compression rules, rebuild rules, cleanup
  rules, subsumption rules, and schedule injection;
- proof nodes stored as ordinary database rows when a compact side arena or
  rule-firing receipt is sufficient;
- `proof_check_program` as a second full command stream;
- backend-selection and lowest-common-denominator abstractions if the project
  is in fact removing the alternate backends;
- generic always-on provenance or causal-slicing infrastructure as the
  foundation for proofs.

### Keep as semantic and validation assets

- the pure equality, proof, and slotted translations;
- the equations and invariants currently documented by the term encoding;
- a deterministic printer for the typed encoded IR, usable by paper examples,
  differential tests, and debugging;
- the proof algebra, simplifier, extractor, and independent checker;
- proof skeletons and stable source-rule identities;
- slotted renamings, symmetry/group checks, and an explicit account of fresh
  slots;
- origin and interpretation metadata that maps compiled rules and
  substitutions back to the source language;
- literal-vs-fused parity tests.

The reference printer may live in the repository, a paper-artifact crate, or a
test-only feature. That packaging choice is secondary. It must be derived from
the same typed pass result, rather than becoming a second implementation that
can drift.

## What "one execution path" means

One path does not mean one feature-free IR node or one enormous interpreter.
It means:

- one parse, resolution, normalization, and typechecking pipeline;
- one representation of each source rule and function declaration;
- one physical table implementation, union-find, rebuild implementation, and
  scheduler;
- optional compile-time decorations for slots and proofs;
- optional evidence storage selected at monomorphization or plan construction,
  with a zero-cost `NoEvidence` form;
- no runtime branch that sends a whole program through an independently
  maintained semantics.

The fast native mechanisms do not disappear. Their role changes: they become
the physical lowering of the encoding rather than an independent definition of
surface egglog.

Likewise, proof production can remain optional without becoming a second path.
A proof-enabled rule is the same normalized rule with a proof plan attached;
it is not a second rule parsed and typechecked in another `EGraph`.

## A typed encoding contract

The smallest useful contract is not a generic backend trait. It is a compiler
artifact with four pieces:

| Piece | Purpose |
| --- | --- |
| Logical program | The actual target-language declarations, rules, actions, and schedules |
| Origin map | Source declaration/rule/action responsible for every generated item |
| Interpretation | How target values, substitutions, and observations map back to the source language |
| Invariants | Facts a physical lowerer may rely on and must preserve, such as canonical views or total slot maps |

An encoding pass consumes one typed language and produces another typed
language plus this metadata. Its output language must be the next pass's input
language. That makes pass ordering explicit and makes invalid compositions fail
at the compiler boundary rather than in generated source.

The compiler should preserve administrative operations as typed nodes or typed
annotations long enough for fusion. It must not ask the lowerer to rediscover
them from generated names such as `@UF_Math` or `@AddView`. Name-based
peepholes would retain the entire source generator and introduce a hidden third
path.

For rules, the conceptual result is:

```text
normalized rule
  + source origin
  + optional slot match/action plan
  + optional proof skeleton
  -> one executable rule plan
```

This is a conceptual record, not yet a proposed Rust API. The vertical-slice
experiment should determine which fields are real and which can be derived.

## Directed composition: slotted first, proofs second

The project notes already answer the commutativity question: the passes do not
commute; proofs should run after the slotted encoding. That is not a failure of
composition. Composition means that the codomain of the slotted pass is in the
domain of the proof pass:

```text
E_slot  : SlottedEgglog -> CoreEgglog + SlotInterpretation
E_proof : CoreEgglog    -> ProofCoreEgglog + ProofInterpretation

E_both(P) = E_proof(E_slot(P))
```

This order is substantively useful:

- the slotted pass makes the paper's `beta` and `mp` explicit in rule matching;
- it lowers a union of renamed ids into the base operations that implement it;
- the proof pass then records the actual compiled premises and actions;
- a single rule firing can carry both the slot witness and proof skeleton;
- proof extraction can interpret that firing through both origin maps to name
  the original source rule and source-level substitution.

Arbitrary pass permutation should not be a paper claim. A stronger and more
defensible claim is **typed, directed composition with an interpretation
theorem**.

### The correctness obligations

The paper needs to separate four properties that are easy to blur:

1. **Proof erasure.** Erasing proof decorations from `E_proof(Q)` has the same
   observations as running `Q`.
2. **Proof soundness.** Every extracted proof denotes a valid equality in the
   semantics of `Q`.
3. **Slotted preservation.** Interpreting the observations of `E_slot(P)` gives
   the observations of slotted program `P`.
4. **Physical refinement.** Running the fused physical plan gives the same
   observable result as running the literal encoded core program.

Schematically:

```text
observe(run_core(E_both(P)))
  == observe(run_fused(lower(E_both(P))))

decode_slot(erase_proof(observe(run_core(E_both(P)))))
  == observe_slotted(P)
```

The second equation gives semantic composition. It does **not** by itself give
a pleasant source-level proof. For that, the proof interpretation must map an
encoded rule firing and its renaming witness back to the source slotted rule.
That resugaring/interpretation lemma is a real paper obligation, not metadata
that can be reconstructed after execution.

## Why the current proof skeleton is the right precedent

The existing proof design already has a valuable specification/implementation
split:

- layer 1 describes the proof that would be built as the rule executes;
- layer 2 emits a compact proof skeleton and reconstructs layer 1 later.

The next engineering step is not to abandon that encoding. It is to stop
storing the skeleton, term identities, and proof nodes as ordinary egglog rows
when the production engine can retain them more compactly.

In the proposed architecture:

- layer 1 remains the declarative proof specification used in the paper;
- the typed proof pass derives a skeleton from a normalized rule;
- the fused rule plan stores the static part of that skeleton once;
- a firing records only the dynamic holes that the skeleton needs;
- extraction materializes the existing proof algebra on demand;
- `NoEvidence` erases the skeleton holes and all per-firing writes.

This is partial evaluation of the proof encoding, not a different proof
semantics.

## How the literal equality encoding should fuse

The current term encoding makes several logical objects explicit. A native
lowerer can recognize the typed objects directly and implement them with one
physical structure:

| Logical encoded object | Fused production representation |
| --- | --- |
| term relation plus canonical view | native constructor/function table, with optional stable `TermId` sidecar |
| explicit per-sort `@UF` | native union-find |
| view collision merge | native congruence/rebuild event |
| occurrence relation/index | native rebuild occurrence index |
| parent/rebuild/cleanup schedule | native commit and rebuild loop |
| `Unit` proof column | erased |
| proof-valued column | compact `CauseId` or receipt sidecar |
| proof-node relations | append-only proof arena materialized on demand |
| generated rule proof | static skeleton plus firing-hole bindings |

Reaching 5-10% requires essentially all of these fusions. The current
term-only measurements show that frontend cleanup alone is not enough: the
literal relational representation changes row widths, query shapes, write
counts, and maintenance work.

It is therefore plausible for **encoded semantics with evidence erased** to be
within 5%, because it can lower to nearly the same physical operations as
normal mode. It is not currently plausible for the literal encoded program to
reach that range, nor is there evidence that **always retaining arbitrary proof
evidence** can do so.

## Slotted-specific implications

The current slotted rule design is already naturally compiler-shaped: it
computes the paper's `beta` and `mp`, turns each user variable into a leader plus
renaming, and distinguishes fully bound group lookups from genuine
`find-mapping` joins.

The typed pass should preserve those distinctions. In particular:

- a known symmetry membership test should stay a lookup, not be expanded into
  an enumerating join and then rediscovered by an optimizer;
- extension of `mp` is a real solver operation and should remain explicit;
- union acts on renamed ids, so its origin and renaming witness must survive
  into proof interpretation;
- fresh-slot completion must be solved before claiming a complete slotted
  encoding;
- the self-edge/group invariant must be stated at phase boundaries, because
  the current machinery can expose transient derived facts inside maintenance.

Some slotted operations may remain relational in the first fused engine. The
architecture does not require every encoding feature to have a native data
structure on day one. It requires one execution plan and an explicit boundary
where a measured hot logical operation can later receive a specialized
physical implementation.

## Why generic slicing/provenance is not the shared substrate

The slicing campaign is a useful negative architecture experiment.

It found that a general recorder plus post-hoc causal reconstruction:

- added roughly 9,820 lines of provenance recording and 5,300 lines of slicing
  including tests, with about +26,182 production lines at PR time;
- still had a witness-free capture floor of 2.213x normal on the decisive Math
  experiment;
- required reasoning about row lifetimes, deletes, merge boundaries,
  containment, replay identity, and pre-event equality denotation;
- did not become small merely because "any valid support" replaced exact
  historical support.

That does not mean receipts are unusable. It means proof production should not
be implemented as arbitrary execution history followed by a generic graph
query. The proof compiler already knows the rule, its static proof skeleton,
and the exact dynamic holes it needs. Record those holes locally at the rule
and equality-effect boundaries.

The slicing lesson should become an architectural constraint:

> No generic recorder, replay engine, or second interpreter may be added to
> support the first proof/slotted vertical slice.

Slicing can remain out of scope, or later consume an explicitly bounded receipt
interface as a debug feature. It must not define the common runtime substrate.

## Removing backends changes the paper story

The older paper pitch used a cross product of expressive features and
performance backends, then claimed that one encoded program was portable over
several backends. If DuckDB, Differential Dataflow, and slicing are being
removed, that claim should be removed rather than simulated by abstractions in
main.

The replacement story is tighter:

1. E-graph extensions such as proofs and slotted matching normally cut across
   matching, actions, equality, rebuild, extraction, and printing.
2. Expressing each extension as a typed semantic encoding localizes its
   definition and makes their order of composition explicit.
3. Literal execution establishes an executable reference semantics.
4. Staging and fusion recover the specialized performance of one production
   engine without reintroducing a second language implementation.
5. The implementation is evaluated on semantic parity, composition,
   performance, and net production complexity.

This changes "portability across backends" into **portability of extension
semantics across physical representations**, demonstrated here by a literal
reference execution and one fused execution. If that wording sounds too much
like two backends, omit portability entirely and call the contribution
*composable encodings with semantics-preserving fusion*.

The paper should not claim that encodings eliminate all extension-specific
engineering. Each encoding still needs a pass, a correctness argument, and
possibly a physical optimization. The claim is that this work is localized and
composes at a declared boundary instead of multiplying through the core.

## Candidate paper claims and evidence

| Claim | Required evidence | Current state |
| --- | --- | --- |
| Proofs and slotted semantics are separate encodings | formal definitions plus executable reference translations | proof translation exists; slotted user-rule translation is incomplete |
| The encodings compose | runnable `E_proof(E_slot(P))`, directed composition theorem, source interpretation | not yet demonstrated |
| Fusion preserves the encoding | differential/reference tests plus a physical-refinement argument | absent; proposed work |
| Fusion recovers near-native performance | same-binary literal vs fused vs current-normal benchmarks | absent; current literal term mode is 2.01-2.12x |
| Main becomes simpler | net production LoC, deleted paths, fewer core touchpoints and support gates | absent; must be measured, not asserted |
| Proofs remain independently checkable | existing checker validates source-interpreted composed proofs | checker exists; composed interpretation absent |

The paper can succeed without 5-10% proof-enabled overhead. A defensible
performance result would report three distinct costs:

- fused encodings with evidence erased;
- fused proof evidence capture, without extraction;
- proof extraction, simplification, and checking.

Only the first is the gate for deleting the normal semantic path. Conflating it
with always-on proof capture would make the engineering decision depend on a
much stronger and currently unsupported performance claim.

## Complexity budget and stop rules

One engine is not automatically a smaller repository. A typed IR, origin maps,
fusion, and a reference printer can themselves become a large parallel system.
The work should therefore use deletion-backed gates:

1. **Every production abstraction names the old code it will delete.** A new
   pass field or runtime hook is not accepted merely because it may be useful.
2. **No second interpreter.** The reference form is printed from the same typed
   artifact and run only by the existing core semantics in tests/artifacts.
3. **No generated-name peepholes.** Fusion operates on typed provenance or
   typed operators.
4. **No generic provenance substrate.** The first slice records only holes
   demanded by its static proof skeleton.
5. **One vertical slice before broad coverage.** Stop if the slice adds more
   production machinery than the old slice it demonstrably replaces.
6. **Keep a running LoC ledger.** Separate production, tests, reference
   semantics, and documentation. A smaller core cannot be inferred from a
   smaller file count.
7. **Delete as the migration proceeds.** Do not defer all deletion until every
   feature is supported; use narrow internal seams so completed families stop
   exercising the old path.
8. **Re-measure on every architectural checkpoint.** The slicing campaign
   showed that stale cost attribution can steer days of design in the wrong
   direction.

The final deletion gate should require:

- one frontend/typechecker and one runtime dispatcher;
- one physical equality/rebuild implementation;
- no production execution of printed encoded source;
- no support gate whose only reason is representational inability of the old
  generator;
- net production LoC reduction relative to the frozen baseline, or an explicit
  maintainer decision that a measured complexity increase is worth the result.

## Falsifying implementation sequence

### A0: settle the semantic boundary

Write down the source and target languages of `E_slot` and `E_proof`, their
observations, pass order, and interpretation maps. Decide whether the composed
proof must name source slotted rules or whether a proof of the compiled core
program is sufficient.

Stop if the paper team cannot agree on this: the implementation cannot repair
an ambiguous theorem statement.

### A1: one typed reference artifact

Change no runtime behavior. Make one tiny constructor/rewrite example produce a
typed encoded artifact from which the current literal core program can be
printed. The artifact must retain source origins without parsing generated
names.

Gate: printed output behaves exactly like the existing term/proof encoding and
the existing proof checker accepts its proof.

### A2: fuse one equality/proof vertical slice

Lower the same artifact directly to the existing native constructor table,
union-find, and rebuild path. Attach one static proof skeleton and record only
its dynamic firing holes under `ProofEvidence`.

Gates:

- literal and fused observations match;
- the source-interpreted proof checks;
- `NoEvidence` makes no per-row allocation and adds at most 5% wall time/RSS on
  the microcase and a representative existing benchmark;
- the diff includes a named deletion or replacement of the corresponding old
  execution branch.

### A3: measure the proof-capture floor

Record stable terms and the minimal sound rule/equality receipts, but do not
extract or simplify proofs. This is the optimistic lower bound for proof
availability.

Do not set 5-10% proof-enabled overhead as a project promise unless this floor
meets it. If it misses, keep evidence optional and proceed with the one-path
design.

### A4: compose a minimal slotted proof

Use a program that needs a non-identity renaming and a repeated-variable group
membership check. Run `E_slot` then `E_proof`; compare the literal and fused
forms; extract a proof that names the source rule and carries enough renaming
evidence to check.

This is the decisive paper slice. Do not begin broad slotted benchmarks until
it works.

### A5: close known slotted semantic gaps

Implement and validate fresh-slot completion, settle the phase-boundary group
invariant, and differential-test the translation against the slotted-egraphs
reference implementation. These are correctness gates, not optimization work.

### A6: migrate semantic families and delete the split

Move globals/scopes, containers, input, custom merge, delete/subsume, user
indexes, primitives, and extraction one family at a time. Each family must add
parity tests, remove its representation-only rejection, and stop using the old
production path.

After corpus and proof gates pass, remove the production term/proof execution
mode. Retain only the derived reference printer and paper/test artifacts.

## Architecture alternatives

| Alternative | Paper fit | Performance | Complexity outcome | Verdict |
| --- | --- | --- | --- | --- |
| Execute today's literal term encoding universally | strongest superficial dogfooding | current evidence is about 2x term-only and about 3x proofs | deletes native semantics but retains a large generator and maintenance program | reject |
| Typed encodings plus semantics-preserving fusion | keeps encodings and directed composition central | can lower erased mode to current native mechanisms | can delete both independent production paths if deletion gates hold | recommend |
| Native extensible annotation/hook algebra | proofs and slots may share elegant metadata operations | potentially fastest | risks another broad core substrate and weakens the compiler-encoding paper | research alternative, not first slice |
| Paper artifact separate from production main | cleanest immediate main cleanup | production stays fast | paper and engineering may drift; no dogfooding claim | fallback if fusion fails its complexity gate |

## Open decisions

1. Must a composed proof name and validate the original slotted rule, or is a
   proof over the compiled core rule the paper's theorem? The former is much
   more compelling and requires an explicit interpretation lemma.
2. What exactly is `CoreEgglog` for the formalism? It should be small enough to
   state semantics, but not chosen as a lowest common denominator for backends
   that are being removed.
3. Is the literal printer shipped in main, test-only, or held in the paper
   artifact? It must not become a public execution mode by accident.
4. Which stable term identity is genuinely required under `NoEvidence`? Any
   always-present identity must earn its measured cost.
5. Can slot and proof plans share a firing substitution without widening every
   native binding row? This is a primary performance experiment.
6. What is the accepted production LoC outcome? "Less complexity" needs a
   frozen baseline and a measurable deletion target.
7. Is slicing fully out of scope, or a later debug consumer? It should not
   influence the first common interface either way.

## Knowledge-unit map

| ID | Knowledge unit | Kind |
| --- | --- | --- |
| KU-1 | The current paper direction is proofs plus slotted as composable encodings, with backends and slicing being removed from scope | project decision |
| KU-2 | The intended order is slotted then proofs; the passes do not commute | project decision |
| KU-3 | Literal term-only execution is far outside a 5-10% normal-path gate | measured fact |
| KU-4 | The proof design already separates a declarative layer from emitted skeletons | current design fact |
| KU-5 | The slotted rule translation makes `beta`/`mp` explicit but has unresolved fresh-slot and invariant questions | current design fact |
| KU-6 | General causal recording produced high overhead and a large production diff even after simplification campaigns | measured historical fact |
| KU-7 | Typed fusion can make encoded/no-evidence execution near-native | hypothesis to falsify |
| KU-8 | Composed proof interpretation can recover source-level slotted rules and substitutions | blocked design obligation |
| KU-9 | The architecture will reduce net production complexity | hypothesis to measure |
| KU-10 | Arbitrary proof evidence can always be retained within 5-10% | unsupported stronger hypothesis |

## Evidence matrix

| KU | Primary source | Status | Consequence |
| --- | --- | --- | --- |
| KU-1 | project meeting notes, Aug. 5-6; current maintainer direction | Convergent | remove backend portability and slicing from the central architecture |
| KU-2 | project meeting notes lines 102-142 | Convergent | specify typed directed composition, not commutativity |
| KU-3 | `term-encoding-unification.md` fresh same-binary benchmark | Convergent | do not attempt to tune the literal representation to 1.05x |
| KU-4 | `egglog/src/proofs/proof_encoding.md`, proof layers 1 and 2 | Convergent | preserve the semantic layer while changing storage/lowering |
| KU-5 | `slotted-user-rules.md`, fresh-slot gap and open questions | Convergent | composition claims remain gated on slotted correctness work |
| KU-6 | `SLICING-CAMPAIGN-REPORT.md` and its fresh capture-floor experiment | Convergent | prohibit generic recording/replay in the first architecture slice |
| KU-7 | no prototype or benchmark yet | Absent | A2 is a falsifying experiment, not an implementation commitment |
| KU-8 | meeting notes identify resugaring/composition difficulty; no theorem exists | Blocked | A0 must settle the source-level proof contract |
| KU-9 | no fused implementation or deletion diff exists | Absent | use an LoC ledger and named deletion gates |
| KU-10 | current term/proof and slicing capture measurements | Divergent | keep proof evidence optional unless A3 changes the evidence |

## Source basis

Highest-authority sources used for this note:

1. Current maintainer direction in this design discussion: proofs and slotted
   remain encodings that compose; alternate backends and slicing are being
   removed.
2. `/Users/saul/Downloads/egglog encoding project.md`, especially the Aug. 5-6
   notes on pass ordering, composition, paper claims, and removal of backends
   and slicing.
3. [`egglog/src/proofs/proof_encoding.md`](egglog/src/proofs/proof_encoding.md),
   the current equality/proof encoding and skeleton design.
4. [`slotted-user-rules.md`](slotted-user-rules.md), the current concrete
   slotted user-rule translation and its open semantic gaps.
5. [`term-encoding-unification.md`](term-encoding-unification.md), current-main
   benchmark and code-path evidence.
6. `/Users/saul/p/wt/egglog-encoding/pr42-agent-causal-slice-logical-v1/SLICING-CAMPAIGN-REPORT.md`,
   the slicing complexity/performance retrospective.

This note intentionally treats the fusion architecture, its performance, its
net LoC effect, and source-level composed-proof interpretation as proposals.
They are not established by the current sources.

## Review checklist

- Does the paper team agree that an encoding is the logical pass, not a mandate
  to execute its literal output?
- Is directed `E_proof(E_slot(P))` the intended meaning of composition?
- Is source-level proof interpretation required?
- Are backends and slicing definitively out of the central claims?
- Does A2 delete a named old path before any broad framework is built?
- Are disabled, capture-only, extraction, and checking costs reported
  separately?
- Does every complexity claim have an LoC/touchpoint measurement?
