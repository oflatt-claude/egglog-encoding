# Encoding passes

## Agreed plan and scope

This is the working plan for PR #58. The current priority is to separate mathematical
compiler correctness from the executable sanity checks:

- Add a top-level `check q`. It observes whether the complete query has a match, leaves
  the database unchanged on success, and stops the program on failure. Checks neither
  construct terms nor initiate a merge or rebuilding phase.
- Give finite evaluation the explicit results `Result.ok db` and `Result.checkFailed`.
  Failure short-circuits the suffix; divergence has no finite evaluation derivation.
- State congruence compiler correctness over mathematical `Database` states on both
  sides. For well-formed programs in the supported source fragment, every pair of
  terminating source/compiled evaluations must have the same success/failure observation.
  Establish query correspondence at command boundaries as the internal proof invariant.
- Interpreter correctness is outside the paper's obligations. Keep executable models
  and differential tests as sanity checks; do not route the paper theorem through
  `FDatabase` or an existential wrapper around executable target evaluation.
- **Stretch goal:** termination preservation. The required theorem assumes both
  evaluations terminate, counting a failed check as termination.

The existing theorem about an executable compiled target is retained during the port;
it does not discharge the new mathematical execution theorem.

The remaining pipeline responsibilities are:

1. **Port completeness to the mathematical congruence pass.** Establish the execution
   invariants and check correspondence above, retaining the constructor-only
   source fragment (`Program.Fragment`). The paper's completeness theorem ends
   here. The compiled target uses functions, but extending the theorem to arbitrary
   source merge functions is deferred.
2. **Implement a sound source proof checker.** Check explicit propositions against
   the original program, initially in the constructor-only source fragment.
   `Fiat` must be justified by original globals; it cannot
   introduce an arbitrary constructor or discharge an unproved rule premise.
   Congruence must preserve evidence that the enclosing application exists. Prove
   that accepted certificates imply their source propositions, including existence.
3. **Add a separate provenance pass.** Instrument the congruence-compiled program
   like Datalog provenance, extended to function entries and merges. Record evidence
   for global entries, rule firings, and merge-derived entries. Rule-created terms
   must have rule evidence, and merge-created entries must retain the evidence for
   both inputs and the merge computation. Do not hide these cases behind `Fiat`.
4. **Lift certificates back to the original program.** Recognize generated rebuilding
   rules by their origin tags and UF operations by the generated table name.
   Translate their justifications into source reflexivity, symmetry, transitivity,
   and anchored congruence, as appropriate. View collisions also require a source
   justification. For source rules, recover premises by walking the original query
   in exactly the compiler's recursive order, unflattening nested applications with
   congruence. Both algorithms receive the original query; there is no saved
   flattening tree. Validate that all generated names and maintenance rules have
   disappeared from the resulting source justification.
5. **Validate the whole pipeline.** Check the *same lifted certificates* with both
   Lean and Rust checkers. Running Rust's own encoder on the same inputs is useful
   comparison evidence, but does not establish this interoperability. Include
   negative tests for invented globals, missing existence premises, malformed rule
   substitutions, and incorrect equality endpoints, alongside positive tests for
   nested queries, repeated applications, rebuilding, UF chains, and function
   merges. Run the complete Lean, Python, and Rust validation suites.

The two compiler passes have separate responsibilities: congruence compilation
encodes rebuilding, union find, and query flattening without proof annotations;
provenance records how its resulting entries were derived. Proof lifting is a third
algorithm that interprets that provenance against the original source program.
The congruence output must contain no built-in unions and must execute without
implicit congruence or other equality axioms. Structural identity and existence
tests remain available. Provenance and lifting need soundness and validation;
they do not need their own completeness theorem for the paper.

This refactor targets the Lean model and encoding. Existing Rust certificate
formats and the Rust checker provide the interoperability target; rewriting the
Rust parser or runtime is outside the agreed scope. Source syntax has no lets,
and function entries use full table atoms such as `(LowerBound expr bound)` in
queries and evaluation. Function entries are not nested term values or union
operands. The constructor-only theorem scope does not remove functions from the
target or from provenance.

Stop and discuss an actual design blocker rather than weakening a theorem,
accepting unjustified proof premises, or silently broadening the source fragment.
Update the status below as each obligation is discharged. Intermediate commits
and pushes to the PR are authorized, including before the proofs are complete.

## Current implementation

The Lean refactor separates congruence compilation, provenance instrumentation, and proof
lifting. The congruence pass is implemented in
[Congruence/Encode.lean](EgglogSemantics/Congruence/Encode.lean), provenance in
[Provenance/Encode.lean](EgglogSemantics/Provenance/Encode.lean), and lifting in
[Resugar/Lift.lean](EgglogSemantics/Resugar/Lift.lean).

## Congruence compilation

`Egglog.Congruence.encode : Program → Program` compiles constructor-source programs into
explicit tables:

| Table | Atom | Meaning |
| --- | --- | --- |
| `@UF` | `(@UF t parent)` | An explicit parent edge |
| `@fView` | `(@fView children… id)` | The id of a source constructor application |

Each table has one output column. Structural constructor terms serve as ids. Building
`f(cs…)` builds its children and writes `(@fView cs… (f cs…))`; it needs no table lookup,
temporary variable, proof term, or separate construction-history relation.

`min` is the only computation in the fragment: the smaller of two terms in the model's
structural order, egglog's `ordering-min`. A source union writes an edge from each of the
two ids to the smaller one; the edge from the smaller id to itself is not a union-find
edge. Both UF and view collisions keep the smaller output and write the same two edges.
Their merge specifications explicitly bind singleton parameters `old` and `new`. All output columns determine
whether a row changed, so no special identity-column setting is needed.

Maintenance rules compress paths, propagate changed output ids through views, and re-key
child columns. Rebuilding runs after each source action and run. Copies of the maintenance
rules join each source saturation ruleset, so rebuilding also happens between its rounds.

`Congruence.compile` returns commands with rule origins. Source rules are tagged with
their original command index; generated rules identify path compression, output
propagation, or the particular constructor child being re-keyed. Copies in another
ruleset retain the same tag. `tableRole` recognizes UF and source-constructor views.
These tags are for later resugaring and do not affect execution.

The output has no built-in `union` in commands, rule heads, or merge bodies. It also
needs no equality axioms from the target runtime. `Relational.exec` uses structural
identity and stored-value existence for matching and function-key collisions, and omits
implicit congruence rebuilding. `encode_relational` proves that this execution produces
exactly the same result as the general interpreter. Source equality is represented by
ordinary UF and view entries; target `(= x y)` is just an identity test with existence.

## Checks and observable correctness

A top-level `check q` asks whether the entire query has a compatible existential
substitution:

```text
holds(D, q)  iff  ∃ σ. ValidQuerySubst(D, q, σ)
result      ::= ok(D) | checkFailed
```

The finite evaluation rules are:

```text
holds(D, q)     D ⊢ rest ⇓ r
───────────────────────────
D ⊢ check q; rest ⇓ r

¬ holds(D, q)
────────────────────────────────────
D ⊢ check q; rest ⇓ checkFailed
```

The first rule uses exactly the original database. Checks create no terms, export no
bindings, and perform no merge phase. The second rule has no premise about the suffix,
so failure terminates even before a divergent suffix. The empty query succeeds.
Divergence has no finite evaluation derivation; it is not `checkFailed`.

`Source/WellFormed.lean` supplies the static premise separately from `Program.Fragment`:
declarations are fresh and precede uses, applications have the declared arities, and
actions have bound variables and legal global union operands. A declared but absent
constructor remains a valid query and may cause a failed check. Rule unions may use query
variables under the fragment's existing literal restrictions.

The obligation in `Congruence/Correctness.lean` is:

```text
WellFormed(P) ∧ Fragment(P)
∧ ∅ ⊢ P ⇓ r ∧ ∅ ⊢ encode(P) ⇓ s
⇒ succeeded(r) = succeeded(s)
```

Both states are mathematical `Database` values. Neither `FDatabase` nor interpreter fuel
appears in this statement. `PreservesObservations` remains an **unproved Lean obligation**.
The abstract rebuilding, query-correspondence, and observation-composition lemmas below
are proved; the outstanding obligation is to establish their data and metadata invariants
along every compiled prefix. The older executable `Complete.lean` theorem does not
discharge that obligation.

`Proofs/Result.lean` proves that successful results coincide with `ProgramStep`, that a
failure is exactly a successful prefix followed by a false check, and that query
correspondence gives check-outcome agreement in both directions. Interpreter correctness
is outside the paper's obligations. The executable `observeM` and `Relational.observe`
return `some checkFailed` for a failed check and reserve `none` for an inconclusive run,
including exhausted fuel. Their regressions are sanity checks, not a replacement proof.

`PreservesTermination` is a separate stretch goal: a finite source evaluation implies
some finite compiled evaluation. It is not a premise or a consequence of the required
conditional observation theorem.

### Correctness proof

Write `C_P(A)` for the prelude of the **whole** program `P`, followed by the compiled
commands of its prefix `A`. Using the whole prelude matters: its declarations and copies
of maintenance rules depend on the complete program, including later saturation commands.
The internal statement needed at each check is

```text
P = A; check q; B
∅ ⊢ A ⇓ ok(S)       ∅ ⊢ C_P(A) ⇓ ok(T)
──────────────────────────────────────────
holds(S, q) iff holds(T, flatten(q)).
```

`CheckAgreement` in `Proofs/Congruence/Observation.lean` states exactly this property.
`observations_of_checkAgreement` proves the final success/failure theorem from it. The
prelude and the compiled blocks of non-check commands contain no checks, so a terminating
execution of any such block must succeed. Align the two executions one source command
at a time. At a check, query agreement implies that both pass or both fail. In the passing
case the databases remain unchanged and induction continues. In the failing case both
executions immediately return `checkFailed`; there is no premise about the remaining
program. If both reach the end, both return `ok`. This argument uses only the two given
finite executions. It does not construct a target execution or relate round counts.

The data proof supplying `CheckAgreement` uses the following boundary relation. A reading
`T ⊢ t ↝ i` is `ViewRepr T t i`: literals read as themselves; an application reads through
the view of its constructor after recursively reading its children.

- Every held source term has a target reading, and every nonreflexive asserted source
  equation has readings of its two endpoints joined by a UF edge in either direction.
- Every view row `View_f(cs, i)` has a held source witness `f(as)` with `as ≡_S cs` and
  `f(as) ≡_S i`. Every UF row `UF(a, b)` satisfies `a ≡_S b`.
- The target is rebuilt. Its equations are diagonal, its UF edges descend in the term
  order, and its generated declarations and maintenance rules are present. Source rules
  registered so far correspond exactly to their compiled rules.

The first two clauses express completeness and soundness. They do not require the raw
source and target term sets to be equal, or a particular choice of representative.

**Rebuilding lemma.** A finite, well-formed target at a generated-rule and merge fixed
point has canonical readings. A collision of two views at the same key joins their
outputs: the merge body writes both outputs to their minimum. The same reasoning joins
two outgoing UF edges. Path compression makes parent reachability transitive. Output
propagation and child rules transport view rows along these parent paths. All of these
facts follow from actual `RuleResults` and `MergeStep` instances; they are not additional
rewrites in the semantics.

Every id reaches a root. The proof uses the finite set of ids reachable in this database
and strict descent of nontrivial UF edges; it does **not** assume that the structural
order on all terms is well founded. Two reachable roots coincide because competing
paths join. Normalize each view's keys and output to roots. Structural induction on a
source term then shows that all its readings have the same root: corresponding child
readings normalize to equal keys, and the parent outputs join at that key. UF soundness
and literal isolation keep literal roots equal to their original literals.

This lemma is proved in `AbstractMaintenance.lean` and `AbstractRebuild.lean`.
`Proofs/Finite.lean` separately proves finiteness for every mathematical state reached
from empty by a finite successful prefix, including finite saturation derivations. A
round has finitely many matching substitutions because its rules, held terms, and query
variable lists are finite. Finite actions, merges, and sequences preserve finiteness.

**Query lemma.** At a boundary satisfying the relation, a source query has a complete
match iff its flattening has a complete target match. In the forward direction, choose
one canonical reading for each value of the source substitution. This single assignment
is shared by every occurrence of every query variable. Congruence transports a held
pattern witness to readings of the instantiated expressions. Even when matching
temporarily introduces query operands, those operands introduce only reflexive equations;
they cannot provide a new held witness. Traverse the original syntax in compiler order,
bind the fresh variable for each application to its reading, and satisfy the emitted
view atoms and equalities. Disjoint fresh-variable intervals and the reserved namespace
make these bindings compatible across the whole conjunction.

For the reverse direction, read the flattened view atoms back through the original
syntax. Sound view rows supply source existence and congruence. Because each source
variable occurs as a view key, its target value is a held source value; generated table
terms cannot be substituted for source values. Restrict the resulting assignment to
each pattern and join those substitutions. Groundedness preserves the existence
requirement at equality patterns. This is the proved `Abstract.Rebuilt.queryHolds_iff`
in `AbstractForward.lean`, using `AbstractQuery.lean`, `AbstractTransport.lean`, and
the reverse matching proof in `Match.lean`.

**Execution lemma (remaining Lean port).** The prelude establishes the boundary relation
at empty source data, and paired successful executions of each source command and its
compiled block preserve it. The mathematical argument is by command cases:

- The prelude declares tables and registers maintenance rules without creating data.
  Source declarations are already installed there. Fresh declarations, consistent arities,
  and the reserved namespace give the required signatures without name collisions.
  Rule registration installs exactly the corresponding compiled rule. At a rebuilt
  boundary neither operation can add data through a further merge phase.
- Building an application writes its children before its view, with the structural
  application as its id. Induction on the expression gives readings for the source result
  and all newly built subterms. A union additionally writes both endpoint ids to their
  minimum, directly establishing the required joined readings. These rows are sound in
  the source action's post-state.
- A generated merge preserves soundness. Colliding views have source-congruent outputs
  by anchored congruence on their held witnesses; colliding UF edges have source-congruent
  outputs by transitivity. Their minimum is one of those outputs. Maintenance preserves
  soundness by transitivity and replacement of congruent children. All phases retain old
  rows, so existing readings and joined source equations persist. Minimum links descend,
  and compression preserves descent. Thus arbitrary intervening merge choices are allowed.
- For `run R`, use the query lemma in both directions on the pre-state. A compiled match
  gives a source match at the same source-valued ids, so its whole head is justified by a
  source firing in that round. Conversely, a source match gives a compiled match under
  the common canonical assignment. Induction over the head's expressions and actions
  represents every source contribution. Scoping, declared constructors, and the fragment's
  literal-union restriction ensure these whole source heads evaluate successfully.
  Unioning all contributions preserves both directions. Maintenance copies selected by
  `R` add nothing to the already rebuilt pre-state; the trailing rebuild reestablishes
  canonical readings after the new contributions.
- For `saturate R`, compare fixed points rather than rounds. To prove soundness, fix the
  final source state and induct over the given finite target derivation. Initial rows
  remain justified there; a compiled firing reads back to a source firing whose results
  are already included by the source fixed point. Merges and maintenance preserve those
  justifications. To prove completeness, fix the final target state. Copies of all
  maintenance rules in `R` make that state rebuilt. Induct over the given finite source
  derivation: represented premises give a compiled firing, and the target fixed point
  already contains its head. The query argument here is relative to the represented
  source intermediate state; soundness may be justified in the larger final source state.
  Thus different numbers of source and target rounds cause no problem. The trailing
  dedicated rebuild preserves the established relation.
- A successful check leaves both states unchanged. The query lemma also ensures that a
  failing check fails on both sides, as used in the observation proof above.

Induction over successful prefixes using this execution lemma establishes
`CheckAgreement`, which the observation theorem turns into `PreservesObservations`.
The execution lemma is the remaining formal obligation; the checked query and observation
theorems must not be reported as a completed Lean proof of the compiler theorem.

## Query traversal

Flattening visits conjuncts left to right. Within an application it recursively visits
children left to right, then emits the parent's view atom. Within equality it visits the
left expression, then the right, then emits equality of their resulting ids. Each
application occurrence gets one fresh variable, including repeated subexpressions.
Variable supplies are local to a rule; source names cannot use the generated `@` prefix.

For example, `(= (F (G x)) (H x))` becomes:

```text
(@GView x @v0)
(@FView @v0 @v1)
(@HView x @v2)
(= @v1 @v2)
```

Resugaring will receive the original query and repeat this traversal while consuming
premise proofs in order. No separate tree describing flattening is stored.

## Provenance instrumentation

`Provenance.encode` adds one proof output to each function. Proof constructors identify
the exact global command, rule action, or merge computation. Rule proofs carry the
substitution and ordered premises; merge proofs carry both input proofs. Their claims
are recovered by evaluating the original action or merge, without guessing endpoints.

Appending a proof output preserves the original merge parameter bindings. The pass
instruments actions and appends a result without renaming the original expressions; it
appends fresh `@prov:p0` and `@prov:p1` parameters for the two input proofs. The input
check requires distinct parameter names of the declared width and excludes the reserved
`@prov:` prefix, even for unused parameters. Scalar and tuple parameter spellings are
handled by the parser and emitter;
the [merge guide](MERGE.md#collisions-and-command-steps) gives the componentwise notation.

The pass accepts flat table queries and equality tests whose variables and existence
witnesses come from table premises. This covers the congruence compiler's output;
unanchored equality-only queries and constructor writes are outside its input
fragment. Function bodies and results may use `min` and
multiple output columns. Generated names use the reserved `@prov:` prefix.

Only original data columns determine merge conflicts. This also suppresses collisions
between distinct proofs of identical rows. A conflict records both inputs' proofs in
the result's proof, and body facts record the merge justification too. Proof metadata
therefore cannot trigger a data merge or cause an otherwise stable rule to accumulate
longer resident proofs.

Extraction decodes a proof constructor into a proof tree with explicit facts, then checks
it against the uninstrumented relational program, which has no `union`. Equality premises
use checked subterms of table facts as existence witnesses; no auxiliary existence
relation is needed. These are intermediate proofs, which lifting translates into source
proofs checked against the original program.

## Proof lifting

`Resugar.lift` checks a relational proof against the compiled program, then rebuilds it
recursively as a source proof tree. A view row `(@fView cs… id)` becomes the claim
`id = f(cs…)`, a UF row an equality, and a value its reflexivity. Global rows become
`fiat` nodes. Generated rules are recognized by their origin tags: path
compression is transitivity, output propagation symmetry and transitivity, and child
re-keying anchored congruence. A UF or view collision joins its two inputs the same way.
A source rule firing names the original command, restricts the substitution to the
original query's variables, and recovers its premises by walking the original query in
the compiler's order ([Resugar/Query.lean](EgglogSemantics/Resugar/Query.lean)),
consuming one flattened premise per application and equality and rebuilding nested
patterns with congruence. A subterm's existence comes from the derivation that introduced
it, never from a new `fiat`.

Each node is validated by `SourceProof.checkNode` as it is built, and the result is
checked again by `SourceProof.check`. `lift_sound` therefore inherits the source
checker's soundness: a lifted claim whose endpoints the source holds is a source
congruence.

`Resugar.Export` writes proofs as JSON certificates with the program as `.egg` source,
listing each tree's nodes in postorder with shared subtrees, and
[proof_certificate.rs](../egglog/src/proofs/proof_certificate.rs) replays them through
Rust egglog's proof checker. The fixtures in
[Resugar/Fixtures.lean](EgglogSemantics/Resugar/Fixtures.lean) pair lifted proofs with
hand-written proofs that both checkers must judge alike; their export is committed as
`egglog/tests/lean-certificates.json`, and `make lean-certificate-test` also exports and
checks the whole corpus.

## Proof status

The congruence pass has kernel-checked proofs for:

- Union-free output and equivalence with execution using structural identity only
  (`encode_unionFree`, `encode_relational`).
- Query flattening and matching in both directions (`sourceMatch_of_encodedQuery`,
  `encodedQuery_match_of_source`).
- Preservation of sound entries, descending UF edges, and the connection between
  retained entries and live rows through source actions, merges, and maintenance.
- Unique roots and normalized view readings at rebuilding fixed points
  (`Rebuilt.viewLeader`, `Rebuilt.viewsCover`).
- Source rule firings, aligned rounds, and saturation (`encodedRule_firing_reads`,
  `round_simulation`, `saturation_simulation`).
- Prelude initialization and global actions with interleaved merges and rebuilding
  (`prelude_state`, `global_cmd_simulation`).
- The executable reader and correspondence under explicit state invariants
  (`sameClassF_iff`, `Rebuilt.corresponds`).

**The previous executable-target theorem is complete; the mathematical execution port
is pending.** [Complete.lean](EgglogSemantics/Proofs/Congruence/Complete.lean) proves
`Egglog.Congruence.encode_corresponds`:

```lean
Cong src a b ↔ SameClass target.toDatabase a b
```

Its premises are `P.Fragment`, a source execution from empty, successful compiled
execution, and membership of both endpoints in the source. `encode_corresponds_relational`
gives the same theorem for execution using structural matching and table operations only.
Termination is not asserted.

**Step 2 is complete for the agreed constructor source fragment.**
[SourceProof/Soundness.lean](EgglogSemantics/Proofs/SourceProof/Soundness.lean) proves
`check_supported` and `check_sound` for the executable checker. Accepted claims have
source existence witnesses for every subterm. For endpoints held by the source,
acceptance implies its original `Cong` relation. The source state must be reached by
the original program, well formed, and saturated for every ruleset. No proof is accepted
by assuming an unproved intermediate term exists.

**Step 3 is implemented.** [Provenance/Soundness.lean](EgglogSemantics/Proofs/Provenance/Soundness.lean)
proves that every accepted relational fact exists in a well-formed, reached state
saturated for the original relational program's rules and merges. The corpus gate
checks data preservation and every retained function entry's extracted proof.

**Steps 4 and 5 are implemented.** [Resugar/Soundness.lean](EgglogSemantics/Proofs/Resugar/Soundness.lean)
proves `lift_sound` for lifted proofs. Every retained row of every in-domain corpus
program lifts to a proof the source checker accepts, and Rust egglog's checker accepts
the same proofs and rejects the same hand-written counterexamples
(`make lean-certificate-test`).

Source merge proofs are deferred: equality can produce another spelling of one
stored function row without establishing a second input to its merge body. The
[checker guide](CHECKER.md#source-merge-inputs) records the counterexample. This does not
affect the constructor-only completeness theorem or the relational provenance pass.

The source fragment is defined once, as `Program.Fragment`: constructor declarations, no
`min` and no generated source names, consistent arities, supported queries, scoped and
declared heads, and no literal unions. A query fact is an application, as in egglog's
syntax; a bare variable or literal fact is outside it. The completeness theorem assumes it
and the source proof checker accepts only programs in it. Arbitrary source merge functions
remain outside its scope.
See [Source.lean](EgglogSemantics/Source/Domain.lean) for the exact conditions.

## Validation

`make lean-check` builds the library, audits for proof holes, and runs the corpus gates.
The congruence gate compares every pair of held source terms against the compiled
program's reading, and checks that execution with and without equality reasoning agrees.
The provenance gate checks data preservation
and every retained row's extracted proof. The resugar gate lifts those proofs and checks
them against the original source program, and the certificate gate exports the same
proofs and checks them with Rust egglog. Failures, stuck executions, and
insufficient fuel fail the command. Out-of-domain cases are counted separately.

The corpus is the curated and generated programs in `DiffTest.lean` together with the
hand-written `.egg` programs under [`tests/`](tests), which `Program.ofEgg` parses. The
egg gate (`difftest egg`) checks each of those against its committed snapshots: the
congruence encoding in `<name>.congruence.egg`, the provenance encoding in
`<name>.provenance.egg`, and the lifted source proofs in `<name>.proofs.txt`.
`make lean-update-egg-snapshots` rewrites them after an intended change. A program that
unions a term with its own subterm does not saturate in the model, whose classes are sets
of explicit spellings, so the hand-written programs evaluate into separate constructors
instead.

From `semantics/`:

```sh
lake build difftest
.lake/build/bin/difftest congruence 64
.lake/build/bin/difftest congruence 64 both-2 rand-43 sat-hit
.lake/build/bin/difftest provenance 64
.lake/build/bin/difftest resugar 64
.lake/build/bin/difftest egg 64
.lake/build/bin/difftest export-certificates 64 /tmp/certificates.json
```

Executable regressions also check recursive traversal order, origin tags, rebuilding
necessity, and rejection of a rule firing whose constructor premise never existed.
