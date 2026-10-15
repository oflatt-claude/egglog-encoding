# Mathematical tables, merging, and saturation

The specification uses one mathematical `Database` on both sides of the compiler.
Its state contains declarations, rules, an evaluation environment, constructor
existence/equations, current function entries, and pending function writes. Current
entries and writes are sets of `Entry { name, key, value }`; both the key and output
are explicit tuples. This is a mathematical state, not an executable row index.

## Values and current entries

Constructor values are ground terms. The reflexive equation `t = t` records that
`t` exists, and constructor congruence is derived from the asserted equations.
A function entry is stored separately:

```text
f(k̄) ↦ v̄
```

Writing an entry records the existence of its column values and proposes the entry
for insertion. A table query reads only current entries. A pending write is not a
query result, and replacing an entry does not leave its displaced output available
to table queries. The existence of the displaced value and established equations
are preserved.

The surface atom `(f k₁ … kₙ v₁ … vₘ)` still uses the declaration to separate keys
from outputs. Function entries cannot occur in value-expression positions.

## Explicit merge binding

A merge specification binds two output tuples:

```text
merge (ō, n̄) { A; return ē }
```

A collision evaluates the body and result with the componentwise substitution
`σ = [ō ↦ ā, n̄ ↦ b̄]`. Scalars are singleton tuples. The declared identity columns
control whether an arriving tuple differs enough to run the body; an unchanged
collision keeps the resident tuple and skips the body.

`MergeStep` has three cases:

1. Insert a pending write whose key has no current entry.
2. Consume a pending write and a resident entry with congruent keys, run the merge,
   and install its result in place of the resident entry.
3. Consume two distinct current entries whose keys have become congruent, run the
   merge, and install one result in their place.

Inputs are consumed before the merge body runs. Consequently, a body that proposes
one of those inputs again leaves a new pending write; it is not accidentally
removed afterward. Body actions can create constructor terms, add equations, or
propose further function writes. The surrounding environment and rules are restored.

A completed merge phase has no pending writes and at most one current entry per
function/key congruence class. A lone resident entry is not a collision with itself.
`MergeNormalize D D′` requires both a finite merge closure and this completion
condition. The semantics does not assume that arbitrary merge bodies normalize.

Pending writes are a **set of proposals per phase**. A proposal identical to a
resident row is still a real write, but duplicate proposals within one phase are
coalesced. This is sufficient for the congruence compiler's idempotent merges; it is
not a model of the multiplicity of arbitrary non-idempotent Rust updates.

## Representative ordering

`ordering-min` compares constructor/literal node counts first, then uses the
structural comparison to break ties. In particular, a proper subterm precedes the
term containing it. Comparing two integer literals retains ordinary integer order.

The constructor fragment introduces no new constructor names or literal values.
Over that finite vocabulary, every initial segment of the size-first order is
finite, and the order is well founded. This is the bound used for representatives;
there is no claim that the order on all integers or all possible names is a global
well-order. `Proofs/Order.lean` and `Proofs/OrderFinite.lean` prove these properties.

## Completed rounds and semantic stopping

A round fires the rules against its pre-state, combines their equation additions
and proposed writes, then finishes a merge phase. Saturation repeats these completed
rounds and stops at the **first** round preserving the database's meaning. It returns
that round's post-state, including its permitted redundant writes.

For constructor terms, meaning includes both inferred existence and equality:

```text
Infers(D, a, b) iff
  ∃ w ∈ terms(D). CongOn(D, [a,b], w, a) ∧ CongOn(D, [a,b], a, b)
```

The old-state witness is essential: reflexivity of a hypothetical operand does not
establish that an absent term exists. `SameMeaning D D′` requires agreement on these
inferred facts, current function entries, and metadata. Pending writes are empty at
both completed boundaries. Current entries are compared directly; the compiler
must establish their normalization through its own UF/view rules.

```text
Round(D, D′)    SameMeaning(D, D′)
─────────────────────────────────
Saturate(D, D′)

Round(D, M)    ¬SameMeaning(D, M)    Saturate(M, D′)
─────────────────────────────────────────────────
Saturate(D, D′)
```

The constructor source fragment excludes `min`, so its rule evaluation can respect
congruence. Proving that an unchanged semantic round remains stable requires that
fragment property. The general language's `min` can observe different represented
spellings; semantic stability for arbitrary such programs is not assumed.

## Congruence compilation and proof migration

The target still uses ordinary UF and view tables and has no implicit equality
reasoning. Generated heads seed each value's UF self-parent. Source-rule queries
bind `UF(x, r)` and `UF(r, r)`, then use `r` in the head. With a single current output,
the second atom certifies a genuine root. Maintenance supplies compressed parent
edges and normalized view entries.

The core spec, size-first order laws, finite-vocabulary order bounds, and direct
live-table lemmas are kernel checked. `Proofs/SameMeaning.lean` gives a partial
interpretation of constructor terms that characterizes inferred facts;
`Proofs/SourceMeaning.lean` proves that ordering-free source checks agree across
`SameMeaning` states, transporting their substitutions when necessary.

`Proofs/Congruence/LiveNormalization.lean` proves termination of **every** generated
merge schedule from a finite store with the generated declarations and singleton
output shape. It also constructs a completed normalization. A row whose output
has finite-set rank `n` has weight `5^n`; a pending write has twice that weight.
Every insertion or collision strictly decreases the total weight, including the
up to two UF writes emitted by a changed collision. This proof needs neither
diagonal congruence nor a global well-order on terms.

The end-to-end compiler execution and termination proofs are still being ported.
They must establish the generated-table invariants from actual compiled programs,
prove rebuilt view/query correspondence using current rows and inferred source
facts, and bound whole saturation rounds. Merge termination alone does not imply
termination of saturation. The former historical-row theorems must not be cited as
proofs of the new semantics: a finite bound on equations alone no longer proves
merge termination, since current tables can change without adding equations.

`Tests/LiveSemantics.lean` gives a concrete distinction from raw equality: with
`C = F(C)`, the spelling `F(F(C))` is absent but inferred, and adding it preserves
`SameMeaning`. `Tests/LiveCompiler.lean` checks that the formerly growing compiled
nested-head and descending-leader examples terminate, and that displaced outputs
and missing constructor instances fail their checks.
