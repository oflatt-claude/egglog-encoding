# A relational encoding of slotted e-graphs

This branch implements the simpler relational style of the encoding: pairwise
congruence, one relation row per symmetry, and ordinary construction of right-hand
sides. It keeps the current fixes for redundancy, binders, matching, and
substitution. It is an executable baseline, rather than a restoration of an older
compiler with its older bugs.

A slotted e-graph, as described in Schneider et al.,
[*Slotted E-Graphs* (PLDI 2025)](https://michel-steuwer.github.io/files/publications/2025/PLDI-2025.pdf),
gives each e-class a set of public **slots**. A node reaches a child through an
injective renaming of the child's slots. A class can be equal to itself under a
permutation of its slots; these permutations form its **symmetry group**. The
encoding represents this information in egglog tables and restores its invariants
with egglog rules. Rust primitives provide operations on finite maps, matching
constraints, and extraction-based substitution.

[LANGUAGE.md](LANGUAGE.md) describes the input language. To inspect the generated
encoding of any input, run:

```sh
python3 slotted/slotted-egglog.py slotted/tests/figure-3.egg --desugar
```

The fragments below shorten generated names and omit routine guards where stated.
The compiler generates separate tables for each equality sort; for example, the
first sort uses `RenamesToLeader_0` and `ClassSlots_0`.

## Representation

Write an invocation as `m * c`, where `c` is a class and `m` maps its public slots
into the surrounding node's namespace. A binary constructor becomes:

```lisp
(constructor F (Renaming U Renaming U) U)
```

Thus `F(m1,c1,m2,c2)` has children `m1 * c1` and `m2 * c2`. Payload columns such as
strings or integers stay unchanged. `Renaming` is a finite injective map, represented
by `(Map i64 i64)`. `compose m n` means `m ∘ n`: apply `n`, then `m`.

A slotted class may span several egglog values. These values represent different
materialized invocations, and egglog's own equality is finer than membership in one
slotted class. The core tables are:

| Table | Meaning |
| --- | --- |
| `ClassSlots(c)` | An identity map on the public slots of the invocation `c`; merges intersect |
| `Equated(a,m,b)` | An equation asserting `a = m * b`, awaiting maintenance |
| `RenamesToLeader(a,m,b)` | A maintained equation in the same direction, normally toward the smaller egglog value |
| `RenamesToLeader(c,g,c)` | A symmetry of `c`, including its identity |
| `SubstPending(root,q,m,c)` | A substitution result whose frame must be translated back to the rewritten root |

The domain of `m` in `RenamesToLeader(a,m,b)` is the public slots of `b`; its image
is the public slots of `a` at a fixed point. During maintenance an equation can
expose redundant slots, so these sets must be narrowed before the invariant holds.

A node's own slots are the union of its child edges' images, including binder
markers. This set can be larger than its class's public slots. For example, a node
representing a constant function can still contain a bound name. Such **node-local
slots** must survive even though the class does not depend on them. This is the
distinction in Definition 4 of the paper.

The variable constructor is stored as `Var(0)`. An occurrence of `$7` is
`[0 ↦ 7] * Var(0)`, not a separate variable class. Noncanonical variable rows are
redirected and removed during maintenance.

## Equality and maintenance

Equations are oriented toward the smaller egglog value. A renaming entering the
relation is restricted at both endpoints:

```
R(a, S(a) ∘ m ∘ S(b), b)
```

where `S` abbreviates `ClassSlots` and `R` abbreviates `RenamesToLeader`. Reversing
an equation also inverts its renaming. Old relation rows are restricted again when
support shrinks. An edge whose orientation becomes backwards after an egglog union
is removed.

Support is transported in both directions along every edge:

```
S(a) := S(a) ∩ image(m ∘ S(b))
S(b) := S(b) ∩ image(inverse(m) ∘ S(a))
```

These updates also apply to self-edges. If part of a symmetry orbit leaves the
support, the rest of that orbit becomes redundant. An ordinary swap of two live
slots, however, is a symmetry and does not make either slot redundant.

Path composition derives `Equated(a,m ∘ n,c)` from `R(a,m,b)` and `R(b,n,c)`.
The generated guard allows composition of self-symmetries and paths through distinct
values, but avoids multiplying a follower's edges by every symmetry of its leader.
If a follower has two leaders, `R(a,m,b)` and `R(a,n,c)`, maintenance derives
`Equated(b,inverse(m) ∘ n,c)` and removes the greater competing edge. These deletions
operate only on maps already restricted to current support.

Composing a follower's self-symmetry `g` with its edge `m` to a leader, then
reconciling that edge with `m`, transports the symmetry to the leader by conjugation.
Followers retain their self-edges. Deleting them in the same phase as native unions
can delete a leader's symmetry after the two values become equal; semi-naive
evaluation need not rederive it. Composition closes the symmetry rows under
composition. No whole-group value or separate group index is involved.

Two egglog values can be unioned when they denote the same invocation:

```lisp
(rule ((R a m c) (R b n c) (R c g c)
       (= m (compose n g)))
      ((union a b)))
```

A common leader alone is insufficient. For a class with two distinguishable public
slots, its identity invocation and its swapped invocation differ unless the swap
is in its symmetry group.

## Pairwise congruence

Consider two rows with the same constructor, payloads, and child classes:

```
a = F(m1,c1,m2,c2)
b = F(n1,c1,n2,c2)
```

For each pair of child symmetries `g1 ∈ G(c1)` and `g2 ∈ G(c2)`, solve for an
injective renaming `r` satisfying:

```
r ∘ n1 = m1 ∘ g1
r ∘ n2 = m2 ∘ g2
```

A solution establishes `Equated(a,r,b)`. The emitted rule is essentially:

```lisp
(rule ((= a (F m1 c1 m2 c2))
       (= b (F n1 c1 n2 c2))
       (R c1 g1 c1) (R c2 g2 c2)
       (= r (find-mapping (compose m1 g1) (compose m2 g2) n1 n2)))
      ((Equated a r b)))
```

`find-mapping` is partial: inconsistent slot equations or noninjective solutions
make the rule fail to match. Comparing a row with itself is essential; it discovers
symmetries of the parent induced by its children.

When both rows belong to the same egglog value, the rule also permits removal of
the lexicographically greater vector of raw child edges. The equation is still
recorded, so deletion preserves any newly discovered symmetry. This makes one
physical row represent a node modulo renaming and child symmetry. It deletes the
actual stored row, not a spelling obtained after composing with a symmetry.

There is no canonical shape table. The cost is a join of pairs of rows and the
product of the relevant child symmetry relations.

## Moving nodes and updating children

If `a = m * b`, a node on follower `a` must move into leader `b`'s namespace.
For `a = F(m1,c1,m2,c2)`, the new child edges are conceptually
`inverse(m) ∘ m1` and `inverse(m) ∘ m2`. But `inverse(m)` can be undefined on a
node-local slot that is absent from `S(a)`.

Migration therefore uses `find-mapping-total` to extend the inverse injectively
over **all** the node's slots, choosing fresh names where needed. It builds the
translated node, unions its value with `b`, and deletes the old row. Partial
composition alone would erase node data. The migration guard only permits movement
toward the smaller value.

Similarly, an edge `m1 * c1` whose child is now `c1 = n * c2` becomes
`(m1 ∘ n) * c2`. The node is rebuilt and the old row removed. An identity self-edge
can narrow an outdated child edge after redundancy. A nonidentity self-symmetry
is excluded from this update: congruence already handles it, and repeatedly
rewriting through it would cycle between equivalent rows.

## Binders

A binder column uses an edge to the variable constructor as a **name marker**.
For example, `Lam([0 ↦ x],Var(0),m,c)` binds `x` in `m * c`. It is not a semantic
child occurrence. Pairwise congruence compares binder marker edges directly without
composing them with the variable class's symmetries. Child updates may rename a
marker but must preserve its slot `0`, even if the variable class has become
slotless.

A binder covers the child immediately following the binder columns. A `Let` can
therefore bind a name in its body while leaving the value child outside its scope.
A bound name is removed from the class's public support only when it is absent
from the uncovered children. If it is also free in an uncovered child, the binder
and its covered child are first alpha-renamed to a fresh slot; the uncovered
children remain as they were. This prevents a bound occurrence from swallowing a
free occurrence with the same spelling.

## Multipattern matching

A source rule is flattened into depth-one atoms. Egglog joins constructor rows on
their class and payload columns. Slot agreement is a separate constraint problem,
represented by the Rust `Frame` value.

For each matched atom, the frame records the node's slot occurrences, the public
slots of each bound pattern variable, and any literal slot names. Distinct slots
within one node, within one class, or within the set of distinct literals must
remain distinct. They form **cliques** of incompatible identifications. Shared
pattern variables equate the corresponding occurrences across atoms.

A pattern variable denotes an invocation, so its repeated occurrences agree only
up to symmetry. This branch joins a symmetry row for **every** repeated occurrence:

```lisp
(R cls_x sym_x cls_x)
```

The chosen `sym_x` is passed directly to the occurrence's `root` or `child` frame
binding. The first occurrence fixes a representative with the identity. There are
no coset representatives, cached readings, or deferred whole-group choices.

`frame-join` combines atoms' constraints. Slot literals are solved through the
matched edges; they are not freshened eagerly. Node-local redundant slots also
participate in these constraints. Once all atoms are joined, `refinements`
enumerates every consistent identification of the remaining placeholders reached
by pattern variables or carried literals. Omitting these alternatives would miss
matches made by the reference multipattern matcher.

Conditions such as `free` and `not-free` are evaluated on each refined frame.
Fresh RHS names are minted afterwards. A rewrite that rebinds a matched slot over
a variable from outside its scope must provide the corresponding `not-free`
condition; the compiler checks these capture guards.

## Actions and scheduling

The match frame is anchored at the rewritten root: its public slots retain their
names there. The RHS is constructed bottom-up in this frame, with one binding for
each new node and its free slot set. Binder slots are removed only from the child
they cover. Every intermediate node keeps this numbering; maintenance later merges
equivalent spellings. This branch does not canonicalize inner RHS nodes with
`shape`.

A constructed root is unioned with the matched root. A bare-variable RHS instead
records an `Equated` row using that variable's frame renaming. A substitution RHS
uses `SubstPending` to carry its result class and renaming back to the root.

Each user round has four stages:

1. Match every user rule and store its refinement vector and bound classes.
2. Grow the shared `Idx` relation to cover every stored vector's length.
3. Apply every refinement, check its conditions, and drain the stored matches.
4. Saturate the single `slotted` maintenance ruleset.

Maintenance also runs before the first user round. The refinement-index rules have
no fixed cap. Their binary expansion reaches every required index before actions
run. Keeping application in one stage also preserves the common read snapshot
used by substitution. These stages are retained from the optimized implementation;
they are not the old fixed-size index enumeration.

## Substitution

`slotted-subst` chooses a representative of the body's class and substitutes into
that term with capture avoidance. Selection minimizes **tree size**, counting each
child occurrence, with exact integer costs. Ties use a canonical spelling of
constructors, payloads, and slots. Selection observes the graph at the start of the
application phase. Changing that policy can change the final graph even when the
represented equalities remain sound.

This branch retains the existing Rust extractor, frame solver, and their tests.
The extractor stores selected trees using shared templates and compares their
spellings lazily. Sharing is a storage optimization; it does not turn the objective
into DAG size. Snapshot parsing and substitution-result caches are also unchanged.
This experiment simplifies the relational encoding, rather than independently
reimplementing these primitives.

The multipattern oracle deliberately uses the same snapshot and representative
selection policy, with an independent expanded-template implementation. The nested
performance baseline uses the reference's syntactic substitution instead. In the
paper artifact, the slotted SDQL runner selects `SynExprSubst`; extraction-based
substitution is available in the library, and the egg SDQL baseline uses
`BetaExtractApplier`. The slotted runner separately extracts its final optimized
program. The array case study uses explicit let-rewriting.

## Contract used by the compiler comments

These labels summarize the obligations referred to in the implementation:

| Label | Obligation |
| --- | --- |
| C1 | A pattern variable denotes a class together with a renaming, modulo symmetry |
| C2 | Each atom contributes slot occurrences and distinctness constraints to a frame |
| C3 | Connected atom order is an emission convention, not a semantic restriction |
| C4 | A variable binding names exactly its class's public slots; a node may carry more |
| C5 | Repeated occurrences quantify over the class's symmetry rows |
| C6 | Shared variables identify corresponding slot occurrences across atoms |
| C7 | Slot literals are solved, and distinct literals remain distinct |
| C8 | All consistent placeholder refinements are considered |
| C9 | Conditions are checked after refinement; rebinding observes capture guards |
| C10 | Unpinned RHS slots are fresh with respect to the completed match |
| C11 | Actions build in the root's frame; invocation renamings are retained |
| C12 | Substitution returns a selected term's class together with its frame |
| C13 | Stored matches are fully enumerated, applied, and drained within one user round |
| C14 | Pairwise congruence includes self-pairs and removes duplicate node rows |
| C15 | Maintained renamings and symmetries are restricted to endpoint support |

## Optimizations to explain separately

The optimized encoding can replace these operations without changing their intended
semantics:

| Baseline operation | Optimization |
| --- | --- |
| Pairwise node comparison and self-comparison | Canonical shape index, sharing the shape and symmetry walk |
| Symmetry relation closure | Whole-group values and group primitives |
| Pairwise equality of invocations | An invocation index keyed by a canonical coset representative |
| All symmetry readings at repeated occurrences | Cached coset representatives on pinned slots and deferred choices |
| Build every RHS node in the match frame | Canonical construction below the root |
| One maintenance fixed point | Separate phases for indexes, groups, and node movement |

Slot restriction, fresh extension during migration, binder scope, and complete
refinement are correctness requirements in both versions. They cannot be removed
as optimizations. The shared Rust primitives and staged application remain part
of this baseline and should be stated explicitly when comparing its performance.

## Running the comparisons

The branch uses the same source programs, reference rules, and validation entrypoints
as the optimized encoding:

```sh
make check
make slotted-check
python3 spot-check.py
python3 slotted/eval.py array --params 0 --side encoding,ref-multi \
  --counts --jsonl /tmp/slotted-simple-array.jsonl
```

`make slotted-check` includes source regressions, snapshot drift, invariant checks,
mutation tests of the graph checker, curated differential comparisons, and generated
cases. The corpus covers symmetry, redundancy, binder collisions, transitive
renamings, complete refinement, substitution, and the array and SDQL languages.
`spot-check.py` runs Array N=0, independently counting live constructor rows for
nodes and subtracting follower values from `ClassSlots` entries for classes. It
reports one process timing per side. It imports no eval or graph
comparison helpers.

`eval.py` supports the paper's full array and SDQL workloads on this branch.
With counts enabled, it requires matching class and node counts **and** a verified
isomorphism against `ref-multi`. The witness contains a class bijection and one
slot bijection per class; validation checks support, symmetry groups, and nodes
under those maps. Work limits, timeouts, and missing graph dumps remain explicit
unverified outcomes, and cause a requested correctness comparison to fail. A
matching count alone never certifies a graph. Goal success is checked independently
on each side.

The oracle is pinned in [xmulti/Cargo.toml](xmulti/Cargo.toml) to
[`memoryleak47/slotted-egraphs`](https://github.com/memoryleak47/slotted-egraphs)
revision `48cefee5503822224257e4f2e81681fef212ae89`. Correctness comparisons use its
multipattern matcher. The nested matcher is only a performance baseline; its graph
is not required to agree.

Use separate report paths when comparing branches: saved evaluation rows are
observations, not a substitute for rerunning the changed compiler. The simpler
joins may be much slower on large workloads. Passing the available comparisons is
evidence for this implementation, not a proof for every input, and retaining the
Rust primitives retains their limitations as well.
