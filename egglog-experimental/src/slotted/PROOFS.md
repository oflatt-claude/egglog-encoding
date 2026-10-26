# Slotted proofs

`egglog-experimental --slotted --proofs source.egg` extracts and checks proofs
for supported equality checks in [slotted programs](LANGUAGE.md). Each proof uses
source terms, rewrites, and unions. The slotted checker verifies the translated
proof against the source program before and after normalization.

The compiler emits a variant of the [slotted encoding](ENCODING.md) supported by
egglog's term/proof encoding. The translator consumes unsimplified egglog proofs;
egglog's own proof checker and simplifier are skipped in this mode.

```text
source → encoded program → egglog proof → surface proof → checked claim
```

# Terms

A term is what the language writes: a constructor applied to children, a payload
literal, or a slot such as `$a`. A binder column holds the bound slot itself.
Ordinary proof steps compare terms syntactically: `(Lam $a $a)` and
`(Lam $b $b)` are different terms. Equivariance explicitly transports proofs
between slot names. Source equality conditions compare bound names by scope,
and the final claim records how its requested terms are named in the proof.

Printed proofs preserve source slot names in terms, substitutions, and renamings.
Internal slots without a source name print as `$v0`, `$v1`, …, skipping source names
and rule variables, even when they do not occur in the printed proof. The same
slot has one name throughout the proof, including permutation coordinates that
appear only in an equivariance step or the final witness. Numbered source slots
remain numbered.

When source terms and rule instances are read, each binder receives a name
separate from other binders and free slots. Names already distinct are preserved.
This lets alpha-equivalent terms differ by a permutation of slot names. The
translator and checker use the same binder refresh.

The checker associates each equality with its carrier sort. An equality derived
from a source union or rewrite retains that sort through composition and
congruence. Reflexivity of bare slots and literals is sort-independent.

# Propositions

A proposition is an ordinary equality `t1 = t2`. Any renaming has already been
applied to the actual terms. Symmetry, transitivity and congruence check exact
term identities and carry no renaming state.

A renaming `m` is a finite bijection on slot names, the identity outside its
support. `rename(m, t)` recursively renames every slot occurrence, bound and free
alike, including binder declarations. Constructor heads and payloads are unchanged.
The explicit Equivariance rule applies this operation to both endpoints of a proof.

# Justifications

The ordinary equality rules, source axioms and source rewrite applications, plus
Equivariance. The checker is independent of egglog's checker; its small equality
rules have the same ordinary semantics.

**Fiat.** `t = t` for a term the program built -- a slot, a payload literal, or a
subterm of a `let` or a `union` -- and `a = b` for a source `(union a b)`, in
either direction. Reflexivity is not assumed for terms the program never built.

**Rule.** Instantiate `(rewrite L R :name n :when (...))` by a substitution σ.
Pattern variables take terms of their declared sorts; slot literals take distinct
slots, as required by the [language](LANGUAGE.md#fresh-slots).

Premises are ordered: first a proof `t = L[σ]`, then one proof for each
multipattern condition `(= v call)`. Each condition's endpoints must be `σ(v)`
and `call[σ]` up to alpha-equivalence, with identical free names.

Guards are evaluated on σ with the constructors' binding scopes. `free` tests
membership in the union of the listed terms' free slots; `not-free` tests absence
from that union. `free-names-are` requires exactly the listed free slots.
`(!= a b)` requires different instantiated terms. This guard records the state
when the rule fired; a later union may equate its terms.

RHS-only slot literals must be fresh for every other binding. The conclusion is
`L[σ] = R[σ]`, its reverse, or reflexivity of a subterm of either side. A
right-hand side using `subst` is unsupported.

**Sym.** From `a = b`, derive `b = a`.

**Trans.** From `a = b` and `b = c`, derive `a = c`. The middle terms must
be syntactically identical and their carrier sorts must agree.

**Congr.** From `a = F(..., c, ...)` and `c = d`, derive `a = F(..., d, ...)`.
The selected child must match the child proof's left endpoint exactly; the
child proof must have the column's sort. No renaming is performed by this rule.

**Equivariance.** From `a = b`, derive `rename(m, a) = rename(m, b)` for a finite
slot permutation `m`. The checker recomputes both endpoints and preserves the
proof's carrier sort. This rule applies only the slotted theory's action on slots;
it does not rename payload values or constructor names.

# Claims

A printed claim is an instance of the source query. Query-local slots take the
names selected by the match; globals retain their concrete source names. For
example, after `(let p (F $a))`, `(check (= p (F $b)))` can print a proof of
`(F $a) = (F $a)`: `$b` is a query variable, not a request to rename `$a`.
This instantiation happens before constructing the equality and its renaming witness.

A claim carries an ordinary proof and a separate renaming witness `m`. For source
terms `a` and `b`, the proof must have exactly the endpoints
`a = rename(m, b)`, after the usual binder refresh on the source terms.

`(check (= a b))` additionally requires `m` to fix the free slots of `b`, or the
free slots of `a`. The latter is sufficient by equivariance with `m⁻¹` and
alpha-equivalence of bound names. `(check (renaming-= a b))` allows any witness,
but still checks the actual ordinary equality proof and its endpoints. The
proof must have the claim's carrier sort, or no sort at all. Negative claims
and other claim forms are checked, not proved.

When the witness changes the spelling of `b`, the display ends with one
`claim: a = m·b` line. This is a checked interpretation of the root equality,
not another inference rule. For example, alpha-renaming needs only:

```text
#0: (Lam $a $a) = (Lam $a $a)
    by fiat
claim: (Lam $a $a) = {a->b, b->a}·(Lam $b $b)
```

# Normalization

The lifted proof is checked before and after a normalization pass. The pass
carries an accumulated permutation through Sym, Trans and Congr, materializing
it in their endpoints. Nested equivariance steps compose. Source axioms and
rule instances retain their provenance and substitutions, so remaining
equivariance steps sit immediately above source steps. A renamed source union
still has a proof of the original union underneath it.

The pass also removes reflexive congruence, symmetry and transitivity steps and
double symmetry. It memoizes by proof ID and accumulated permutation: shared
subproofs stay shared when used in the same coordinates. Slot names are assigned
to the resulting displayed proof, reserving all source names and rule variables.

# The proof profile

`--slotted --proofs` compiles the same slotted graph operations into forms supported
by egglog's term/proof encoding. Generated machinery rules have stable names under
`slotted/`, so the translator can identify their derivations. User rules use their
source names, disambiguated when reused, with `/apply` and `/drain` on companion rules.

`group-coset-reps` returns a vector sorted by content in both profiles, so the index
a `Reading` row was read at means the same in every run, which a proof citing it needs.

The proof-compatible encoding represents these operations as follows:

- *Shape tables.* `_shape_F` becomes `_shape_class_F (key...) <sort> :merge old`
  and `_shape_back_F (key...) Renaming :merge old`, both set by the index rule;
  `_shapeof_F` becomes `_shapeof_edges_F (...) Renamings :no-merge`, holding
  `[s1 .. sn, back]`, and `_shapeof_syms_F (...) Group :no-merge`.
- *Shape collisions.* The collision a merge block stated is a rule,
  `shape-collision`, in the shape phase: a row `c` whose memoized shape finds a
  stored pair `(c0, back0)` under its key other than its own `(c, back)` states
  `(ShapeEqual c (compose back (inverse back0)) c0)` -- a symmetry of `c` when only
  the renaming differs -- one run after the index write it reads. Since the dedup
  can fold a row in that run, before the collision rule sees it, the profile's dedup
  also states the symmetry between the two rows it compares as it deletes one.
  `Invocation` becomes `(relation Invocation_N (<sort> Renaming <sort>))`, written
  `(Invocation c name a)`, and `invocation-merge` unions two members under one name.
- *Merge behavior.* The `:no-merge` tables are `Unit`- or container-valued.
  Source-term extraction uses the same cost model and decoder in both modes.
- *Claims.* Supported equality checks compile to `prove-slotted` over the shared
  query compiler's facts. The command extracts an existence proof, reconstructs
  the matched source terms, and checks their equality. Other checks use the same
  queries without proof extraction. `--slotted-proof-checks` runs this encoding
  with ordinary checks for comparison.

**Source metadata.** Four hidden `Unit` functions, declared beside the layout tables
and filled by the compiler, carry the source a translator needs:

| row | holds |
| --- | --- |
| `(SlottedCarrier "Sort" n)` | the equality sort with carrier index `n`, the suffix of its tables |
| `(SlottedRuleSource "name" "(rewrite LHS RHS :when (...) :name \"name\")")` | a rewrite's canonical source under its rule name |
| `(SlottedLetSource "x" "(Mul $7 (Null))")` | a global and the term text it was bound to |
| `(SlottedUnionSource "a" "b" "U")` | the two terms of a top-level `union`, as written, and their carrier sort |

Source text preserves identifier spelling: `x` and `?x` are distinct variables.
Slot literals keep their `$`; globals are resolved through `SlottedLetSource`.
A rewrite's conditions record the compiler's resolved pattern names, including
generated variables for bare constructor facts and nested condition terms.
Unnamed rewrites receive names unique across scopes and successive inputs.
Source recording follows execution order; `push` and `pop` restore the recorded
source together with the database.

The source recorder resolves globals through `SlottedLetSource` and reads
binder positions from `SlottedBinderLayout`. Constructor declarations provide
column and output sorts. Each claim also carries a JSON map of source slot
spellings to interned IDs, including names from earlier inputs. These records
provide the source program used by the checker; the checker does not inspect
encoded tables.

# Translation

For user rewrites, the compiler records the pattern, class, reading, and
frame names it actually allocated with `slotted-record`. This small name map
survives serialization and push/pop; reconstruction does not repeat the
compiler's fresh-name allocation. It carries no lowered rule bodies or proof
derivations, and the surface checker does not consult it.

Generated slots come from one supply that reserves all interned source slots, the input terms' slots,
encoded renaming coordinates, and names introduced during translation. Negative
input slots are valid and are reserved too. A source union is stated using its
recorded terms, then transported to the decoded binder names by proof steps.

The translator (`egglog-experimental/src/slotted/proofs/translate.rs`) maps an egglog proof over
the encoded program to a slotted proof. Pattern expansion returns its proof,
variable bindings, and occurrences together; recursive rule applications have
their own bindings. The translator retains the shared proof arena, memoized
derivations, and fresh-slot supply across expansions. Its core is a denotation
`dec` from encoded terms to source terms:
`dec(F(m1, c1, ..., mk, ck)) = F(m̂1·dec(c1), ...)`, where
each edge is completed to a bijection by naming the child's redundant slots with
fresh names, and `dec(SlottedVar_N 0)` is `$0`. Every encoded fact then denotes an
ordinary proposition, and every maintenance rule firing has a fixed derivation.
A private lifting context also retains the encoded edge coordinates needed by
later reconstruction. Restating an edge in different coordinates reuses the same
ordinary proof; transporting its endpoints emits Equivariance:

| encoded fact | proposition |
| --- | --- |
| egglog equality `a = b` | `dec(a) = dec(b)` |
| `RenamesToLeader a m b`, `Equated a m b`, `ShapeEqual a m b` | `dec(a) = rename(m̂, dec(b))` |
| `g` in `EclassGroup c`, `Reading c _ g` | `dec(c) = rename(ĝ, dec(c))` |
| `Invocation c n a` | `dec(a) = rename(n̂, dec(c))` |
| slot `r` of `c` outside `FreeVars c` | `dec(c) = rename(swap(r, r'), dec(c))` for fresh `r'` |

The last row is a *redundancy certificate*. It is derived on demand from the
derivation of the `FreeVars` row: the merge chain of intersections says which
`set` dropped the slot, and transport along an edge and group slot closure each
have a short Sym/Equivariance/Trans derivation. Group membership is derived through a
provenance-aware closure, since the stored group is closed and an element has to
be expressed as a product of symmetries the translator has proofs for.

| rule firing | derivation |
| --- | --- |
| orient, restate on narrower slots | Change edge coordinates; use certificates for slots the restriction dropped |
| self-equation, self-edge into the group | the premise, respelled |
| transitivity | Trans of the first edge with the second |
| one leader per follower | Sym, Trans, Equivariance |
| migration | Sym of the edge, Equivariance by the total extension `R` |
| child update | Equivariance into the parent's names, then Congr with the child's edge |
| binder scope | Reframe the edge away from the bound slot; transport equality when needed |
| shape collision, node symmetries | Congr with transported child symmetries, then align edge coordinates |
| invocation naming | the edge, then Congr with the symmetry `coset-min` chose |
| user rewrite | Rule, with premises built from the atom rows by Congr and Equivariance |
| claim | the two terms' atom proofs, the class equality, and the `coset-same` symmetry |

# Running

The end-to-end demo snapshots show the source alongside its translated, checked
proof: [a rewrite](../../tests/snapshots/slotted_proofs__demo_rewrite.snap),
[bound-slot renaming](../../tests/snapshots/slotted_proofs__demo_alpha_renaming.snap),
[congruence through a binder](../../tests/snapshots/slotted_proofs__demo_binder_congruence.snap),
[a redundant slot](../../tests/snapshots/slotted_proofs__demo_redundant_slot.snap),
and [fresh names avoiding source and rule variables](../../tests/snapshots/slotted_proofs__demo_fresh_names.snap).
They run with `make check` or
`cargo test -p egglog-experimental --test slotted_proofs demo_proof_snapshots`.

`egglog-experimental --slotted --proofs source.egg` prints a proof for a check
containing one positive `=` or `renaming-=` fact. Its terms may contain constructors,
globals, slots, and literal payloads. Checks with term or payload pattern variables,
multiple facts, negation, or other predicates are checked without printing a proof.

To replay lowered code, use
`egglog-experimental --slotted-encoded --proofs encoded.egg`.
From Rust, compile with `Options { proof_mode: ProofMode::Prove, ..Default::default() }`
and evaluate the result with `new_egraph_with_proofs()`.
`make slotted-proof-tests` runs the supported source corpus through the Rust API,
including its supported equality checks. The same tests run in `make check`.
Sources using `subst` are ignored because it has no proof translation;
the CLI refuses them. Rewrite guards using `renaming-=` or `renaming-!=`
are also unsupported by proof translation. Some symmetry proofs after restricting
a class's group to fewer slots cannot yet be reconstructed. `--slotted-proof-checks`
runs the same encoding with ordinary checks for comparison.

The command and source recorder use egglog's extension APIs. Their state is stored
on the e-graph and restored by `push`/`pop`. The core crate has no slotted commands,
claim types, proof state or CLI flags.
