# Slotted semantics (phase 1) and the slotted pass (phase 2)

The slotted layer ports the "Slots and Binders" and "E-Matching" semantics of the paper's
slotted section onto the plain specification under `EgglogSemantics/Spec/`, without
changing it. The slotted pass compiles a slotted program to a plain `Program` over a primitive
evaluation layer; its correctness proposition relates `SEval` to `Target.Eval`. Phase 3
is the proof of that proposition, including the maintenance and matching simulations.

## What exists

| Part | Module |
| --- | --- |
| The specification, one blueprint node per displayed definition, rendered by the `slotted` blocks of `paper/semantics.tex` under `make -C semantics paper-check` | `Slotted/Spec/{Binders,Slots,Congruence,Match,Eval,Step}.lean` |
| The parser for the slotted `.egg` subset, one slotted program per check, and its corpus report (`difftest slotted-parse`, `make -C semantics lean-slotted-parse`) | `Slotted/Tests/Parse.lean`, `DiffTest.lean` |
| The specification evaluated over a finite slot universe and a finite term universe, with soundness of what it finds | `Slotted/Tests/Bounded.lean` |
| The paper's distribution example and the `tests/slotted/paper` phenomena as `#guard`s, and the conservative-extension test against the plain interpreter | `Slotted/Tests/Examples.lean` |
| The slotted closure contains the plain one under the empty signature | `Slotted/Proofs/Conservative.lean` |
| The bounded evaluator against the Rust reference on the `paper/` corpus files (`make -C semantics lean-slotted-difftest`) | `slotted-difftest.sh`, `difftest slotted-bounded` |
| The executable slotted pass, its primitive target and phase 3 premises | `Slotted/Encode.lean`, `Slotted/Encode/`, `Slotted/Target/` |
| Compiled corpus outcomes against Rust, and checked hand-written snapshots | `slotted-compile.sh`, `Slotted/Tests/Compile.lean`, `tests/slotted/` |

## Layering

Slots are ordinary terms: the slot `$s` is `Term.app "$s" []`, recognised by its head
(`Term.isSlot`); its name is spelled with the `$`. In queries and actions a written slot `$v`
is stored as `Expr.var "$v"`, with a deterministic query binding to the name `$v`.
Ordinary variables range over renamed representatives. A concrete slot, such as one a `let` binds, is the term
`Expr.app "$s" []`. No core type changes; the plain `Cong`, `Matches`, `Reach` and `Eval` are
untouched, and the slotted definitions live beside them in namespace `Egglog.Slotted`.

A slotted program (`Slotted.Program`) is a plain `Program` together with a binder signature
`Binders := FnName → List (Nat × Nat)`; the pair `(j, i)` is the paper's
`(j, i) ∈ bind(f)`: argument `j` is a binding position whose slot is bound in argument `i`.
A binding position is a field of the head: congruence replaces term children only.

## Definitions and their paper names

| Paper | Lean (namespace `Egglog.Slotted`) | Node |
| --- | --- | --- |
| `bind(f)`, binding positions, `B_i(t)` | `Binders`, `Binders.isBinding`, `Binders.bindingPositions`, `Binders.boundIn` | `def:slotted-binders` |
| slot `$s`, `slots(t)`, all slot names of a term | `Term.slot`, `Term.isSlot`, `slots`, `allSlots` | `def:slotted-slots` |
| renaming `m`: finite partial injection, `dom`, `img`, `m⁻¹`, `m ∘ m'`, `m|_A`, `id_A`, `m_s^r` | `Renaming`, `Renaming.WF`, `.dom`, `.img`, `.inv`, `.comp`, `.restrict`, `Renaming.id`, `.update`, `.Covers` | `def:slotted-renaming` |
| the action `m * t` with fresh bound names | `Renames bind m t t'` (a relation: every fresh choice is a result), `RenamesList`, `plans`, `childMap`, `Fresh` | `def:slotted-action` |
| α-equivalence | `AlphaStep`, `AlphaEq` | — |
| `Rename` rule; `∼_E` closed under renaming; slot terms reflexive; congruence on term children only | `SCong bind db`, `SCongArgs` | `def:slotted-congruence` |
| redundant slot; live free slots `FS(E, t)` | `Redundant`, `liveSlots` | — (defined in prose) |
| `reps'(E)`, `live'(E, X)` | `sreps` (least stored spelling under `SCong`), `reps'`, `subsumed'`, `SameRow'`, `live'` | `def:slotted-reps` |
| slotted `G ≡ G'` | `SameMeaning'` | — |
| `Query'`, `App'`, fixed literal pattern slots; `Free`, `NotFree`, `free-names-are`, `renaming-=` | `SExpr.Matches`, `SMatches`, `ValidEnv'`, `SQueryMatches`, `SQueryHolds`, `Builtin`, `RenamingEq` | `def:slotted-query` |
| slots used only in actions receive fresh names; the slotted round `Run'` | `freshVars`, `FreshSlots`, `evalActions'`, `SRunRules` | `def:slotted-round` |
| slotted schedules and outcomes | `SReach`, `SEval`, `Slotted.Program`, `Program.Eval` | — |

### The action `m * t`

`Renames bind m t t'` holds when `t'` is a result of `m * t`: a slot goes through `m`; a
literal stays; for an application the binding positions receive pairwise distinct fresh
names, fresh for all slot names of the term and for `dom(m) ∪ img(m)`, each covered child is
renamed by `m` updated at its bound names (`m_s^r = (m \ {$s}) ∪ [$s ↦ $r]`), and every
other child by `m`. The relation holds only when `slots(t) ⊆ dom(m)`. Different fresh
choices give different results, all α-equivalent; `SCong`'s `rename` rule takes any result
on each side, so α-equivalent spellings of an existing term are congruent, as the paper
states.

### Redundant slots

A free slot `s` of `t` is redundant in `E` when renaming it alone to a name fresh for `t`
gives a term congruent to `t`: `$x·0 ∼ 0` makes `$x` redundant. `liveSlots E t` is
`slots t` without its redundant slots: a slot is free in a term when renaming it changes
the term's class. This is the paper's `FS`, which `free`, `not-free` and `free-names-are`
inspect. The definition stays in Lean; the displayed congruence node shows only `Rename`,
while `Slot` and `Cong'` remain constructors of `SCong`.

### Pattern slots and fresh action slots

A literal pattern slot `$x` denotes the slot named `x`; no name-assignment step precedes
matching. `ValidEnv'` stores these constants as deterministic environment entries and
ranges ordinary variables over `reps'`. Thus the only branching is over renamed
representatives. A slot used only in actions receives, in `SRunRules`, a name absent
from every value of the match; every fresh choice is a result of the round.

## Executable checking (bounded)

`Slotted/Tests/Bounded.lean` fixes a finite list of slot names `S` and a finite term
universe `U`, the subterm closure of the stored terms closed under renaming over `S`
(`termUniverse`), and computes:

- `injections A S`, all injective assignments of keys to `S`; `renameAll bind S m t`, every
  result of `m * t` with fresh names from `S` (`renameAll_sound`: each is a `Renames`);
- `scong bind S U eqs`, the least partition (`Classes`) of the known terms closed under the
  `SCong` rules with renamings over `S`: slot terms are reflexive, children of known
  applications exist, same-head terms of `U` with congruent children merge, and every pair of
  a class's first member with a member is renamed under every injection of their free slots
  (`closure_sound`: two terms in one class are `SCong`-related; symmetry and transitivity are
  the partition's);
- from a closure: `sreps`, `reps'`, `live'`, `redundant` and `liveSlots`, `renamingEq`, the
  reference evaluators `exprB`/`patternB`/`validEnvB` of the match judgement, and a
  join-driven candidate generator (an application pattern is unified against the live terms,
  a bare variable ranges over `reps'`, a literal slot denotes itself) whose output is filtered by
  the reference evaluators;
- `round`, `exec`, `observe`: the slotted round under every fresh choice from `S`, schedules
  with fuel, and the outcome of a slotted program. A check is decided on the universe seeded
  with the instances of its expressions under every assignment.

What is bounded: a pair the closure does not relate, a slot it does not find redundant, and a
check it finds to fail are statements about the universe. `Examples.lean` says for each
assertion which kind it is. The distribution example uses five slot names: the two stored binders, the fixed literal
`$v` of the rule, and two names for the checked α-variant. The capture example includes its
fixed rule literal as well.

## Conservative extension

For a program without slots, under the empty binder signature and the empty slot universe,
the slotted evaluator and the plain interpreter agree on four small programs (a union, a
failing check, a saturation, a disequality guard) in `Examples.lean`. Of the theorem that
`SEval Binders.none` and `Eval` coincide on slot-free programs, the half that the slotted
closure contains the plain one is proved (`Slotted/Proofs/Conservative.lean`:
`scong_of_cong`, `mem_live'_of_mem_live`). The other half is stated in prose only: on a
slot-free store `Renames` is the identity and the `rename` rule adds nothing beyond the
reflexivity of slot terms, which no slot-free query can see, so `SCong` is `Cong` there,
`reps'` is `reps`, `live'` is `live`, and the match judgements coincide; its Lean proof is
left to phase 3, where a simulation may need `SCong Binders.none db a b ↔ Cong db a b`
for slot-free `db`.

## Parser subset

`Slotted/Tests/Parse.lean` reads `(sort …)`, `(datatype …)` and `(constructor … :binder …)`
declarations into a binder signature (binder indices count the non-payload columns and bind
in the child after the last of them), `(let x e)` as a substitution of the ground term (or
concrete slot) for later uses of `x`, top-level `(union a b)` and ground terms as runs of
empty-query rules, `(rewrite lhs rhs :when (…) :name "…")` and `(rule …)` as rules of the
default ruleset, `(run N)` as `N` rounds, `(check …)` and `(fail (check …))` as checks, the
predicates `=`, `!=`, `free`, `not-free`, `free-names-are`, `renaming-=`, `renaming-!=`, and
`(push)`/`(pop)` by saving and restoring the state. A file with several checks becomes one
program per check.

Skipped forms, with the reason: `subst` (a representative choice outside the semantics),
`extract` (output, not a check), `include` (external files), `__internal-*` checks,
`datatype*`, `function`, `relation`, `run-schedule`, `:ruleset`. On
`egglog-experimental/tests/slotted` the parser accepts 35 of 50 files with 205 checks,
including all six `paper/` files; the 15 skipped files are 9 `include`, 3 `subst`, 2
`__internal-holds`, and 1 `datatype*`. Three accepted files contain declarations only.

## Interfaces used by the pass and its correctness proposition

- `Slotted.Program` and `Program.Eval`/`SEval` as the source side of the pass's correctness
  statement, `SReach` for the schedule-level simulation, `SameMeaning'` for its fixpoints.
- `Renaming` with `comp`, `inv`, `restrict`, `id`, `update`, `Covers`, and `Renames`, the
  action, to state what the compiled renaming columns mean.
- `SCong`, `reps'`, `live'` and `SQueryMatches` to state the matching correspondence;
  `liveSlots` as the meaning of the compiled free-slot analysis `FS`.
- The parser, to read the slotted corpus for the pass's own tests, and the bounded evaluator
  as an oracle on small cases.
- Open: the conservative-extension theorem (above); completeness of the bounded closure on
  a universe, which the pass does not need since its executable path is the target
  interpreter on compiled programs.

# The slotted pass (phase 2)

Phase 2 compiles a slotted program, a plain `Program` with its binder signature, to a plain
program over the primitive target semantics and interpreter below, following the paper's
"Representation and Slotted Maintenance" and "E-Matching" subsections and the Rust compiler
under `egglog-experimental/src/slotted/`. The pass is `Slotted.compile`
(`Slotted/Encode.lean`); `Slotted.encode` is its total form and `Program.encode` applies it
to a `Slotted.Program`.

## The target extension

The compiled program needs two things the plain specification lacks: primitive values
(slot sets, renamings, lists of renamings, lists of slot sets, booleans, and the integer
generation of a row) with primitive functions on them, and analyses with a merge function
(`FS` by intersection, `G` by union).

**Why no new constructor.** `Expr.min` is the one computation of the plain specification. A
new constructor `Expr.prim` would be the natural generalization, but `Expr` is matched
exhaustively at 126 sites in 37 modules outside `Slotted/`, and `Matches` is inverted in
about 195 proof steps; every such definition and proof would have to change. The pass keeps
the existing definitions and proofs intact by encoding
primitive values and primitive applications as applications of reserved `@`-names and adds
the primitive step as a separate evaluation layer (`Slotted/Target/`), without touching
`Spec/`:

- A **value** is a canonical term: a slot `$s` is itself; a slot set is `@set(s₁, …, sₙ)`
  with the names sorted and distinct; a renaming is `@ren(@pair(s₁, t₁), …)` sorted by key
  and functional (a frame is a renaming value too, and frames are not injective); a list of
  renamings (a group, or the results of `final-refine`) is `@rens(m₁, …)`; a list of slot
  sets (distinctness cliques) is `@sets(A₁, …)`; the booleans are `@true()` and `@false()`;
  a generation is an integer literal. Value heads applied to non-canonical arguments
  evaluate to the canonical form (`Prim.eval`).
- A **primitive application** is `@op(args)` for `op` in the catalogue below. The
  **primitive step** `Prim.norm?` reduces a term bottom-up: every application of a primitive
  name is replaced by its value, and `none` is a stuck computation. `Target.evalExpr e σ`
  is `Expr.eval` followed by that step.
- The target semantics `Target.Eval` (`Slotted/Target/Spec.lean`) is the plain `Eval` with
  `Target.evalExpr` in place of `Expr.eval` in matching: `TExpr.Matches` reads a
  non-primitive application as a live row of its *reduced* instance and a primitive
  application by evaluating its operands, which need not be stored. In particular, the
  placeholder keys passed to `fresh` are constants of the rule, not rows. Ordinary literals
  and table applications still require live membership. `TMatches` compares the reduced
  values of an equality or disequality, equal when identical or congruent; the membership
  pattern `@mem(x, e)` binds `x` to an element of the value of `e`. Query variables are
  *match variables*, bound to representatives as in `ValidEnv`, except the **computed
  variables** of a query: a variable `v` whose defining pattern is `v = @op(…)` or
  `@mem(v, …)` (`computedVars`) is bound by that pattern and exempt from the representative
  requirement. Actions are plain: the pass binds every computation in the query, so
  `evalActions`, `Database`, `Cong`, `reps`, `live` and `SameMeaning` are reused unchanged,
  and `TRunRules`, `TReach`, `Target.Eval` and `Target.Diverges` are the plain definitions
  over `TQueryMatches`.
- On a program without primitive names, `Prim.norm?` is the identity on every term the
  program can build, so the target semantics is the plain one; phase 3 may prove this
  conservativity where it needs it.

**Analyses with merge.** `FS(a, A)` and `G(a, Π)` are tables with a functional dependency
and a merge function. They compile to a row plus the paper's rule form of a merge annotation
(`def:fd-rule`): `FS(a, A) ∧ FS(a, B) ∧ C = A ∩ B ∧ C ≠ A ⇒ FS(a, C), subsume(FS(a, A))`
and the same for `G` with union, so the target needs no merge feature. The symmetries
themselves are the paper's `Sym(a, π)` rows; `G(a, Π)` collects them into one value for the
comparisons `=` and `!=` (`cosetSame`).

### The primitive catalogue

Arguments are values; a primitive is stuck (`none`) off its domain.

| Primitive | Meaning |
| --- | --- |
| `@set(s…)`, `@ren(@pair(s,t)…)`, `@rens(m…)`, `@sets(A…)`, `@true()`, `@false()` | value constructors, canonicalized |
| `@img(m)`, `@dom(m)` | image and domain of a renaming, as slot sets |
| `@inv(m)`, `@comp(m, m′)`, `@restrict(m, A)`, `@id(A)` | `m⁻¹`, `m ∘ m′` (`s ↦ m(m′(s))`), `m|_A`, `id_A` |
| `@apply(m, s)` | `m(s)`; stuck when `s ∉ dom(m)` |
| `@union(A, B)`, `@inter(A, B)`, `@diff(A, B)` | set operations |
| `@elem(s, A)` | `s ∈ A`, a boolean |
| `@isPerm(π, A)` | `π ∈ Perm(A)`: a bijection of `A` |
| `@align(m₁, …, mₙ)` | the union of renamings, defined when they agree and the result is injective (Collide) |
| `@extend(m, S, B)` | `extend(m, S, B)`: `m` extended injectively to `S`, fresh names outside `img(m) ∪ B` (Migrate) |
| `@mint(L)` | the least canonical name outside `L` (binder refresh) |
| `@succ(g)` | `g + 1` on an integer literal (the generation of a replacement) |
| `@gunion(Π, Π′)` | union of renaming lists (the merge of `G`) |
| `@cosetSame(μ, μ′, Π)` | `∃π ∈ Π. μ′ ∘ π = μ` |
| `@fresh(S, U)` | placeholders: an injection of `S` into placeholder names outside `U` |
| `@cliques(A…)` | the distinctness cliques `distinct(A) ∪ …` |
| `@identity(A)` | the frame with every placeholder in `A` in its own block |
| `@unify(F, m, m′, C)`, `@unify1(F, p, p′, C)` | identify `m(t)` with `m′(t)` for `t ∈ dom m ∩ dom m′` (or `p` with `p′`) and re-close; stuck when a clique of `C` would share a block |
| `@refine(F, C, D)` | `final-refine`: every consistent coarsening of `F` by merging blocks touched by `D`, as a renaming list; read with `@mem` |
| `@anchor(q, ν)` | `anchor`: names the blocks, `q′(ν(s)) = s` for `s ∈ dom ν`, fresh names for the others |

A frame is itself a renaming on placeholders, sending each placeholder to the least member
of its block; placeholders are the slot names `$@0, $@1, …` minted by `@fresh`, and final
names from `@anchor`, `@extend` and `@mint` are the least unused of `$0, $1, …`.

## The pass

| Module | Contents |
| --- | --- |
| `Slotted/Target/Values.lean` | the value kinds as canonical terms, their encoders and decoders, fresh names |
| `Slotted/Target/Prim.lean` | the catalogue, `Prim.eval`, `Prim.elements`, `Prim.norm?`, the frame operations |
| `Slotted/Target/Spec.lean` | the target semantics `Target.Eval` and `Target.Diverges` |
| `Slotted/Target/Interp.lean` | the executable e-graph interpreter for target programs (`Target.observe`) |
| `Slotted/Spec/Divergence.lean` | `SDiverges`, divergence of a slotted schedule |
| `Slotted/Encode/Layout.lean` | constructor layouts: term children, binding fields, payload columns inferred from the program; the generation column; the representation `repr` of a ground term |
| `Slotted/Encode/Maintenance.lean` | the maintenance rules and the rebuild schedule |
| `Slotted/Encode/Query.lean` | flattening, binder normalization, frames, query compilation, the guards, action compilation |
| `Slotted/Encode/Premises.lean` | well-bound expressions, payload consistency, action scope and source-round equivariance |
| `Slotted/Encode.lean` | `compile`, `encode`, the schedule and the check, `Pass.Correct`, `fragmentReport` |

**Representation.** A constructor position is a binding position (`bind`), a payload column
(some occurrence holds a literal there; inferred per program, as the Rust declares it) or a
term child. A term child becomes two columns, a renaming and the child; a binding position
holds its slot; a payload column holds its value; and every row's first column is its
**generation**, an integer. The slot leaf is `$0`: `repr($s) = $0` and the edge to it is
`[$0 ↦ $s]`; `repr(f(t̄))` keeps the source names at every other level, so the edge to a
non-leaf child is the identity on its free slots, and writes generation `0`. This is the
paper's initialization of the distribution example, with the generation added.

**Maintenance** (`Maintenance.lean`), with the paper's names: `nodeFS_f` and the leaf fact
`FS($0, {$0})`; `intersectFS` (the `FS` merge), `transportFS`, `symFS`; `identity`, `reverse`,
`orient`, `edge`, `compress`, `parents`; `symIdentity`, `symEquation`, `symmetry`, `group`,
`inherit`, `trimLeader`, `trimSym`, the `G` collection and merge; per constructor `collide_f`
(the union of the children's correspondences and the binder alignment is `@align`),
`migrate_f`, `child_f,j`, `restrict_f,j`, the binder rules `refresh_f,k,u` and
`shadow_f,k,k′`, and `dedup_f`. A source run compiles to the compiled rules followed by
`saturate(run M)`, as the paper says.

**Queries** (`Query.lean`). A query is flattened to depth-one atoms over fresh root
variables; a ground source term (a `let` global substituted by the parser) is matched
structurally the same way, its concrete slots living on a pseudo-root whose local names are
the global names, so two concrete slots stay distinct and a pattern slot may coincide with
one; its binders, which carry no identity, are α-renamed to fresh pattern slots kept apart
from the concrete slots. Each atom's node slots receive placeholders by `@fresh`; the first
occurrence of a variable defines the placeholders of its class slots through the edge that
carries it, and every later occurrence, including the root of a nested atom, is read
through a symmetry `Sym(c, π)` and joined by `@unify`; a pattern slot is a placeholder
unified with the column that carries it; a row's generation is a wildcard. The cliques are
the node slots of each atom, the concrete slots with the ground binders, and the written
pattern slots. `@refine` ranges over the aliasings of the placeholders reached by variables
and by carried pattern slots (written slots outside binding positions); `@anchor` restores
the root's class slots. From the anchored frame the pass reads `μ_v = q′ ∘ ν_v` for every
variable and `$v′ = q′(q_v)` for every pattern slot; `NotFree($s, e…)` is
`@elem($s′, ⋃ img μ) = @false`, `Free` the positive test, `free-names-are(e, s̄)` is
`img(μ_e) = {s̄′}`, `renaming-=` is class equality, `=` is class equality with
`@cosetSame(μ₁, μ₂, Π) = @true` under `G(c, Π)`, and `!=` is the disjunction of class
disequality and `@cosetSame = @false`: a rule with `k` such guards compiles to `2^k` rules,
and a check with one compiles to goal rules writing `@Goal()` after the schedule and the
check `@Goal()`.

**Actions.** A right-hand side is built bottom-up in the anchored frame at generation `0`:
a variable child is `(μ_v, c_v)`, a slot is the leaf with edge `[$0 ↦ s′]`, a nested build
is a child at the identity on its estimated free slots, a binding position holds `s′`.
`rewrite` unions the built term with the root class; a bare-variable right-hand side
inserts `Equated(root, μ_v, c_v)`; a rule's `union(e₁, e₂)` is a plain union of two builds,
`Equated` when a side is a variable, and a plain union when the variable side is the anchored
root. Slots used only in actions receive placeholders of their own and fresh names from
`@anchor`.

**Rejections.** `compile` returns `.error` for unsupported programs: source `min` or
`subsume`; names in the generated `@` or placeholder `$@` namespaces; inconsistent arities;
applied slots; duplicate, unordered, out-of-range or overlapping nonidentical binder scopes;
a binder binding itself, another binder or a payload; inconsistent payload/term variable
roles; non-slot binders; predicates inside terms; literals built or unioned as terms;
mixed payload/term comparisons; bare-slot query roots or union endpoints; unbound head
variables; unkeyed query variables; and concrete action slots absent from the query's global
frame (use a fresh slot variable). The unrestricted corpus uses none of these unsupported
forms. The gate explicitly rejects the one `nested/` fixture's restricted-aliasing execution
policy after verifying it with Rust's `--slotted-no-aliasing`; it is not silently omitted.

## Deviations from the paper and the reference

Each choice that departs from the paper's displayed rules, with its reason:

1. **Generations.** Every row carries a generation; an update writes its replacement at the
   replaced row's generation plus one and subsumes the replaced row in the same action. The
   paper's separate cleanup rules subsume the replaced row "once its replacement is
   present", and the reference deletes it. In the plain target `subsume` marks a row key
   for good, in every spelling: on `paper/fgh-transitive-symmetry.egg` the follower
   `H($2,$1)` is migrated into `G($1,$2)` and retired, and when a later union makes the
   class of `F($1,$2)` the leader, the migration of `G($1,$2)`'s rows back into it
   recreates exactly the retired spelling, which can never be live again, so the leader has
   no `H` row and `(check (= f12 h21))` fails. With generations the recreated row is a new
   key. Its cost is `Dedup_f`, which retires the older of two live rows with one spelling
   (a migration into a class that already holds the spelling creates such a pair), and the
   generation wildcard in every compiled pattern.
2. **No retirement of reversed leader edges.** A union can make a follower smaller than its
   leader. The reference drops the stale edge; subsuming a `Leader` row would retire a key
   that a second reversal needs again. The edge stays, every update fires only toward the
   smaller class (`b = min(a, b)` in Migrate and in Child, as the reference's
   `ordering-max` guards), so a reversed edge is inert, and `Orient` adds the edge the
   right way round.
3. **Binder refresh and shadowing** (`Refresh`, `Shadow`), from the reference: a bound name
   also used outside its scope is renamed in the binder and its covered children, and of two
   binding positions of one scope with one name the earlier, which binds nothing, is
   renamed. The paper mentions the freshening in one sentence.
4. **Ground terms in queries** are matched structurally, like patterns, rather than looked
   up through `Leader(repr(t), γ, c)`: a global's concrete slots are the names of a
   pseudo-root and its binders become fresh pattern slots that may not alias a free slot.
   The lookup form can fail on globals whose stored spelling is no longer the leader's.
5. **`!=` as a disjunction.** The target has no negation; `!=` between matched terms is
   "different classes, or one class and renamings outside the group", compiled by rule
   splitting; a check with such a guard compiles to goal rules.
6. **Numeric slot names** `$01`, `$+1` are read as `$1` by the parser, as the reference
   reads them (`named-slots.egg`).
7. **`Equated` for a union with a variable side**, as the paper says for a bare-variable
   right-hand side, extended to any `union` whose side is a matched variable other than the
   anchored root, whose renaming is the identity.
8. **One saturation.** The rebuild is `saturate(run M)` over all maintenance rules, as the
   paper says; the reference runs its rulesets in phases, which the pass does not need.

9. **Explicit symmetry enumeration and pairwise collisions.** The pass follows the paper's
   `Sym` and `align` rules. It does not use the reference's shape indexes, coset reading
   indexes, canonical invocation keys or stored-match tables. `@refine` enumerates all
   consistent partitions without a prefix cutoff; the interpreter finds every firing
   against the pre-state before applying actions.
10. **Payload inference and the target layer.** The source model is untyped and has no
    declarations. Literal occurrences determine payload columns; incompatible uses are
    rejected. The target adds the reserved primitive layer described above, and compiles
    `FS`/`G` merges to rows plus functional-dependency rules. Its snapshots describe that
    target, not standalone inputs for the unextended Rust interpreter.
11. **`SymFS` exposed.** `symFSRule` is the self-equation instance of Transport, shortcutting
    `symEquationRule` followed by `transportFSRule`. The supplied paper text displays the
    latter two rules rather than a separately named SymFS. Both directions are retained;
    intersection removes redundant symmetry orbits.
12. **Unrestricted matching only.** The paper's optional restricted-aliasing mode is outside
    the pass. Its `nested/binder-safe-matching.egg` fixture is reported as an explicit policy
    rejection, verified with Rust's corresponding mode, and is not counted as an agreement.

### Rule names and paper nodes

All rule names below are in `Egglog.Slotted.Encode`; the primitive is in
`Egglog.Slotted.Target`. The three maintenance lists are `analysisRules`, `leaderRules`
(including Collide), and `updateRulesAll`. `maintenanceGroups` combines them and `rebuild`
saturates their union. The display block is `slotted-pass` in `paper/semantics.tex`.

| Paper rule or operation | Lean declaration | Blueprint node |
| --- | --- | --- |
| Slot leaf, NodeFS | `leafFSRule`, `nodeFSRule` | `def:slotted-fs-rules` |
| FS intersection, SymFS, Transport | `intersectFSRule`, `symFSRule`, `transportFSRule` | `def:slotted-fs-rules` |
| Identity, Reverse, Orient, Edge | `identityRule`, `reverseRule`, `orientRule`, `edgeRule` | `def:slotted-leader-rules` |
| Compress, Parents | `compressRule`, `parentsRule` | `def:slotted-leader-rules` |
| SymIdentity, SymEquation, Symmetry | `symIdentityRule`, `symEquationRule`, `symmetryRule` | `def:slotted-leader-rules` |
| Group, Inherit | `groupRule`, `inheritRule` | `def:slotted-leader-rules` |
| TrimLeader, TrimSym | `trimLeaderRule`, `trimSymRule` | `def:slotted-leader-rules` |
| G collection and union merge | `gCollectRule`, `gMergeRule` | `def:slotted-leader-rules` |
| align; Collide | `Target.align`; `collideRule` | `def:slotted-align`; `def:slotted-collide` |
| Migrate with extend, Child, Restrict | `migrateRule`, `childRule`, `restrictRule` | `def:slotted-term-updates` |
| Binder refresh, shadowing, generation deduplication | `refreshRule`, `shadowRule`, `dedupRule` | `def:slotted-term-updates` |
| Replacement and nonleader subsumption | `updateRule` | `def:slotted-term-updates` |
| Maintenance between user rounds | `rebuild`, `compileSchedule` | `def:slotted-rebuild` |
| Distribution, frames, NotFree, fresh actions, variable RHS | `compileRule`, `emitFrame`, `emitGuards`, `compileAction` | `def:slotted-compile-rule` |

## The correctness statement for phase 3

For `P` with binder signature `β`, `Pass.Premises P` and `compile β P.plain = .ok P′`,
`Slotted.Pass.Correct P` asks for

```
(∀ o : Result, Target.Eval Database.empty P′ o ↔ Slotted.SEval β Database.empty P.plain o) ∧
(Target.Diverges Database.empty P′.schedule ↔ Slotted.SDiverges β Database.empty P.plain.schedule)
```

`Encode/Premises.lean` defines the premises: `Binders.WF`; `WellBound` (in-range
annotations and slot literals or variables at binding positions); `PayloadConsistent`;
`Scoped` (query-bound head variables, except fresh action slots); and `Commutes` for every
source rule. `Commutes` says that a source round commutes up to `SameMeaning'` with a
bijective slot-name permutation fixing the rule's concrete constants. `NamePermutation`,
`renameTerm`, `renameDatabase` and `FixesConstants` define that statement; none mentions
the target or assumes its correctness. This premise's applicability is a phase 3 obligation.
Successful compilation checks namespace separation, arities, supported forms, keyed queries,
payload/term roles, source ordering exclusion and head scope.

The proof will relate target and source states by decoding classes through leaders and `FS`,
using `reps'`, `live'`, `liveSlots` and `SQueryMatches` from phase 1. Generation is invisible
to decoding. `Correct` is a definition of a proposition; no proof is claimed, and
`ExtlogTheorems.lean` is unchanged. Interpreter adequacy, maintenance termination and
simulation, matching completeness, and conservativity of the target primitive layer remain
phase 3 work. `SDiverges` is the plain divergence definition over `SReach` and `SameMeaning'`.

## Composition with the congruence pass

The target is outside `Program.Fragment`, recorded by `fragmentReport` and printed for every
check and final program. Generated names violate `noAt`; maintenance takes `min` over class
variables inside saturation (`ordering`); primitive queries are neither keyed table reads
nor `min` (`queryEncodable`); variadic value/primitive heads violate `aritiesAgree`; and
integer generations alongside unions through class variables violate `noLitUnion`.
Every one of the 235 compiled asserted checks fails exactly these five clauses.
Of the 41 final programs, 25 fail the same five clauses. The other 16 have no constructor
occurrences (declaration-only files and states restored by `pop`) and fail only `ordering`,
`noAt`, `queryEncodable`: `binder-tests`, `carrier-name`, `datatype`, `egglog-surface`,
`lambda-binders`, `languages/{array,sdql,toy}`, `own-sort`, `proof-conditions`,
`proof-renaming-guards`, `rewrite-tests`, `sdql-binders`, `sdql-sum-sing`, `symmetry-tests`,
and `variable-names`. `headsScoped` holds throughout.
The exact per-program clauses remain in the gate output; this is not a claim that the
existing congruence correctness theorem applies to the slotted output.

## Execution and the gate

`Slotted/Target/Interp.lean` uses a hash-consed e-graph, union-find with congruence closure,
subsumption modulo congruent children, representatives by `Term.blt`, and a matcher joining
table atoms and computing primitive bindings in dependency order. `@mem` ranges over all
refinements. Row lookup recognizes unstored spellings with congruent children; ordinary
literals and table applications must still match live rows. Primitive computations can use
unstored constants. `Tests/Compile.lean` checks these boundaries and explicit rejections.

`slotted-compile.sh` first classifies every file, then confirms accepted files' assertions
against Rust in their required mode. It explicitly rejects the restricted-aliasing fixture.
For the remaining files, `difftest slotted-compile` compiles and executes every asserted check
and the final program, including files without checks and commands after the last check.
A reference failure, process error, timeout, exhausted saturation budget or disagreement fails
the gate. Explicit parser/compilation/policy rejections are counted separately.
`DIFFTEST_TIMEOUT` is a per-process limit (600 seconds by default); the interpreter budget is
256 passes per saturation. Neither limit constitutes evidence of semantic divergence.

`difftest slotted-trace <file> <case> [<index>|<substring>]` prints states after commands and
matches of query prefixes. `make lean-update-egg-snapshots LAKE="lake --no-cache"` writes the
hand-written compiled programs as `*.slotted.egg`, checked by `lean-slotted-egg-test` in
`lean-check`. Snapshots use the target's untyped term syntax and reserved primitive catalogue;
they are not standalone programs for the unextended Rust binary.

The seven hand-written files cover alpha-equivalence, capture, distribution, frames and
fresh action slots, redundant slots, variable right-hand sides, and symmetries. Their 32
checks plus the unrestricted corpus's 203 checks give **235 agreements, zero disagreements**:
57 files, 42 parser-accepted, 41 compiled, 1 policy rejection, 15 parser rejections.
All six `paper/` files (18 checks) and distribution (2 checks) agree. No Rust binary rebuild
or source modification is needed; no Python file is changed.

### Per-file report

Corpus paths are relative to `egglog-experimental/tests/slotted/`; `hand/` denotes
`semantics/tests/slotted/`. Counts are asserted `check`/`fail` outcomes, not synthetic final
programs. Declaration-only files are compiled and executed with an empty final query.

| File | Checks | Status |
| --- | ---: | --- |
| `atom-identities.egg` | — | parser rejection: `include` |
| `bare-slot-union.egg` | 5 | compiled; all agree |
| `binder-scope.egg` | 4 | compiled; all agree |
| `binder-tests.egg` | 24 | compiled; all agree |
| `carrier-name.egg` | 3 | compiled; all agree |
| `coset-direction.egg` | — | parser rejection: `include` |
| `datatype.egg` | 7 | compiled; all agree |
| `egglog-surface.egg` | 18 | compiled; all agree |
| `lambda-binders.egg` | 8 | compiled; all agree |
| `languages/array-rules.egg` | — | parser rejection: `include` |
| `languages/array.egg` | 0 | compiled; declarations only |
| `languages/sdql-rules.egg` | — | parser rejection: `include` |
| `languages/sdql.egg` | 0 | compiled; declarations only |
| `languages/toy.egg` | 0 | compiled; declarations only |
| `multipattern.egg` | — | parser rejection: `subst` |
| `multiple-sorts.egg` | — | parser rejection: `datatype*` |
| `named-slots.egg` | 13 | compiled; all agree |
| `nested/binder-safe-matching.egg` | 2 | policy rejection: restricted aliasing (Rust verified) |
| `own-sort.egg` | 7 | compiled; all agree |
| `paper/enode-collisions.egg` | 4 | compiled; all agree |
| `paper/fgh-transitive-symmetry.egg` | 2 | compiled; all agree |
| `paper/figure-3.egg` | 3 | compiled; all agree |
| `paper/redundancy-orbit.egg` | 4 | compiled; all agree |
| `paper/two-redundant-slots.egg` | 3 | compiled; all agree |
| `paper/var-xy-eq-yz.egg` | 2 | compiled; all agree |
| `proof-child-freshness.egg` | 1 | compiled; all agree |
| `proof-conditions.egg` | 6 | compiled; all agree |
| `proof-group-restriction.egg` | 1 | compiled; all agree |
| `proof-node-symmetry.egg` | 1 | compiled; all agree |
| `proof-redundant-certificate.egg` | 1 | compiled; all agree |
| `proof-renaming-guards.egg` | 6 | compiled; all agree |
| `query-predicates.egg` | — | parser rejection: `__internal-holds` |
| `redundancy-tests.egg` | — | parser rejection: `__internal-holds` |
| `refinement-complete.egg` | — | parser rejection: `include` |
| `rewrite-tests.egg` | 6 | compiled; all agree |
| `rudi/bound-aliasing-rel-decoded.egg` | 2 | compiled; all agree |
| `rudi/bound-aliasing.egg` | 1 | compiled; all agree |
| `rudi/relation.egg` | 6 | compiled; all agree |
| `rudi/unify-redundant-and-symmetric-appid-decoded.egg` | 2 | compiled; all agree |
| `sdql-batax.egg` | — | parser rejection: `include` |
| `sdql-beta.egg` | — | parser rejection: `subst` |
| `sdql-binders.egg` | 22 | compiled; all agree |
| `sdql-paper-batax.egg` | — | parser rejection: `subst` |
| `sdql-paper-mmm.egg` | — | parser rejection: `include` |
| `sdql-rewrites.egg` | — | parser rejection: `include` |
| `sdql-sum-sing.egg` | 2 | compiled; all agree |
| `subst-refresh.egg` | — | parser rejection: `include` |
| `symmetry-tests.egg` | 27 | compiled; all agree |
| `symmetry-with-redundancy.egg` | 4 | compiled; all agree |
| `variable-names.egg` | 8 | compiled; all agree |
| `hand/alpha.egg` | 6 | compiled; all agree |
| `hand/capture.egg` | 4 | compiled; all agree |
| `hand/distribution.egg` | 2 | compiled; all agree |
| `hand/frames.egg` | 8 | compiled; all agree |
| `hand/redundant.egg` | 4 | compiled; all agree |
| `hand/rewrite-variable.egg` | 4 | compiled; all agree |
| `hand/symmetry.egg` | 4 | compiled; all agree |

### Validation

Run from `semantics/` with the supplied Rust binaries, `LEAN_NUM_THREADS=4`,
`RAYON_NUM_THREADS=1`, `CARGO_BUILD_JOBS=4`, and the shared `CARGO_TARGET_DIR`:

| Command | Exit | Result |
| --- | ---: | --- |
| `make lean-check LAKE="lake --no-cache"` | 0 | Whole library and hole audit; 116 congruence, 116 provenance and 104 resugaring cases; 29 existing snapshots; Rust certificate test; parser report; 7 slotted snapshots |
| `make lean-difftest` | 0 | 116 passed, 0 failed, 0 skipped |
| `make lean-compiled-difftest` | 0 | 116 passed, 0 failed |
| `make lean-slotted-difftest` | 0 | 18 paper checks agree, 0 disagree, 0 undecided |
| `make lean-slotted-compile` | 0 | 235 checks agree; file statuses above; 0 disagreements, 0 undecided, 0 execution errors |
| `make paper-check LAKE="lake --no-cache"` | 0 | Seven-page PDF; no overfull boxes |
| `make lean-update-egg-snapshots LAKE="lake --no-cache"` | 0 | Seven slotted snapshots; the 29 existing plain snapshots are unchanged |

No Python source was changed, so root `make nits` was not run. `paper-sync` was not run.
`ExtlogTheorems.lean`, the Rust subtrees and the restored `Cargo.lock` are unchanged.
