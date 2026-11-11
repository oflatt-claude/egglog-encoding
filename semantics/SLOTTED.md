# Slotted semantics (phase 1)

The slotted layer ports the "Slots and Binders" and "E-Matching" semantics of the paper's
slotted section onto the plain specification under `EgglogSemantics/Spec/`, without
changing it. Phase 2 will add the slotted pass, which compiles a slotted program to a plain
one; its correctness statement relates the slotted evaluation defined here (`SEval`) with the
plain `Eval` of the compiled program.

## What exists

| Part | Module |
| --- | --- |
| The specification, one blueprint node per displayed definition, rendered by the `slotted` blocks of `paper/semantics.tex` under `make -C semantics paper-check` | `Slotted/Spec/{Binders,Slots,Congruence,Match,Eval,Step}.lean` |
| The parser for the slotted `.egg` subset, one slotted program per check, and its corpus report (`difftest slotted-parse`, `make -C semantics lean-slotted-parse`) | `Slotted/Tests/Parse.lean`, `DiffTest.lean` |
| The specification evaluated over a finite slot universe and a finite term universe, with soundness of what it finds | `Slotted/Tests/Bounded.lean` |
| The paper's distribution example and the `tests/slotted/paper` phenomena as `#guard`s, and the conservative-extension test against the plain interpreter | `Slotted/Tests/Examples.lean` |

## Layering

Slots are ordinary terms: the slot `$s` is `Term.app "$s" []`, recognised by its head
(`Term.isSlot`); its name is spelled with the `$`. In queries and actions a written slot `$v`
is a *slot variable*, `Expr.var "$v"`: local to the rule or check, and a match assigns slot
variables injectively to slot names. A concrete slot, such as one a `let` binds, is the term
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
| redundant slot; live free slots `FS(E, t)` | `Redundant`, `liveSlots` | `def:slotted-live-slots` |
| `reps'(E)`, `live'(E, X)` | `sreps` (least stored spelling under `SCong`), `reps'`, `subsumed'`, `SameRow'`, `live'` | `def:slotted-reps` |
| slotted `G ≡ G'` | `SameMeaning'` | — |
| `Query'`, `App'`, injective pattern slots `θ`; `Free`, `NotFree`, `free-names-are`, `renaming-=` | `SExpr.Matches`, `SMatches`, `ValidEnv'`, `SQueryMatches`, `SQueryHolds`, `Builtin`, `RenamingEq` | `def:slotted-query` |
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
`slots t` without its redundant slots: the paper's `FS`, which `free`, `not-free` and
`free-names-are` inspect.

### Pattern slots and fresh action slots

The paper assigns the written pattern slots injectively, `θ : PS(Q) ↣ Slot`, before the
rules apply. Here `θ` is the part of the match `σ` on the slot variables: `ValidEnv'` binds
each slot variable to a slot, distinct slot variables to distinct slots, and every other
variable to a member of `reps'`. A slot variable of the actions that the query does not
bind receives, in `SRunRules`, a slot that no value of the match mentions; every such choice
is a result of the round, and the choices differ by a renaming of fresh slots.

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
  a bare variable ranges over `reps'`, a slot variable over `S`) whose output is filtered by
  the reference evaluators;
- `round`, `exec`, `observe`: the slotted round under every fresh choice from `S`, schedules
  with fuel, and the outcome of a slotted program. A check is decided on the universe seeded
  with the instances of its expressions under every assignment.

What is bounded: a pair the closure does not relate, a slot it does not find redundant, and a
check it finds to fail are statements about the universe. `Examples.lean` says for each
assertion which kind it is. The paper's example needs four slot names: two for the stored
binders and two fresh ones for their α-variants.

## Conservative extension

For a program without slots, under the empty binder signature and the empty slot universe,
the slotted evaluator and the plain interpreter agree on four small programs (a union, a
failing check, a saturation, a disequality guard) in `Examples.lean`. The theorem that
`SEval Binders.none` and `Eval` coincide on slot-free programs is stated in prose only: on a
slot-free store `Renames` is the identity and the `rename` rule adds nothing beyond the
reflexivity of slot terms, which no slot-free query can see, so `SCong` is `Cong` there,
`reps'` is `reps`, `live'` is `live`, and the match judgements coincide; the Lean proof is
left to phase 2, which needs the lemma `SCong Binders.none db a b ↔ Cong db a b` for
slot-free `db` in its own simulation.

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
`egglog-experimental/tests/slotted` the parser accepts 29 of 44 files with 189 checks,
including all six `paper/` files; the 15 skipped files are 8 `include`, 3 `subst`, 2
`__internal-holds`, 1 `datatype*`, and 1 `extract`.

## What phase 2 needs from phase 1

- `Slotted.Program` and `Program.Eval`/`SEval` as the source side of the pass's correctness
  statement, `SReach` for the schedule-level simulation, `SameMeaning'` for its fixpoints.
- `Renaming` with `comp`, `inv`, `restrict`, `id`, `update`, `Covers`, and `Renames`, the
  action, to state what the compiled renaming columns mean.
- `SCong`, `reps'`, `live'` and `SQueryMatches` to state the matching correspondence;
  `liveSlots` as the meaning of the compiled free-slot analysis `FS`.
- The parser, to read the slotted corpus for the pass's own tests, and the bounded evaluator
  as an oracle on small cases.
- Open: the conservative-extension theorem (above); completeness of the bounded closure on
  a universe, which phase 2 does not need since its executable path is the plain
  interpreter on compiled programs.
