# Slotted semantics (phase 1)

The slotted layer ports the "Slots and Binders" and "E-Matching" semantics of the paper's
slotted section onto the plain specification under `EgglogSemantics/Spec/`, without
changing it. Phase 2 will add the slotted pass, which compiles a slotted program to a plain
one; its correctness statement relates the slotted evaluation defined here (`SEval`) with the
plain `Eval` of the compiled program.

## Plan

1. `Slotted/Spec/`: the mathematical specification, one blueprint node per displayed
   definition, rendered by `make -C semantics paper-check` through the `slotted` blocks of
   `paper/semantics.tex`.
2. `Slotted/Tests/Parse.lean`: a parser for the slotted `.egg` subset, with the report of
   which corpus files it accepts (`difftest slotted-parse`).
3. `Slotted/Tests/Bounded.lean`: executable evaluators of the specification over a finite
   slot universe and a finite term universe, with soundness theorems for the positive
   direction, and `Slotted/Tests/Examples.lean`: the paper's distribution example and the
   `tests/slotted/paper` phenomena as `#guard`s.
4. The conservative-extension statement: a slot-free program with empty binders has the same
   slotted and plain outcome.
5. Stretch: a finite reference interpreter and a `slotted` difftest gate, in a separate commit.

## Layering

Slots are ordinary terms: the slot `$s` is `Term.app ("$" ++ s) []`, recognised by
`Term.isSlot`. In queries and actions a written slot `$v` is a *slot variable*,
`Expr.var "$v"`: it is local to the rule or check, and a match assigns slot variables
injectively to slot names. A concrete slot, such as one a `let` binds, is the term
`Expr.app "$s" []`. No core type changes; the plain `Cong`, `Matches`, `Reach` and `Eval` are
untouched, and the slotted definitions live beside them in namespace `Egglog.Slotted`.

A slotted program is a plain `Program` together with a binder signature
`Binders := FnName → List (Nat × Nat)`; the pair `(j, i)` is the paper's
`(j, i) ∈ bind(f)`: argument `j` is a binding position whose slot is bound in argument `i`.

## Definitions and their paper names

| Paper | Lean (namespace `Egglog.Slotted`) | Module |
| --- | --- | --- |
| `bind(f)`, binding positions, `B_i(t)` | `Binders`, `Binders.bindingPositions`, `Binders.boundIn` | `Spec/Binders.lean` |
| slot `$s`, `slots(t)`, all slot names of a term | `Term.slot`, `Term.isSlot`, `slots`, `allSlots` | `Spec/Slots.lean` |
| renaming `m` (finite partial injection), `dom`, `img`, `m⁻¹`, `m ∘ m'`, `m|_A`, `id_A`, `m_s^r` | `Renaming`, `Renaming.WF`, `.dom`, `.img`, `.inv`, `.comp`, `.restrict`, `Renaming.id`, `.update` | `Spec/Slots.lean` |
| the action `m * t` with fresh bound names (`def:slotted-action`) | `Renames bind m t t'` (a relation: every fresh choice is a result) | `Spec/Slots.lean` |
| α-equivalence | `AlphaEq bind t u` (`Renames` under the identity on `slots t`) | `Spec/Slots.lean` |
| `Rename` rule, `∼_E` closed under renaming (`def:slotted-congruence`) | `SCong bind db` (the plain rules plus `rename`; slot terms are reflexive) | `Spec/Congruence.lean` |
| redundant slot, live free slots `FS` | `Redundant`, `liveSlots` | `Spec/Congruence.lean` |
| `reps'(E)` (`def:slotted-reps`) | `sreps` (least stored spelling under `SCong`), `reps'` (its closure under renaming) | `Spec/Congruence.lean` |
| `live'(E, X)` | `live'` (`live` with `X` closed under renaming and `∼_E` extended) | `Spec/Congruence.lean` |
| `G ≡ G'` (slotted) | `SameMeaning'` | `Spec/Congruence.lean` |
| `Query'`, `App'`, injective pattern slots (`def:slotted-query`) | `SExpr.Matches`, `SMatches`, `SQueryMatches`, `SQueryHolds` | `Spec/Match.lean` |
| `NotFree($v, x)`, `free`, `free-names-are`, `renaming-=` guards | built-in predicate heads of `SMatches` (`Builtin`) | `Spec/Match.lean` |
| fresh names for action-only slots (`def:slotted-round`) | `FreshSlots`, `SRunRules` | `Spec/Eval.lean`, `Spec/Step.lean` |
| slotted schedules and outcomes | `SReach`, `SEval` | `Spec/Step.lean` |

### The action `m * t`

`Renames bind m t t'` holds when `t'` is a result of `m * t`: slots go through `m`; literals
stay; for an application the binding positions receive pairwise distinct fresh names, fresh
for all slot names of the term and for `dom(m) ∪ img(m)`, each covered child is renamed by
`m` updated at its bound names (`m_s^r = (m \ {$s}) ∪ [$s ↦ $r]`), and every other child by
`m`. The relation is defined exactly when `slots(t) ⊆ dom(m)` and `m` is a partial
injection. Different fresh choices give different results, all α-equivalent; `SCong`'s
`rename` rule takes any result on each side, so α-equivalent spellings of an existing term
are congruent, as the paper states.

### Redundant slots

A free slot `s` of `t` is redundant in `E` when renaming it to a fresh name gives a term
congruent to `t`: `$x·0 ∼ 0` makes `$x` redundant. `liveSlots E t` is `slots t` without its
redundant slots: the paper's `FS`, which `free`, `not-free` and `free-names-are` inspect.

## Executable checking (bounded)

`Slotted/Tests/Bounded.lean` fixes a finite list of slot names `S` and a finite term universe
`U` (closed under subterms and under renaming over `S`) and computes: all partial injections
over `S`; all results of `m * t` with fresh names from `S`; the least relation on `U × U`
closed under the `SCong` rules with renamings over `S`; `sreps`, `reps'`, `live'`, redundant
slots, and the match judgement with slot variables assigned injectively from `S`. Soundness
theorems show that every pair the bounded closure relates is `SCong`-related and that every
match it finds is an `SQueryMatches`; the negative direction (a check that fails) is a
bounded statement and is documented as such in the tests.

## Parser subset

`Slotted/Tests/Parse.lean` reads `(sort …)`, `(datatype …)` and `(constructor … :binder …)`
declarations into a binder signature, `(let x e)` as a substitution of the ground term (or
concrete slot) for later uses of `x`, top-level `(union a b)` and ground terms as runs of
empty-query rules, `(rewrite lhs rhs :when (…) :name "…")` and `(rule …)` as rules of the
default ruleset, `(run N)` as `N` rounds, `(check …)` and `(fail (check …))` as checks, the
predicates `=`, `!=`, `free`, `not-free`, `free-names-are`, `renaming-=`, `renaming-!=`, and
`(push)`/`(pop)` by saving and restoring the parser state. A file with several checks becomes
one program per check (the commands before it, then the check). Skipped forms, with the
reason: `subst` (needs a representative choice outside the semantics), `extract` (output,
not a check), `include` (external files), `__internal-*` checks, and `function`.

## What phase 2 needs from phase 1

- `Egglog.Slotted.Program` (a plain `Program` with its `Binders`) and `SEval` as the source
  side of the pass's correctness statement, `SReach` for the schedule-level simulation.
- `Renaming` with `comp`, `inv`, `restrict`, `id`, `update`, and `Renames`, the action, to
  state what the compiled renaming columns mean.
- `SCong`, `reps'`, `live'` and `SQueryMatches` to state the matching correspondence.
- `liveSlots` as the meaning of the compiled free-slot analysis `FS`.
- The parser, to read the slotted corpus for the pass's own tests.
