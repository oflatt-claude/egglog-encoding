# Slotted-encoding test corpus

33 tests in `slotted-experiments/tests/*.egg`, written in the user-facing dialect
(`Var` / `App1` / `App2` / `Null`, `rewrite` / `let` / `union` / `run` / `check` / `fail`)
and run through `transform.py` on top of `preamble-compiled.egg`.

**25 pass, 8 fail.** Every expectation in the passing set was independently
cross-checked against `memoryleak47/slotted-egraphs` (see
`xcheck-slotted-egraphs.rs`; 27 Rust tests, all agree).

---

## The 8 failing tests

All eight fail in `transform.py` or in the hand-written preamble's coverage, not
in the slotted algebra. Ordered roughly by how deep the fix goes.

| # | What it needs | Fails with |
| --- | --- | --- |
| **26** | conjunctive rule body (`f(x,y) ∧ g(x,y)`) — the whole `mp′` / `find-mapping` story from `slotted-user-rules.md` §"Compiling the body" is untested because `rewrite` is single-rooted. Positive, injectivity-negative, and symmetry-only-`mp′` cases. | `unknown rule type 'rule'` |
| **27** | **fresh slots, soundness.** `f(x,y) ∧ g(x,z)`: `z` is reached only through the second atom, so minimal `mp′` names no slot for it and the action's edge to `z` comes out empty. An empty child edge asserts that slot is redundant *in the child's class* — here the class of every variable. Test only pins the soundness direction (`k($5) ≠ k($6)`), so the "guard and don't fire" fix also passes. | `unknown rule type 'rule'` |
| **30** | **fresh slots, completeness.** Eta-expansion `t → λ$s. (t $s)`: the action introduces a binder over a slot the match never named. Paper §3.6's last paragraph. | `Unbound symbol s` |
| **25** | slot variables in patterns — `(App2 "f" (Var s) (Var t))` must match only variables. Every realistic slotted rule set is written with `(var $x)` patterns (eta's freshness guard, `let-var-same`, `map-fission`). | `stage1: what is ('Var','s')?` |
| **24** | **arity generality.** `App1` is in `preamble-user.egg` but the machinery is hand-written for `App2` only — each arity needs its own α-finder, self-loop, migration, and per-position child-update rules. This is the thing an automatic pass is supposed to generate. | `Unbound function App1` |
| **28** | a `let` whose body mentions an earlier `let` (`(let $b (App2 "g" $a (Null)))`). Needs each global's slot list recorded so the edge to it can be built. | `transform_rhs: what is $a?` |
| **29** | inline terms in `union` / `check`, not only in `let`. They reach egglog unencoded. | `Arity mismatch, expected 5 args` |
| **31** | **scale.** AC over five variables — the case slotted e-graphs should be *good* at, since all the two-slot sums share one class. Fine at `(run 5)`; does not finish in 180 s at `(run 8)`. | timeout |

Not written, because there is no surface syntax to guess at: **side conditions**
(`slot_free_in`). Test 23's eta rule has no freshness guard, so it is unsound on a
capturing body — fine for that test's data, not fine in general.

---

## Test 10 — this one panics the reference implementation

```
union f[$0,$1] with f[$1,$0]     ; symmetry
union f[$0,$1] with g[$0]        ; slot sets differ -> $1 redundant
                                 ; orbit of $1 under <swap> is {$0,$1} -> $0 too
```

Paper §3.5 step 1: *"whenever a slot is marked redundant, then also all slots in
the same orbit of the permutation group needs to be marked as redundant."*
The merged class should end up with **no slots**, so `f($0,$1) = f($7,$8)` and
`g($0) = g($5)`.

`slotted-egraphs` (v0.0.36, `eba0c8a`) **panics** on this:

```
SlotMap::index($f1): index missing!    src/group/mod.rs:167
```

Eight lines to reproduce:

```rust
define_language! { pub enum L { Var(Slot) = "var", F(AppliedId, AppliedId) = "f", G(AppliedId) = "g" } }
let g = &mut EGraph::<L>::default();
uni(g, "(f (var $0) (var $1))", "(f (var $1) (var $0))");   // symmetry first
uni(g, "(f (var $0) (var $1))", "(g (var $0))");            // panics here
```

Swapping the two unions — semantically identical — works fine and gives the
expected slotless class, which is how the cross-check gets a reference answer.
So it is an ordering bug in the orbit-closure path, not a disagreement about the
semantics. The egglog encoding handles **both** orders.

---

## What passes

Ground α-equivalence and injectivity (4, 14); symmetry from rewrites and from
unions, and its propagation to parents (5, 6, 13); group closure of a 3-cycle
without leaking the transposition (7); redundancy from a union, from a rewrite,
through a parent's edge, closed under orbits, on the leaf class itself, and with
two redundant slots matched by a two-variable pattern (8, 9, 10, 11, 32, 33);
composed union chains (12); Def. 6 `≡` for repeated pattern variables, positive
and negative, and at three depths (15, 16, 17); nested path composition (18);
lambda α-equivalence, nested binders, capture avoidance, rewriting under a
binder, a rule whose pattern *is* a binder, and eta (19–23).

---

## Coverage caveat (mutation testing)

Eight single-rule mutations of `preamble-compiled.egg`; four are caught, four are
not:

| mutation | caught by |
| --- | --- |
| child-update drops the composed rename | 3, 5, 6, 7, 8, 10, 15, 16, 17, 20, 21, 22, 32 |
| single-parent unions with the wrong rename (`m2` for `m1⁻¹∘m2`) | 4, 5, 6, 7, 9, 11, 12, 13, 15–20 |
| `let`'s `Union` throws the renaming away | 4, 32 |
| lambda α-rule deleted | 19, 20, 21, 22 |
| **symmetry-finder without the child `G` joins** | *nothing* |
| **self-symmetry shrinking rule deleted** | *nothing* |
| α-finder without the child `G` joins | *nothing* |
| migration rule deleted | *nothing* |

The first two survivors **are** load-bearing — deleting either breaks the
hand-written cases in `tests/slotted-egraph-encoding-11.egg` (case 11 and case 13
respectively). They are only observable through `RenamesToLeader` directly, which
the user surface cannot express, so those machinery-level tests need to stay
alongside this corpus. Whether the last two are genuinely redundant is open: the
hand-written cases do not catch them either.

---

## Running

```bash
cd slotted-experiments && ./run.sh                 # whole corpus
cat preamble-compiled.egg > /tmp/o.egg && ./transform.py tests/10.egg >> /tmp/o.egg \
  && cargo r --bin egglog /tmp/o.egg               # one test
```

Cross-check: clone `slotted-egraphs`, drop `xcheck-slotted-egraphs.rs` in as
`tests/xcheck.rs`, `cargo test --test xcheck`.

One change outside the tests: `transform.py` gained a 13-line `strip_comments`
called from `parse` — the parser choked on `;`, so a commented corpus was
impossible.
