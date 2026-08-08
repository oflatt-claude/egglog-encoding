# Port the egglog Redex semantics to Lean 4

## Context

egglog's proof encoding (`egglog/src/proofs/`, designed in
`egglog/src/proofs/proof_encoding.md`) replaces built-in congruence and rebuilding
with an explicit per-sort union-find and per-constructor view tables maintained by
ordinary rules, so that *every equality has a rule firing behind it*. We want to
prove things about that encoding — that it simulates the ideal semantics, and that
the proof terms it stores really witness the equalities they claim.

To state any such theorem we first need the ideal semantics written down formally.
That exists already as a Redex model — [egglog PR #324](https://github.com/egraphs-good/egglog/pull/324)
(`semantics/semantics.rkt`, `semantics.scrbl`, `test.rkt`; closed, branch
`oflatt-ideal-semantics`, head `e46aef4`). This document plans its port to Lean 4.

Two things shape the design beyond a literal transcription:

- **The encoding's *target* language needs `:merge` functions.** `@UF_<Sort>` and
  `@<C>View` are both merge functions, and the view's `:merge` *is* congruence
  resolution. So the `:merge` extension is not a later nicety — it is a
  prerequisite for the eventual theorem. Phase 1 must be structured so adding it
  is additive.
- **Proof terms are derivations.** Reasoning about `@Trans`/`@Sym`/`@Congr` nodes
  means inducting on how an equality was derived, so congruence must be an
  inductive relation, not a computed fixpoint.

## Decisions

- Project lives at `semantics/` in the workspace root, alongside `egglog/` and
  `egglog-experimental/`, keeping those subtrees clean per `AGENTS.md`.
- Mathlib (`Set`, indexed unions, `Relation.*`, and later lattices for merge
  functions), pinned to `v4.32.2` on Lean `v4.32.2` in `lakefile.toml` and
  `lake-manifest.json`; binaries come from `lake exe cache get`.
- Congruence as an inductive relation; the database stores only *asserted*
  equalities.
- Validation by Lean proofs of the ported test cases; an executable interpreter
  with a decidable congruence procedure is a later milestone (M10).

## Current priority

**The goal is to model egglog as cleanly as possible for a paper, and then prove things
about an implementation.** That is a different goal from wanting a sound and fast verified
engine, and it changes what counts as progress: `Spec/` being readable *as a description of
what egglog means* is the deliverable, not a convenience. It is ~2000 lines with zero
theorems and should stay that way.

(The contrast is worth keeping in mind. `lambdaclass/truth_research` — OptiSat — is a Lean 4
verified equality-saturation engine, ~370 theorems and no `sorry`, whose "specification" is a
five-line `Prop` plus 12k lines of Lean with the load-bearing definitions living inside the
proof files. There is no artifact you can read to learn what the system means. It also has
no differential testing, and a no-op engine satisfies its entire soundness chain.)

**The immediate work is a faithful executable model of egglog, validated against the real
implementation by `make lean-difftest`.** Differential testing comes before proof work: a
proof relates `Impl/` to *our* `Spec/`, and difftest is the only check that can tell us
`Spec/` itself is wrong about egglog — which it has been (see `MERGE.md`, "The merge phase
runs between commands").

**The proof encoding (M11) is parked.** `Encoding/Proofs.lean`, `Encoding/Rebuilt.lean` and
`CHECKER.md` record what has been learned about it; they are not a work queue. Do not start
M11 work or try to prove anything in `Encoding/Proofs.lean`. The encoding is downstream of a
model we trust, and we do not have one yet — though the three things this note used to name,
arity checking, reading a `:merge` function in a query, and the rule-head restriction, are
now done. `Spec/Scope.lean`'s "Arity" and "Reading in an action" sections mirror egglog's
typechecker and `writeCase` enforces both; the read path has curated and generated cases and
agrees with egglog on all of them. What is still missing is the six known-false statements
in `Proofs/Merge.lean`.

This document mentions the encoding often because much of what we know about egglog came
from reading `egglog/src/proofs/`. Those are findings about egglog, which is what we are
modelling.

### The two contracts

`Spec/` is append-only: nothing is ever removed from `terms`, `rows` or `eqs`, and a merge
adds the combined row *beside* the two it merged. `Impl/` has **two** interpreters with
**different** contracts, and confusing them wastes time:

| | merge phase? | contract |
| --- | --- | --- |
| `exec` (`Impl/Interp.lean`) | none | **equality** — `exec_toDatabase` |
| `execM` (`Impl/Merge.lean`) | yes, and it **deletes** the rows it merged | **containment** — `execM_contained` |

`execM` is not a state the specification can reach, hence containment. Containment is
satisfied by a do-nothing implementation, and that is *fine for soundness* — the safety
property is "everything written is valid", so writing nothing is vacuously valid. What rules
out a degenerate implementation is difftest, not a theorem. `execM_current_of_lattice` was
meant to add machine-checked completeness for merges that are joins, but it is **false as
stated** — `Proofs/Lattice.lean` refutes it three ways. A corrected statement is worth
having; see its docstring for what it has to carry, and note it may still be false for
programs with rules.

### The consolidation arc

M9 introduced a shadow of each M0–M8 notion, and they have been collapsed one at a time.
Three pairs, in the order they are being retired:

| M0–M8 | M9 shadow | status |
| --- | --- | --- |
| `Database`, `Action`, `Cmd`, `Rule` | `MDatabase`, `RowAction`, `MCmd`, `MRule` | **done** — one of each |
| `Cong` | `MCong` | open — `mcong_iff_cong` licenses the collapse |
| `Expr.eval`, `evalAction`, `stepCmd` | `MEval`, `ActionStep`, `CmdStep` | open — M12, and now *partial* |

The pattern is worth naming because the answer has been different each time. The state
types merged outright. `Cong`/`MCong` cannot merge without pushing `CtorRows` hypotheses
into `exec_toDatabase`, and the split happens to line up with the two sides of a simulation
theorem, so it is structure rather than duplication. And `eval`/`MEval` can now merge —
because reads became query atoms — but only up to the action level: `MergeStep` chooses
which rows collide and `MergeClosure` how many steps, so the step relations stay relations.
See M12.

One live inconsistency this leaves, and it is the argument for finishing M12: the
`CmdStep.action` merge-phase fix landed in the *relational* `CmdStep` but not in the
*functional* `stepCmd`, which still does `.action a => evalAction db a` with no merging. They
are meant to be the same semantics and now disagree off the constructor fragment, where
merging is the identity — which is exactly why nothing broke.

### Which primitives, and why

`Prim` exists for one reason: so a `:merge` body can **compute**. Without it a body can only
select (`old`, `new`) or build a term, so there are no lattice merges and no analyses.

- **`min`/`max`** are what make `:merge` mean anything — every differential merge case uses
  them, `execM_current_of_lattice` is about them, and without them `:merge (min old new)`
  silently built the *term* `min(5, 3)`.
- **`ordering-min`/`ordering-max`** serve the real encoding's union-find leader selection and
  nothing else. **M11-min drops the union-find**, so nothing in the live plan needs them;
  their only remaining uses are inside `Encoding/Rebuilt.lean`, which is parked M11 material.
  Retire the two together when M11-min lands.
  - They also carry the model's one **accepted deviation** on merge results: `Term.blt` is a
    deterministic structural order, egglog's is the allocation order of value ids, so the two
    keep different representatives. It is observable — `(function D (Math) i64 :merge
    (ordering-min old new))` with `(set (D (A)) -1)` then `(set (D (A)) 1)` settles on `1` in
    egglog and `-1` here — and it is a hypothesis of any simulation theorem, not a bug to fix.
    `MERGE.md`, "The representative deviation", has both repros and the mechanism. Retiring the
    two primitives is what retires the deviation.

Dropping all four would collapse `MEval` to `Expr.eval` outright, which is the smallest the
semantics can be — at the price of `:merge` becoming decorative, with no lattice for the
completeness half to be complete about.

### Checking a change

Three theorems are load-bearing enough to check every time, with `lean_verify` (lean-lsp
MCP) or `#print axioms` rather than by grepping for `sorry` — it asks the kernel what a
theorem actually depends on and traces into Mathlib:

| theorem | expected axioms |
| --- | --- |
| `mcong_iff_cong` | `propext` **alone** |
| `exec_toDatabase`, `mem_closure_iff`, `execM_contained` | `propext, Classical.choice, Quot.sound` |

Statements known to be **false** carry compiling counterexamples in
`Proofs/Counterexamples.lean`, and `Encoding/Rebuilt.lean` holds the `Rebuilt` vacuity result.
Both are `sorry`-free and in the build, so they cannot rot — read them before trying to
prove anything they refute.

Two traps that a green build will not catch. Writing `h.ge` for a set inclusion silently
pulls `Classical.choice` into every downstream axiom set. And `lake build` does not rebuild
the difftest executable — `lake build difftest` does, which `scripts/difftest.sh` handles but
a manual run may not.

## What the Redex model contains

| Redex | Role |
| --- | --- |
| `Egglog` grammar | `Program`/`Cmd`/`Rule`/`Query`/`Pattern`/`Action`/`expr` |
| `Database = (Terms Congr Env Rules)` | global state: ground terms, equality pairs, bindings, rules |
| `Eval-Expr`, `Eval-Action`, `Eval-Global/Local-Actions`, `Eval-Actions` | actions add terms and equalities |
| `Congruence-Reduction` + `restore-congruence` | refl/symm/trans/congr + "presence of children", to a fixpoint |
| `valid-env`, `valid-subst`, `valid-query-subst` | declarative e-matching ("pattern instance is equal to a witness term already present") |
| `valid-subst-faster` | operational e-matching, unused by the main relation |
| `Command-Reduction`, `Egglog-Reduction` | run one command; run a program, restoring congruence between commands |
| `typed-*` judgments | scope checking only (a single type `no-type`) |
| `test.rkt` | ~25 unit checks plus `redex-check` random testing |

## Target design

Package `EgglogSemantics`. The tree separates *what is being claimed* from *why it
holds*, so the first can be read closely and the second skimmed — `Spec/` and `Impl/`
contain **no theorems at all**.

```
Spec/     Syntax  Term  Database  Congruence  Merge  Eval  Match  Step  Scope   (+ Encode, parked)
Impl/     Closure  Interp  Merge
Proofs/   one file per Spec/ or Impl/ subject, plus:
            Counterexamples   compiling witnesses that a statement is false
            Rebuilt           the Rebuilt vacuity result (M11, parked)
Tests/    Examples  the Redex checks, as proofs and as #guards
          Egg       renders a Program as egglog source, for differential testing
```

The one exception to "definitions only" is a proof the language requires to *make* a
definition — the `decreasing_by` on `closure`, and decidability instances. Those are
inlined rather than named, so nothing in `Spec/` or `Impl/` is there for a proof's sake.

### Syntax

`Expr` and `Term` are nested inductives over `List`. `Term` gets a hand-written
induction principle (`∀ f args, (∀ a ∈ args, P a) → P (.app f args)`) written once
and used everywhere; recursive definitions use the mutual `Term`/`List Term`
pattern, which is the reliable way to get structural recursion through the
nesting. `Lit` is `Int` for now, deliberately a separate type so base sorts can be
added when merge functions arrive.

A `Cmd.decl` case and a `Signature` (`FnName → Option FnDecl`, `FnDecl` carrying
arity and a `MergeSpec` of `.union | .merge Expr | .noMerge`) go in **from day
one**, with Phase 1 theorems carrying an `AllConstructors sig` hypothesis. This is
what keeps the `:merge` extension from churning the AST.

### Database and congruence

```lean
structure Database where
  sig   : Signature
  terms : Set Term
  rows  : Set Row                -- one entry per value column; added in M9
  eqs   : Set (Term × Term)      -- asserted only
  env   : List (Var × Term)      -- order matters: first binding wins
  rules : Set Rule
```

`Cong db : Term → Term → Prop` is the inductive closure with `assert` / `refl`
(restricted to `t ∈ db.terms`, faithful to the Redex, where reflexivity only fires
for terms actually present) / `symm` / `trans` / `congr`. The `congr` rule is
written as a mutual inductive with a `CongList` companion rather than an
`∀ i, i < length` premise — same relation, workable induction — with a
`List.Forall₂ (Cong db)` bridge lemma.

`restore-congruence` **disappears entirely**, which is the main simplification:

- refl/symm/trans/congr become `Cong`'s constructors.
- "presence of children" becomes a structural invariant: `Database.addTerm`
  inserts a term together with all its subterms, and `Database.WF` asserts
  subterm-closedness plus that every asserted equality's endpoints and every
  binding's value are in `terms`.

This is observationally equivalent because `Eval-Action` never reads `Congr`, so
deferring subterm insertion to a later rebuild is unobservable — recorded in the
source as a documented deviation with that justification.

### Where "restored congruence" went

There is deliberately **no post-restore database state**, and no "the reduction
can no longer step" predicate. The Redex has two kinds of database — one whose
`Congr` holds just the asserted pairs, and one whose `Congr` is closed — and
`restore-congruence` moves between them. Here the database always holds only
asserted equalities, and closure is a predicate rather than a state. Its two
halves are handled differently:

- The **relation** half (refl/symm/trans/congr) is never materialized. The only
  place the Redex reads the closed `Congr` is the `valid-subst` side conditions;
  those become `Cong (db.addTerm t) w t` directly. `Eval-Action`,
  `Command-Reduction` and `Egglog-Reduction` never consult `Congr` at all, so
  nothing else needs it.
- The **term-set** half ("presence of children") is a real state change, and is
  the one part that stays in the state — as the `addTerm`/`WF.subtermClosed`
  invariant above.

The observable meaning of a finished program is therefore the pair
`(db.terms, Cong db)`, not a database with a big closed equality set.

If an explicit closed representation is wanted — to check faithfulness against the
Redex, or for the executable layer in M10 — the right way round is to *define* it
as a comprehension over the relation and *derive* the fixpoint property:

```lean
noncomputable def restore (db : Database) : Database :=
  { db with eqs := {p | Cong db p.1 p.2} }

theorem cong_restore   : Cong (restore db) a b ↔ Cong db a b   -- idempotent
theorem restore_normal : ∀ db', CongStep (restore db) db' → db' = restore db
```

so "no congruence step applies" is a theorem about `restore`, not the definition of
it. Defining the closure this way is far cheaper than defining it as a fixpoint and
then proving it *is* the closure.

The e-graph as a *data structure* — a set of e-classes rather than a relation — is
then `Quotient` of `db.terms` by `Cong db` (an equivalence on `db.terms` by the M2
lemmas). That quotient is the bridge to M11: an e-class on this side corresponds to
an `@UF` leader on the encoded side.

### E-matching

Ported structurally from `valid-subst`, keeping the witness formulation: a
substitution is valid when the pattern instance is `Cong`-equal, *in the database
extended with that instance*, to some witness term already in the database. The
witness is what forbids matching a term the e-graph does not contain.

Three deviations and facts worth recording:

* `ValidEnv` requires the substitution's domain to be a *permutation* of the
  pattern's free variables, where the Redex pins it to the order `varset-union`
  happens to produce. The extra substitutions this admits are permutations of Redex
  ones, which no `lookup` can distinguish; making that precise is the
  environment-agreement lemma in M8.

Two facts the Redex leaves implicit and Lean needs as lemmas:

- `free-vars pat db.env` excludes globally-bound variables, so `σ`'s domain is
  disjoint from `db.env`'s and `Env-Union db.env σ` never fails — plain append is
  correct. (This also preserves the real quirk that a globally-bound variable in a
  pattern denotes its value rather than being a match variable.)
- Envs only ever get consulted through `lookup`, so `evalLocalActions` is
  invariant under extensional agreement of environments. That lemma, rather than a
  list-level normal form, is what lets `Env-Union`'s duplicate bindings be ignored.

### Steps

Because the database's components are `Set`s, an indexed union over *all* matching
substitutions is directly expressible, so `(run)` is a function rather than a
nondeterministic relation, and the whole semantics becomes
`noncomputable def runProgram : Program → Database → Option Database`:

```lean
noncomputable def runRules (db : Database) : Database :=
  db.sUnion { d | ∃ r ∈ db.rules, ∃ σ, ValidQuerySubst db r.query σ ∧
                    evalLocalActions r.actions db σ = some d }
```

`sUnion` is left-biased on `env` and `rules`; `ruleResults_env` and
`ruleResults_rules` show every `d` in that set has `d.env = db.env` and
`d.rules = db.rules`, which is what makes the bias faithful to Redex `U_d`. The
Redex's `skip` command is an artifact of its two-level reduction relation and is
dropped. `Option` carries the partiality of variable lookup; `Scope.lean` proves
well-scoped programs never hit `none`.

`Cmd.decl` updates `db.sig` and nothing reads it yet, so declarations are inert in
this phase — the point is that M9 turns them on without touching the AST or any
`match` over `Cmd`.

## Milestones

The port proper — **all of M0–M7 is done**, `lake build` is clean and `sorry`-free.

| | file | notable |
| --- | --- | --- |
| M0 | scaffold | Mathlib `v4.32.2` on Lean `v4.32.2`; `make lean-check` kept out of `make check` |
| M1 | `Syntax`, `Term` | `Term.recTerm`, the induction principle through the `List Term` nesting |
| M2 | `Database`, `Congruence` | `Cong.le`, the least-congruence principle |
| M3 | `Eval` | `Expr.eval_agree` — evaluation reads the env only through `lookup` |
| M4 | `Match` | `ValidSubst`, `Env.UnionAll` |
| M5 | `Step` | `runRules`, `stepCmd`, `runProgram` |
| M6 | `Scope` | `run_isSome` — a well-scoped program runs to completion |
| M7 | `Examples` | the `test.rkt` checks as closed proofs |

Two of those carry more weight than their size suggests. **`Cong.le`** is how every *negative*
fact about the closure is proved — "this pair is not derivable" means exhibiting a congruence
that omits it — and it is the shape the M11 checker-soundness argument would take. A design
without it cannot state a negative fact at all. **`evalLocalActions_isSome_of_scoped`** says a
well-scoped rule contributes on every substitution its query admits; `runRules` silently drops
stuck firings, so that is the statement worth having rather than mere totality.

Follow-ups, in rough dependency order:

- **M8 — metatheory.** Partly done.
  - ✅ *Environment agreement.* `Env.Agree.of_perm` and `.append_left`,
    `Database.EnvAgree`, and `evalAction`/`evalActions`/`evalLocalActions_agree`.
    This is `Expr.eval_agree` lifted to whole action sequences, and it discharges
    both places the semantics is deliberately loose about environments: the Redex
    `Env-Union` leaving a variable bound twice, and `ValidEnv` fixing a domain only up
    to permutation. `ruleResults_of_agree` is the payoff — `runRules` sees a
    substitution only up to agreement, so an enumerator may emit one representative
    per class.
  - ✅ *Rounds.* `runRounds` (egglog's `(run n)`; `Cmd.run` is one round),
    `runRounds_succ'`, `Saturated`, and the `Contained`/`WF`/env/rules lemmas.
  - ~~`ValidSubst` inversion, without which no example can state what a `run` does *not*
    produce~~ — **superseded by M10.** `exec_toDatabase` makes any statement about a
    *specific* program's result decidable: it transfers to the interpreter, where the
    closure computes. The `#guard` showing one round is not enough for the `Wrapper`
    example is already such a negative fact. Inversion is still wanted for statements
    quantified over *all* programs, which is where M11 will need it.
  - Remaining: nothing on the critical path. The matcher is the slow one by
    construction — `assignments` is `|terms| ^ |vars|` and `patternHolds` recomputes a
    closure per candidate — which is what keeps the differential cases tiny. The fix is
    **not** to port the Redex's `valid-subst-faster`: `exec_toDatabase` is the contract,
    so the reference implementation can be optimized wherever profiling says it is slow
    and the refinement re-established against the unchanged spec. Porting
    `valid-subst-faster` specifically would settle a conjecture the Redex left open,
    which is a nice-to-have rather than a need.
- **M9 — `:merge` functions.** Designed in [`MERGE.md`](MERGE.md). Partly done, and
  **merged into the main development** — there is one `Database`, one `Action`, one
  `Cmd`, and `Spec/Merge.lean` holds only what is genuinely new.
  - ✅ *The compatibility theorem.* `mcong_iff_cong`: where the rows are the constructor
    rows and every function is a constructor, the functional dependency `MCong.fd` **is**
    `Cong` — so `MCong` needs no `congr` constructor and every M2–M8 theorem transports
    rather than being reproved. `Cong.toMCong'` generalizes it to `CtorTerms`/`RowsComplete`,
    which unlike `CtorRows` survive a `:merge` declaration.
  - ✅ *The shape change.* A `:merge` body is an action list, so `MergeStep` is a relation
    on databases and `runProgram` is a relation too. `Spec/Merge.lean` holds `MCong`,
    `MergeStep`, `Expr.MEval`, `RunStep`, `Prim`/`Term.blt`. Evaluation was *also* a
    relation for a while, because a non-constructor application in an action was a lookup;
    that is now forbidden — see "Reading is a query atom" below — and `Expr.MEval` is back
    to being deterministic (`Expr.MEval_unique`, unconditional).
  - ✅ *Multi-column outputs.* `Action.set` takes a `List Expr`, and `Pattern` gained
    `values` — egglog's lowered row atom `f(a…, v…)`, written `(= v (f a…))` at one value
    column and `(= (values v…) (f a…))` at more. It is the only read in the language.
  - ✅ *The implementation deletes; the specification does not.* `Spec/` stays append-only
    while `Impl/Merge.lean`'s merge phase drops the two rows it combined, as egglog does,
    and nothing else — `mergeRound_confined` proves the "nothing else": no term, no
    equality, no `.union` row, no `.noMerge` row. So the contract splits into containment
    (`execM_contained`, proved), the untouched equality on the constructor fragment where
    the pass is the identity (`mergeRound_eq_self`), and `Current` for lattice merges.
  - ✅ *The refinement chain.* 17 of 17 proved. **Nine were false as written** — three in
    ways their M10 counterparts in `Proofs/Interp.lean` had already solved, so read the M10
    counterpart before stating an M9 lemma. Six statements remain `sorry` in
    `Proofs/Merge.lean`, all known-false, with compiling witnesses in
    `Proofs/Counterexamples.lean`.
  - Remaining: `Cong` and `MCong` still coexist over the one `Database` — that is M12.
- **M10 — executable layer.** A `Finset`-based interpreter, a decidable congruence
  closure, and a refinement theorem `↑(exec p d) = spec p (↑d)`.
  Proved end to end. Five design notes are worth more than the lemma inventory, which is
  in the code:

  - **The closure is deliberately the obvious algorithm.** `congStep` is one round of
    one-step-derivable pairs over `terms ×ˢ terms`; `closure` iterates by well-founded
    recursion on how much of that universe is missing, and `mem_closure_iff` shows it
    decides `Cong` exactly (completeness by `Cong.le` against the fixpoint). Union-find
    with upward merging is what egglog does and what the M11 theorems are *about* — using
    it here would put the thing under study inside the thing doing the studying. Stopping
    only at a fixpoint is what makes `Cong.le` applicable, hence well-founded rather than
    fuel-bounded.
  - **`FDatabase` uses `List`, not `Finset`**, because `Finset.toList` is noncomputable and
    the interpreter must enumerate. Duplicates are harmless: the denotation is the set of
    members.
  - **The enumerator departs from the spec on purpose.** The spec takes one substitution per
    pattern and joins them (`Env.UnionAll`, faithful to the Redex); the enumerator assigns
    the whole query's free variables at once and restricts per pattern with `Env.canon`.
    `Env.agree_canon` shows they agree up to `Env.Agree`, which is all `runRules` can see.
    Both directions are proved (`validQuerySubst_of_mem_matchQuery` and its converse).
  - **`Env.UnionAll.refines_of_mem` had to carry self-refinement, not `Nodup`.** Appending
    two substitutions sharing a variable duplicates it in the domain while leaving every
    lookup intact, so `Nodup` is not preserved by a `Union2` step and
    `∀ b ∈ ρ, lookup b.1 ρ = some b.2` is.
  - **Fold lemmas need a closed step term.** `execRunRules` was refactored into named
    `fireInto`/`fireRule` steps so `mem_terms_foldl` and friends can be instantiated at
    them; inline lambdas leave the lemma's step as an uninferable metavariable.

  Well-founded definitions are sealed against kernel reduction, so `decide` cannot see
  through `closure`. Use `#guard` (a command, so it enters no proof term) or `unseal
  closure`. **Not** `native_decide` — it adds `Lean.ofReduceBool` to every downstream axiom
  set. The interpreter reproduces the Redex `execute` cases as `#guard`s in `Examples.lean`,
  including the two-round `Wrapper` test, which has no hand proof because stating it needs
  `ValidSubst` inversion.

  The chain ends at

  ```lean
  theorem exec_toDatabase {p : Program} :
      (exec p).map FDatabase.toDatabase = run p
  ```

  Well-formedness came free: `FDatabase.WF` is the spec's, so `execCmd_wf` is `stepCmd_wf`
  read through the refinement rather than a separate induction.

**M10 is done**, and that is what makes the `#guard`s in `Examples.lean` and the 122
differential cases constrain the *specification* rather than only the interpreter. Before
it they sat on the interpreter's side of an unproved gap.

  Two obligations writing the implementation forces:
  1. *Enumeration completeness* — the spec's `{σ | ValidQuerySubst db q σ}` against an
     enumeration of `freeVars → terms`. Prepared by `ValidEnv.mem_dom_iff` (the domain
     is precisely the free variables) and `mem_terms`.
  2. *Order-insensitivity* — ✅ discharged by M8's agreement lemma.

  *Finiteness* is **not** an obligation: the implementation is a `Finset` function by
  construction, so finiteness of the spec's output falls out of the refinement theorem
  as a corollary rather than needing to be proved first.

### Differential testing — ✅ running

`make lean-difftest` (`scripts/difftest.sh`) compares the Lean interpreter against the Rust
binary. **122 cases pass**: 60 random constructor (38 distinct profiles), 30 random `:merge`
(24 profiles), 32 curated.

The oracle is **`(print-size)`**, one row count per function — the same quantity
`egglog/tests/files.rs` snapshots. egglog's table for `f` holds one row per distinct
*canonical* argument tuple, so the Lean-side quantity is the number of congruence classes of
`f`-applications. `DiffTest.lean` writes a `.egg` file and the predicted counts; the script
runs egglog and diffs, one invocation per case with a timeout.

**No egglog test file is portable.** Of the 104 in `egglog/tests`, zero are in the fragment:
`function` appears in 47, `relation` 35, `constructor` 35, `sort` 32, `set` 31,
`run-schedule` 21. `before-proofs.egg` is closest and needs only a `Lit.str` constructor and
`(rewrite lhs rhs)` desugaring.

**This is the only check that the model matches egglog rather than matching itself** — and it
has caught things no proof would. The specification, not the implementation, was wrong about
merging between commands (`MERGE.md`).

Three generator lessons, each learned from a green suite that was not testing what it looked
like:

* A freely generated pattern almost never matches, so 31 of 60 cases gave an identical
  trivial profile. Patterns are now built by *abstracting subterms of a term the program
  actually builds*, which guarantees the rule fires.
* `pick` read an LCG's low bits, which have period 4 — all 30 merge cases emitted an
  identical program.
* Hence the script prints the **row-count distribution** every run. A pass count alone hides
  a generator that has stopped exercising anything; treat a narrowing distribution as a
  regression even if the count rises.

Two findings that the fragment is **not a subset** of egglog's language: a bare variable was
a legal query fact and `expr` action here and egglog's grammar rejects both (34 of the first
60 cases died on it — now banned via `Expr.IsApp`, the one place `WellScoped` is deliberately
stricter than the Redex); and `Database.rules` is a `Set`, so a repeated rule is silently
ignored where egglog panics.

**Every case is checked for legality before it is written.** `writeCase` refuses to emit a
program egglog would reject — an illegal `set`, a use whose column counts disagree with the
declaration (`Spec/Scope.lean`'s arity check), or a name used at two arities, which the
emitted `datatype` header cannot express. A rejected program is a *missing* case, not a
failing one, so the check aborts rather than skips.

What it does not cover: anything outside the fragment, and value columns, since
`(print-size)` counts key classes and is blind to them.

A performance note that is really a design note: `FDatabase` insertions deduplicate, because
a round's `union` copies every operand's terms and without dedup the per-substitution
`List.toFinset` inside `closureF` goes quadratic. Invisible to `toDatabase`.

- **M11 — the proof encoding.** See below.

- **M12 — one evaluator.** `Expr.eval`/`evalAction`/`stepCmd`/`runProgram` (functions,
  M0–M8) and `Expr.MEval`/`ActionStep`/`CmdStep`/`ProgramStep` (relations, M9) both run
  over the one `Database` and the one `Action`. Collapsing them is the last of the
  unification and is **deliberately deferred**. The direction it goes in has changed, and
  the change is the whole reason "Reading is a query atom" was worth doing.

  - *Determinism came back.* `Expr.MEval_unique` now holds with **no hypotheses** — no
    `AllConstructors`, no `NoPrim` — because the only rule that read the database was
    `lookup` and reading is a query atom. `Database.ActionStep_unique` and
    `ActionsStep_unique` follow: every premise of every action case is an evaluation.
  - *What must stay a relation.* Everything above an action, and for a reason that has
    nothing to do with evaluation: `MergeStep` chooses **which** pair of rows collides and
    in which order, and `MergeClosure` chooses how many steps to take. So `RunStep`,
    `CmdStep` and `ProgramStep` are relations by design and stay that way. The unification
    is therefore *partial* — one evaluator and one action evaluator, two step relations.
  - *The cost, restated.* The old estimate of 1000–1400 lines assumed converting the
    functional side (`Proofs/{Eval,Match,Step,Scope,Interp}`) to relations. It now goes
    the other way: make `ActionStep`/`ActionsStep` functions and the `Option` algebra those
    files are built on is what survives. What is touched is `Proofs/Merge.lean`'s action
    lemmas — `ActionStep.contained`/`.envAgree`/`.mono`/`.wf`,
    `execAction_ActionStep`, `execActions_ActionsStep` and their callers, ~60 references —
    and `Expr.eval` gaining a `Signature` argument so that one evaluator serves both, which
    is what puts a hypothesis on `Proofs/Scope.lean` and `exec_toDatabase`.
  - *The recovery, unchanged in shape.* `exec_toDatabase` is an **equality** on the
    constructor fragment, and that is what makes the differential cases bear on the
    specification rather than only on the interpreter. It survives the collapse for the
    same reason it holds now: on that fragment there is no `.merge` function, so no
    `MergeStep`, so `ProgramStep` is deterministic there.

## Extending with `:merge` (M9)

The design is [`MERGE.md`](MERGE.md). What this plan originally proposed is kept only for
the record of where it was wrong, since two of the mistakes were instructive:

- **A merge body is an action list, not an expression.** So the observable value of a key
  class cannot be a fold over asserted rows, and there is no `SemilatticeSup` to lean on.
  Evaluation and `runProgram` became *relations* instead.
- **A non-constructor application is a lookup**, with no `:default` to fall back on.

What did stand: the signature was already in the AST from M1, so only `MergeSpec`'s other
cases became reachable; rows replaced the bare term set with congruence *as* the functional
dependency; and merge closure carries no termination claim. Base sorts (`i64`, `String`, a
real sort discipline replacing the Redex's `no-type`) are still deferred — see "arity
checking" in the current priority.

## Reading is a query atom

**All reading happens in the query; all writing happens in the actions.** An application of
a non-constructor is a *lookup* — it reads a recorded row rather than building a term — and
`Spec/Scope.lean`'s `Program.noLookup` says a program contains none, anywhere. The one place
a program reads is the query atom `Pattern.values`, which is egglog's lowered
`f(a…, v…)` and now covers every width: `(= v (f a…))` at one value column,
`(= (values v…) (f a…))` at more.

**What it buys.** `Expr.MEval` loses its `lookup` constructor. It is then deterministic
unconditionally (`Expr.MEval_unique`), reads the database only through its signature
(`Expr.MEval.ofSig`), and `Impl/Merge.lean`'s `execExpr` computes it instead of choosing
among its answers. `Database.ActionStep`/`ActionsStep` are deterministic too, which is what
reopens M12. The one remaining place the model over-approximates egglog's reads is the
query atom itself, which matches *any* recorded row where egglog matches the current one.

**Where it is stricter than egglog, checked against the binary.** egglog runs
`check_no_function_lookups_in_actions` (`src/typechecking.rs:1325`) on a **rule head** only,
and only for a seminaive rule. Three other positions read there and are rejected here:

| position | egglog | repro |
| --- | --- | --- |
| top-level action | accepted, copies the value | `(set (Copy (A)) (Dist (A)))` |
| `:merge` body | accepted; missing row is `Lookup on Zero failed in the merge function for Dist` | `(function Dist (Math) i64 :merge (max old (Zero)))` |
| nested in a query fact | accepted, flattened to two atoms | `(F (Dist k))` |

The first two are `Context::Full` and `Context::Write`, neither of which runs the check; the
third is egglog's query flattening, which this model does not have. Each has a flat
equivalent — `(rule ((= v (Dist k))) ((set (Copy k) v)))` for the first — so the loss is
notation, not expressiveness, except in the `:merge` body, where a body that reads another
table genuinely cannot be written.

**What it exposed in `Encoding/Encode.lean`.** `encodeBuild` interns an application by `set`ting
the view and then *reading it back* with `(let x (@fView c…))` — a lookup in a rule head,
which egglog refuses. egglog does the same job with `set-if-empty-<View>!`, registered as a
**primitive** (`src/proofs/proof_fresh.rs`), and `expr_has_function_lookup` flags only
`ResolvedCall::Func`. So `encode` emits rule heads the real system rejects, and the fix is
the one egglog made: a `Prim`-style get-or-insert, which is a write. Recorded in
`Encoding/Encode.lean`, not done — it is M11 work.

## The minimal proof encoding (M11-min)

The target. Everything below is *design*, not built yet.

**Proved against the specification, not against the Rust.** That is the decision that makes
this tractable: no differential testing against real egglog, no matching its row counts, no
conversion layer. The claim is about our `encode` and our `Cong`.

### What it drops

Everything the real encoding needs in order to be *fast*:

- **No union-find, no canonical ids, no leader lookups.** Terms are their own ids — the
  "natural" term a rule builds is the id. No `@UF_<Sort>`, no `ordering-min`/`ordering-max`.
- **No view tables and no rebuilding.** Nothing is ever re-keyed.
- **No proof skeletons.** No nested `@Proof` terms, no `get-fresh!`, no `@Ast`.

### What it keeps

The property we actually want: *every equality has a rule firing behind it, and every
recorded proof is valid.*

**Leading option, not yet settled: constructors for terms, view tables for proofs.**

- The source's **constructors carry over**, so a term is its own id — the "natural" term a
  rule builds. No canonicalization, so no leader lookup.
- Per source constructor `C`, a **view table** `@CView : (S…) → (S, Proof)`, a *function*
  whose output carries the proof alongside the id. Its `:merge` is what resolves
  congruence: colliding rows over congruent keys merge their outputs and record why.

Three things this decides:

- **It needs `:merge`.** The view's merge is the congruence resolution, so this does *not*
  live in the `:no-merge` fragment.
- **It uses multi-column outputs.** `(S, Proof)` is two columns — exactly what `Action.set`'s
  `List Expr` output and `Pattern.values` were built for.
- **It stays inside reads-in-query/writes-in-actions.** A merge body has `old*`/`new*` bound
  by the collision, so it writes without reading. Nothing looks anything up on a
  right-hand side, because there are no canonical ids to look up.

### The side condition that makes it work

Since the source constructors carry over, `MCong.fd` still fires on them in the target —
which would mean some equalities have no rule behind them, defeating the point. That
collapses to nothing **provided `encode` emits no `union` actions**: with `eqs` empty,
`MCong` reduces to reflexivity, and `fd` on equal arguments yields nothing new. So "emits no
`union`" is a syntactic property of `encode` that makes the target's built-in congruence
vacuous, and `Encoding/Proofs.lean`'s `encode_mcong_eq` is exactly that lemma.

### What a proof value is

egglog's **user-facing** `Proof` (`src/proofs/proof_format.rs:289`), not `RawProof`:

```rust
struct Proposition { lhs: TermId, rhs: TermId }
struct Proof { proposition: Proposition, justification: Justification }
enum Justification {
  Fiat,                                                     // top-level equalities, and reflexivity
  Rule { name, premise_proofs: Vec<ProofId>, substitution },
  MergeFn { function, old_proof, new_proof },
  Trans(ProofId, ProofId),
  Sym(ProofId),
  Congr { proof, child_index, child_proof },
}
```

It maps onto `Cong` almost one for one, which is why checking is a structural induction with
no conversion layer — the payoff for `Cong` being inductive rather than a computed closure,
and why dropping the skeletons costs nothing (they exist to make proofs *small*, not
checkable).

| `Justification` | `Cong` |
| --- | --- |
| `Fiat` | `assert`, and `refl` for top-level terms |
| `Rule` | a rule firing — `ValidQuerySubst` plus `runRules` |
| `Trans` / `Sym` | `trans` / `symm` |
| `Congr` | `congr`, **but one child at a time** |
| `MergeFn` | `MergeStep` — only once merge functions are involved |

Two mismatches to settle before writing `encode`:

- **`Congr` is incremental, `Cong.congr` is n-ary.** egglog extends `t1 = f(…, ci, …)` to
  `t1 = f(…, c2, …)` one `child_index` at a time; ours takes a whole `CongList`. They are
  inter-derivable — n chained steps make one of ours — but the proof *terms* differ in
  shape, so matching the user-facing type needs a bridging lemma by induction on the child
  list. This is the one place the correspondence is not definitional.
- **Reflexivity is not assumed, and we already agree.** "A proof of `t = t` must correspond
  to some `t` added at the top level." `Cong.refl`'s `a ∈ db.terms`, inherited from the
  Redex, is exactly that discipline.

### The invariant is a precondition of the encoding, not just a style rule

`ProofEncodingUnsupportedReason` (`src/proofs/proof_encoding_helpers.rs:851`) lists
**`FunctionLookupInAction`** — "action contains a function lookup. Finding the output of a
function is only supported in queries" — and **`UnsafeSeminaive`** — "Arbitrary RHS database
reads are not representable by the term/proof encoding." egglog's own encoder *refuses* a
program that reads on a right-hand side. So "reads in the query, writes in the actions" is
not merely egglog's default typechecking rule; it is what the proof encoding requires in
order to exist.

### Three theorems

1. **Soundness.** `@Eq(a, b)` present in `run (encode P)` → `Cong (run P) a b`.
2. **Completeness.** `Cong (run P) a b` → `@Eq(a, b)` present, given enough rounds.
3. **Justification validity.** Every justification row's premises are present, and it maps
   to a `Cong` step. This is "every proof we write, the checker accepts" — and here it is
   close to definitional, which is the point of dropping the skeletons.

### The costs, stated up front

Without canonicalization the encoded database is much larger — transitivity and congruence
generate quadratically many `@Eq` rows and nothing dedups them. That is fine for a semantics,
which is about what is *derivable*, but it means row-count claims are out and there is no
size comparison against real egglog to be had. Since the theorems are against the spec, that
costs nothing we wanted.

What this does *not* establish: that egglog's real encoding is correct. It establishes that
the idea is correct, in a setting where every step is checkable. Recovering the real
encoding means adding canonicalization and skeletons back, one at a time, each as a
refinement of this one.

## Path to the full proof-encoding theorem (M11)

With M9 in place, the encoding becomes a translation between two instances of the
same semantics. **Parked**, and superseded as a near-term target by M11-min above — this is
what the full encoding would eventually need, kept because the shape of the theorems carries
over. [`CHECKER.md`](CHECKER.md) has the scoping and the known defects, including that
`Rebuilt` is reachability-vacuous.

Three theorems, in increasing order of what they buy:

1. **Every proof the encoding writes is accepted by the checker** — for every `@Proof` row
   in `runProgram (encode P)`, `Checks` holds. About the *encoder*, with no reference to the
   source semantics, so it is what would catch a proof row written with the wrong column or
   a `@Congr` at the wrong child position.
2. **The checker is sound** — `Checks p` and `p` concludes `a = b` gives
   `Cong (runProgram P) ⟦a⟧ ⟦b⟧`. With (1), every stored proof witnesses a real equality.
3. **Simulation** — `Cong (runProgram P) a b` iff `a` and `b` share an `@UF` leader in
   `runProgram (encode P)`. `⇐` is (1)+(2) at the union-find; `⇒` is completeness and needs
   the rebuild to have saturated.

`Cong` being inductive is what makes all three tractable: all five justifications the
constructor fragment needs map onto `Cong`'s constructors, so (2) is a structural induction
on the proof and (3)'s `⇒` an induction on the `Cong` derivation. This is the reason the
whole development uses a derivation relation rather than a computed closure.

**Fresh ids are structural.** An earlier draft said to add an id supply to the target; that
was unnecessary. Terms *are* the ids — the id for `f` over canonical children `cs` is the
term `.app f cs`, the skolem encoding of `get-fresh!` — so source terms and target ids share
one type and the simulation theorem needs no correspondence relation. The cost is in row
counts, not equalities: egglog mints per construction *site* and so holds strictly more
`@UF` rows.

**Naive, not seminaive.** This port returns *all* matching substitutions where egglog
returns only new ones. Deliberate: a reference semantics should be simple, and a naive round
fires a superset of a seminaive one, so "every proof row written is valid" covers rows the
real encoder never writes. It bites only claims about row *counts* — and, once merges are
not idempotent joins, the number of firings does change the result, so the two genuinely
diverge there. M9's over-approximation is the same trade for the same reason
([`MERGE.md`](MERGE.md), "The framing").

Other omissions inherited from the Redex to-do list: schedules, extraction, containers.

## Verification

- `cd semantics && lake build` — the whole development typechecks. This is the check that
  must stay green.
- `make lean-difftest` — 122 cases against the real egglog binary. Watch the profile
  distribution, not only the pass count.
- `make lean-check` additionally fails on any `sorry`. It **currently fails by design**:
  19 statements are deliberately unproved (13 parked M11, 6 known-false with witnesses in
  `Proofs/Counterexamples.lean`). Use it to check that a change adds no *new* `sorry`.
- Axioms, on every change: `lean_verify` or `#print axioms` against the table in "Current
  priority". A green build does not catch an axiom leak.
- `Tests/Examples.lean` compiling *is* the M7 suite — each ported Redex check is a closed
  proof or a `#guard`.

## `set` legality is a separate predicate, for now

`Database.CtorRows` is one of the two hypotheses `mcong_iff_cong` takes, so it is the
on-ramp from "a database you can run a program to" to "the functional dependency *is*
congruence". Preserving it needs `set` restricted, and egglog restricts it the same way:
`set` on a constructor is a type error (`egglog/src/constraint.rs`). Constructors are
exactly the `.union`-merge functions, so the condition is `mergeOf f ≠ .union` — note this
admits `:no-merge`, checked against the binary.

That is `Action.SetLegal`/`Program.SetLegal` in `Spec/Scope.lean`, **beside** `Scoped`
rather than inside it, for one reason: `Scoped` relates syntax to a `Scope`, this relates
it to a `Signature`, and threading a signature through the whole `Scoped` family would put
an argument on every lemma in `Proofs/Scope.lean` and a hypothesis on `exec_toDatabase`
that none of them would use. Fold them together when `Program.Scoped` needs the signature
for its own sake — the sort discipline is that reason. Until then carry
`WellScoped p ∧ p.SetLegal sig`.

**`SetLegal` alone is not enough**, and the gap is not about actions. Declaring `f` a
`:merge` function makes the constructor row `f ↦ (f)` *already in the database* collide
with itself, and `MergeStep` then writes whatever the body computes there — a
non-constructor row, with no `set` anywhere. Hence the second, independent condition
`Cmd.CtorDecl`. `Proofs/Step.lean`'s `exists_mergeStep_not_ctorRows` is that counterexample
as a theorem.
