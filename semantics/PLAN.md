# A Lean 4 model of egglog's semantics

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
`oflatt-ideal-semantics`, head `e46aef4`) — and this development began as its port to
Lean 4. That is the only debt worth recording up front; "The Redex model this was ported
from", below, is the one place it is discussed, and nothing in the development itself
refers to it.

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
what egglog means* is the deliverable, not a convenience. `Spec/` is ~1200 lines with zero
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

**The proof encoding (M11) is parked, and its theorems are deleted.** `Encoding/` now holds
`encode` and nothing else. The three theorems and their vacuity witnesses were removed
rather than carried through the `Spec/` simplification: two defects made statements true
without saying anything, and the remaining eleven were never checked for the same, so what
was there was a liability rather than an asset. [`ENCODING.md`](ENCODING.md) is what survives them — the two defects, the
repairs that do and do not work, and the SHA to recover the Lean from. Read it before
restating anything. The encoding is downstream of a model we trust, and we do not have one
yet.

**So the work queue is short.** M0–M10 and M12 are done; M11 is parked. What is open:

| open | where |
| --- | --- |
| five unproved statements, all with a recorded defect *in the statement* | `Proofs/Merge.lean` |
| base sorts, in place of the single untyped `Term` | `MERGE.md`, constraint (5) |
| restating M11 against a reachable saturation condition | `ENCODING.md` |

The three things this note used to name — arity checking, reading a `:merge` function in a
query, and the rule-head restriction — are now done: `Impl/Check.lean`'s "Arity" and
"Reading in an action" sections mirror egglog's typechecker, `writeCase` enforces both, and
the read path has curated and generated cases that agree with egglog on all of them.

This document mentions the encoding often because much of what we know about egglog came
from reading `egglog/src/proofs/`. Those are findings about egglog, which is what we are
modelling.

### The two contracts

`Spec/` is append-only: nothing is ever removed from `terms`, `rows` or `eqs`, and a merge
adds the combined row *beside* the two it merged. `Impl/` has **two** interpreters with
**different** contracts, and confusing them wastes time:

| | merge phase? | contract |
| --- | --- | --- |
| `exec` (`Impl/Interp.lean`) | none | **exact, both directions** — `exec_programStep` |
| `execM` (`Impl/Merge.lean`) | yes, and it **deletes** the rows it merged | **containment** — `execM_contained` |

`execM` is not a state the specification can reach, hence containment. Containment is
satisfied by a do-nothing implementation, and that is *fine for soundness* — the safety
property is "everything written is valid", so writing nothing is vacuously valid. What rules
out a degenerate implementation is difftest, not a theorem. `execM_current_of_lattice` was
meant to add machine-checked completeness for merges that are joins, but it is **false as
stated** — `Proofs/Lattice.lean` refutes it three ways. A corrected statement is worth
having; see its docstring for what it has to carry, and note it may still be false for
programs with rules.

### The consolidation arc — ✅ closed

M9 introduced a shadow of each M0–M8 notion. All four pairs have now collapsed, and the
answer was different each time, which is why the arc is worth keeping:

| M0–M8 | M9 shadow | how it resolved |
| --- | --- | --- |
| `Database`, `Action`, `Cmd`, `Rule` | `MDatabase`, `RowAction`, `MCmd`, `MRule` | merged outright — one of each |
| `Expr.eval`, `evalAction`, `evalActions` | `MEval`, `ActionStep`, `ActionsStep` | the **functional** side won, once reads became query atoms |
| `stepCmd`, `runProgram` | `CmdStep`, `ProgramStep` | the **relational** side won; the functional semantics was deleted |
| `Cong` | `MCong` | `MCong` deleted; `Cong` alone, with `Cong.fd` a theorem |

The two step rows went opposite ways for one reason. Below an action nothing reads the
database — `Expr.eval` wants only a `Signature` — so evaluation is a function
unconditionally. Above an action `MergeStep` chooses *which* rows collide and
`MergeClosure` *how many* steps to take, and neither choice can be made by a function.
So `Spec/` now has one evaluator and one action evaluator, both functions, under step
relations that stay relations by design. `Spec/Step.lean` is gone with the functional
half, and with it the standing inconsistency that `CmdStep.action`'s merge phase had
landed in the relation and not in `stepCmd`.

The `Cong`/`MCong` row was the last, and it was the one previously argued to be blocked:
collapsing them was supposed to push `Database.CtorRows` hypotheses into the refinement
theorem. It did not. `Proofs/Congruence.lean`'s `Cong.fd` derives the functional
dependency from `Cong` alone, under nothing but the shape of a constructor's rows — no
`CtorRows`, no `CtorTerms`, no `RowsComplete` — so what a row set adds to congruence is a
*theorem about* `Cong` rather than a second relation. The collapse is **not**
meaning-preserving: `Cong ⊊ MCong`, and `(set (f) (c)) (set (f) (d))` reaches the gap,
where `MCong.fd` equated `c` and `d` and `Cong` does not. `Action.SetLegal` forbids
exactly that program, which is why `exec_programStep`'s statement and axioms were
unchanged by the deletion and `execM_contained` came out strictly stronger.
`Proofs/Counterexamples.lean`'s `setCtorProgram` is that gap as a compiling witness, and
is what keeps `Cong.fd`'s row-shape hypothesis from looking automatic.

### Which primitives, and why

`Prim` exists for one reason: so a `:merge` body can **compute**. Without it a body can only
select (`old`, `new`) or build a term, so there are no lattice merges and no analyses.

- **`min`/`max`** are what make `:merge` mean anything — every differential merge case uses
  them, `execM_current_of_lattice` is about them, and without them `:merge (min old new)`
  silently built the *term* `min(5, 3)`.
- **`ordering-min`/`ordering-max`** serve the encoding's union-find leader selection and
  nothing else. They are live: `Encoding/Encode.lean`'s `mergeBody` and `mergeResult` —
  the `:merge` shared by `@UF` and every view — are literally `(set (@UF (ordering-max old
  new)) (ordering-min old new))`, so `encode` cannot be stated without them. Only a
  union-find-free encoding would retire them.
  - They also carry the model's one **accepted deviation** on merge results: `Term.blt` is a
    deterministic structural order, egglog's is the allocation order of value ids, so the two
    keep different representatives. It is observable — `(function D (Math) i64 :merge
    (ordering-min old new))` with `(set (D (A)) -1)` then `(set (D (A)) 1)` settles on `1` in
    egglog and `-1` here — and it is a hypothesis of any simulation theorem, not a bug to fix.
    `MERGE.md`, "The representative deviation", has both repros and the mechanism. Retiring the
    two primitives is what retires the deviation.

Dropping all four would take `Prim` out of `Expr.eval` entirely, which is the smallest the
semantics can be — at the price of `:merge` becoming decorative, with no lattice for the
completeness half to be complete about.

### Checking a change

Three theorems are load-bearing enough to check every time, with `lean_verify` (lean-lsp
MCP) or `#print axioms` rather than by grepping for `sorry` — it asks the kernel what a
theorem actually depends on and traces into Mathlib:

| theorem | expected axioms |
| --- | --- |
| `Cong.fd` | `propext` **alone** |
| `exec_programStep`, `mem_closure_iff`, `execM_contained` | `propext, Classical.choice, Quot.sound` |

Statements known to be **false** carry compiling counterexamples in
`Proofs/Counterexamples.lean` and `Proofs/Lattice.lean`. Both are `sorry`-free and in the
build, so they cannot rot — read them before trying to prove anything they refute.

Two traps that a green build will not catch. Writing `h.ge` for a set inclusion silently
pulls `Classical.choice` into every downstream axiom set. And `lake build` does not rebuild
the difftest executable — `lake build difftest` does, which `scripts/difftest.sh` handles but
a manual run may not.

## The Redex model this was ported from

**This section is the whole of the port record.** `Spec/`, `Impl/`, `Proofs/` and
`Tests/` name nothing here: the Lean development is meant to be read on its own, by
someone who has never seen the source model. Anything that only makes sense by contrast
with the source belongs on this page.

| source | role | Lean |
| --- | --- | --- |
| `Egglog` grammar | `Program`/`Cmd`/`Rule`/`Query`/`Pattern`/`Action`/`expr` | `Spec/Syntax.lean` |
| `Database = (Terms Congr Env Rules)` | global state: ground terms, equality pairs, bindings, rules | `Database` |
| `Lookup`, `free-vars`, `Env-Union`, `Env-Union2` | environments | `Env.lookup`, `Expr.freeVars`, `Env.UnionAll`, `Env.Union2` |
| `Eval-Expr`, `Eval-Action`, `Eval-Global/Local-Actions`, `Eval-Actions` | actions add terms and equalities | `Expr.eval`, `evalAction`, `evalActions`, `evalLocalActions`, `RuleResults` |
| `Congruence-Reduction` + `restore-congruence` | refl/symm/trans/congr + "presence of children", to a fixpoint | `Cong`, plus `Database.WF.subtermClosed` |
| `valid-env`, `valid-subst`, `valid-query-subst` | declarative e-matching ("pattern instance is equal to a witness term already present") | `ValidEnv`, `ValidSubst`, `ValidQuerySubst` |
| `valid-subst-faster` | operational e-matching, unused by the main relation | not ported |
| `U_d` | union of databases | `Database.sUnion` |
| `Command-Reduction`, `Egglog-Reduction` | run one command; run a program, restoring congruence between commands | `CmdStep`, `ProgramStep` |
| `typed-*` judgments | scope checking only (a single type `no-type`) | the `Scoped` family, `Spec/Scope.lean` |
| `test.rkt` | ~25 unit checks plus `redex-check` random testing | `Tests/Examples.lean`, `DiffTest.lean` |

### What the port changed, and why

* **`skip` is gone.** It exists only so `Command-Reduction` can signal completion to
  `Egglog-Reduction`. That two-level arrangement is there because `(run)` picks a set of
  substitutions nondeterministically; here the database's components are `Set`s, so the
  union is expressible directly and `RunRules` is a plain function. `CmdStep`/`ProgramStep`
  are still relations, but for an unrelated reason — the merge phase, not the match set.
* **`restore-congruence` is gone.** Congruence is the inductive predicate `Cong` rather
  than a closed set of pairs the state carries — see "Where 'restored congruence' went".
  Its "presence of children" half is the one part that *is* state, and it holds by
  construction because `Database.addTerm` inserts a term with all its subterms.
* **A `Signature` and `Cmd.decl` are new.** The source has no declarations at all and
  treats every applied name as a constructor. Here a name means nothing until it is
  declared, which is egglog's own declare-before-use, and it is what lets `:merge`
  functions be added without reshaping the AST.
* **A bare variable is no longer a fact or an action.** The source admits `expr = var`
  as a query fact, matching any term, and as an action, adding one already present.
  egglog's grammar admits neither — `parse error: expected fact`, `parse error: expected
  action`, `parse error: expected command` — so `Expr.IsApp` bans them. **Stricter than
  the source, not stricter than egglog**: the model matches egglog here and the source
  did not. It was a difftest finding, 34 of the first 60 generated cases.
* **`ValidEnv` is up to permutation.** `valid-env` pins `σ`'s bindings to the order
  `varset-union` happens to produce; `Perm` does not. The extra substitutions this admits
  differ from the pinned ones only by reordering, which no `lookup` can see —
  `Env.Agree.of_perm`, and `evalLocalActions_agree` lifts it to whole rule firings.
* **Appending environments replaces `Env-Union` in the one place it is used.** A
  pattern's free variables exclude the globally-bound ones, so the substitution's domain
  is disjoint from the globals' and the append cannot fail
  (`Pattern.freeVars_lookup_eq_none`).
* **`number` is `Int`,** not Racket's whole numeric tower.
* **`no-type` is a single untyped `Term`.** The source's type judgments check scope and
  nothing else, and so do these. A real sort discipline is deferred — `MERGE.md`, the
  closing section, has the shape it would take.
* **`valid-subst-faster` is not ported.** It is the source's operational matcher, unused
  by its main relation, and proving the two agree is a conjecture the source left open.
  The Lean model reaches an operational matcher from the other end instead:
  `Impl/Interp.lean`'s `matchQuery`, tied to `ValidSubst` by `exec_programStep`.
* **`set`, `Pattern.values`, `:merge` functions and multi-column outputs are all new.**
  None of them exist in the source; they are M9 and M11, designed in `MERGE.md`.

## Target design

Package `EgglogSemantics`; `README.md` has what each directory is for. As it landed:

```
Spec/      Syntax  Term  Database  Congruence  Eval  Match  Scope  Merge
Impl/      Closure  Interp  Merge  Check
Proofs/    one file per Spec/ or Impl/ subject, plus:
             Counterexamples   compiling witnesses that a statement is false
             Lattice           the same for execM_current_of_lattice
             Step              Spec/Merge.lean's step relations, split off from Proofs/Merge
Tests/     Examples  worked examples, as proofs and as #guards
           Egg       renders a Program as egglog source, for differential testing
Encoding/  Encode                         — parked M11; see ENCODING.md
```

### Syntax

`Expr` and `Term` are nested inductives over `List`. `Term` gets a hand-written
induction principle (`∀ f args, (∀ a ∈ args, P a) → P (.app f args)`) written once
and used everywhere; recursive definitions use the mutual `Term`/`List Term`
pattern, which is the reliable way to get structural recursion through the
nesting. `Lit` is `Int` for now, deliberately a separate type so base sorts can be
added when merge functions arrive.

A `Cmd.decl` case and a `Signature` (`FnName → Option FnDecl`) go in **from day one**, with
Phase 1 theorems carrying an `AllConstructors sig` hypothesis. This is what keeps the
`:merge` extension from churning the AST. As it landed, `FnDecl` carries `arity`,
`outArity` and `merge : Option MergeSpec`, where `none` **is** what makes a name a
constructor and `MergeSpec` is `.merge (List Action) (List Expr) | .noMerge`. The draft
here had a third `MergeSpec.union` case for constructors; folding it into the `Option`
removed the state in which a name both had a merge specification and was a constructor.

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
(restricted to `t ∈ db.terms`, so reflexivity only fires
for terms actually present) / `symm` / `trans` / `congr`. The `congr` rule is
written as a mutual inductive with a `CongList` companion rather than an
`∀ i, i < length` premise — same relation, workable induction — with a
`List.Forall₂ (Cong db)` bridge lemma.

A congruence-restoring pass **disappears entirely**, which is the main simplification:

- refl/symm/trans/congr become `Cong`'s constructors.
- "presence of children" becomes a structural invariant: `Database.addTerm`
  inserts a term together with all its subterms, and `Database.WF` asserts
  subterm-closedness plus that every asserted equality's endpoints and every
  binding's value are in `terms`.

This is observationally equivalent because no action ever consults congruence, so
deferring subterm insertion to a later rebuild is unobservable — recorded in the
source as a documented deviation with that justification.

### Where "restored congruence" went

There is deliberately **no closed-equality state**, and no "the reduction can no
longer step" predicate. The database always holds only asserted equalities, and
closure is a predicate rather than a state. Its two halves are handled
differently:

- The **relation** half (refl/symm/trans/congr) is never materialized. The only
  place the semantics consults congruence is `Matches`' side conditions, which ask
  `CongOn` — `Cong (db.withOperands ts)` — for a derivation directly. Evaluating an
  action and running a command never consult it at all, so nothing else needs it.
- The **term-set** half ("presence of children") is a real state change, and is
  the one part that stays in the state — as the `addTerm`/`WF.subtermClosed`
  invariant above.

The observable meaning of a finished program is therefore the pair
`(db.terms, Cong db)`, not a database with a big closed equality set.

This section used to sketch a `restore` that materialized the closure as a
comprehension over the relation, for the executable layer to use. **M10 answered it a
different way and the sketch is dropped:** `Impl/Closure.lean`'s `closure` computes the
closure over a `Finset` and `mem_closure_iff` proves it decides `Cong` exactly, so no
state ever carries a closed equality set — not even the interpreter's.

The e-graph as a *data structure* — a set of e-classes rather than a relation — is
then `Quotient` of `db.terms` by `Cong db` (an equivalence on `db.terms` by the M2
lemmas). That quotient is the bridge to M11: an e-class on this side corresponds to
an `@UF` leader on the encoded side.

### E-matching

The witness formulation: a substitution is valid when the pattern instance is
`Cong`-equal, *in the database extended with that instance*, to some witness term
already in the database. The witness is what forbids matching a term the e-graph
does not contain.

One deviation worth recording:

* `ValidEnv` requires the substitution's domain to be a *permutation* of the
  pattern's free variables rather than fixing its order. The extra substitutions
  this admits differ only by reordering, which no `lookup` can distinguish; making
  that precise is the environment-agreement lemma in M8.

Two facts Lean needs as lemmas:

- `Pattern.freeVars p db.env` excludes globally-bound variables, so `σ`'s domain is
  disjoint from `db.env`'s and appending the two never fails — plain append is
  correct. (This also preserves the real quirk that a globally-bound variable in a
  pattern denotes its value rather than being a match variable.)
- Envs only ever get consulted through `lookup`, so `evalLocalActions` is
  invariant under extensional agreement of environments. That lemma, rather than a
  list-level normal form, is what lets `Env.UnionAll`'s duplicate bindings be
  ignored.

### Steps

Because the database's components are `Set`s, an indexed union over *all* matching
substitutions is directly expressible, so the rule-firing half of a round is a function
rather than a nondeterministic relation:

```lean
def RunRules (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ db.rules, d ∈ RuleResults db r}
```

`sUnion` is left-biased on `env` and `rules`; `evalLocalActions_env` and
`evalLocalActions_rules` show every `d` in that set has `d.env = db.env` and
`d.rules = db.rules`, which is what makes the bias harmless.
`RuleResults`' `Option` carries the partiality of variable lookup;
`Proofs/Scope.lean`'s `programStep_isSome` proves well-scoped, evaluable programs never
hit `none`. What the draft got wrong is one level up: `(run)` is *not* a function, because
`RunStep` composes `RunRules` with a merge closure that chooses how many steps to take.

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
| M4 | `Match` | `ValidEnv`, `Env.UnionAll` |
| M5 | the step relations | `RunRules`, `CmdStep`, `ProgramStep` — now in `Spec/Merge.lean`; `Spec/Step.lean` is gone |
| M6 | `Scope` | `programStep_isSome` — a well-scoped, evaluable program runs to completion |
| M7 | `Examples` | the worked examples as closed proofs |

Two of those carry more weight than their size suggests. **`Cong.le`** is how every *negative*
fact about the closure is proved — "this pair is not derivable" means exhibiting a congruence
that omits it — and it is the shape the M11 checker-soundness argument would take. A design
without it cannot state a negative fact at all. **`evalLocalActions_isSome_of_scoped`** says a
well-scoped rule contributes on every substitution its query admits; `RunRules` silently drops
stuck firings, so that is the statement worth having rather than mere totality.

Follow-ups, in rough dependency order:

- **M8 — metatheory.** Partly done.
  - ✅ *Environment agreement.* `Env.Agree.of_perm` and `.append_left`,
    `Database.EnvAgree`, and `evalAction_envAgree` / `evalActions_envAgree` /
    `evalLocalActions_agree`. This is `Expr.eval_agree` lifted to whole action sequences,
    and it discharges both places the semantics is deliberately loose about environments:
    `Env.UnionAll` leaving a variable bound twice, and `ValidEnv` fixing a domain only
    up to permutation. The payoff is that `RunRules` sees a substitution only up to
    agreement, so an enumerator may emit one representative per class — which is exactly
    what `Impl/Interp.lean`'s `Env.canon` does.
  - ~~*Rounds.* `runRounds` (egglog's `(run n)`), `runRounds_succ'`, `Saturated`~~ —
    **deleted with the functional semantics.** `Cmd.run` is one round and `(run n)` is
    `n` copies of it, which `Spec/Merge.lean`'s `CmdStep` says in one line; nothing needed
    a named iterator, and schedules are still unmodelled.
  - ~~`ValidSubst` inversion, without which no example can state what a `run` does *not*
    produce~~ — **superseded by M10.** `exec_programStep` makes any statement about a
    *specific* program's result decidable: it transfers to the interpreter, where the
    closure computes. The `#guard` showing one round is not enough for the `Wrapper`
    example is already such a negative fact. Inversion is still wanted for statements
    quantified over *all* programs, which is where M11 will need it.
  - Remaining: nothing on the critical path. The matcher is the slow one by
    construction — `assignments` is `|terms| ^ |vars|` and `patternHolds` recomputes a
    closure per candidate — which is what keeps the differential cases tiny. The fix is
    **not** a cleverer *specification*: `exec_programStep` is the contract, so the
    reference implementation can be optimized wherever profiling says it is slow and the
    refinement re-established against the unchanged spec.
- **M9 — `:merge` functions.** Designed in [`MERGE.md`](MERGE.md). Partly done, and
  **merged into the main development** — there is one `Database`, one `Action`, one
  `Cmd`, and `Spec/Merge.lean` holds only what is genuinely new.
  - ✅ *Congruence is the functional dependency.* For a constructor, two rows with
    congruent keys have congruent outputs — `Proofs/Congruence.lean`'s `Cong.fd`, whose
    one hypothesis is the shape of a constructor's rows. A *theorem about* `Cong`, so
    every M2–M8 theorem transports rather than being reproved and `Spec/` keeps one
    congruence relation. The route here went through a second relation `MCong` carrying
    the dependency as a constructor, and a compatibility theorem `mcong_iff_cong`; both
    are deleted — see "The consolidation arc".
  - ✅ *The shape change.* A `:merge` body is an action list, so `MergeStep` is a relation
    on databases and `CmdStep`/`ProgramStep` are relations too. `Spec/Merge.lean` holds
    `Database.Out`, `Database.Recorded`, `MergeStep`/`MergeClosure`/`MergeSaturated`, the
    matching family (`Matches`, `ValidSubst`, `ValidQuerySubst`) and the step relations;
    `Prim` and `Term.blt` are in `Spec/Term.lean`. Evaluation was *also* a relation for a
    while, because a non-constructor application in an action was a lookup; that is now
    forbidden — see "Reading is a query atom" below — and `Expr.eval` is a function again.
  - ✅ *Multi-column outputs.* `Action.set` takes a `List Expr`, and `Pattern` gained
    `values` — egglog's lowered row atom `f(a…, v…)`, written `(= v (f a…))` at one value
    column and `(= (values v…) (f a…))` at more. It is the only read in the language.
  - ✅ *The implementation deletes; the specification does not.* `Spec/` stays append-only
    while `Impl/Merge.lean`'s merge phase drops the two rows it combined, as egglog does,
    and nothing else — `mergeRound_confined` proves the "nothing else": no term, no
    equality, no constructor row, no `.noMerge` row. So the contract splits into
    containment (`execM_contained`, proved), the untouched equality on the constructor
    fragment where the pass is the identity (`mergeRound_eq_self`), and `Database.Current`
    for lattice merges.
  - ✅ *The refinement chain.* 17 of 17 proved. **Nine were false as written** — three in
    ways their M10 counterparts in `Proofs/Interp.lean` had already solved, so read the M10
    counterpart before stating an M9 lemma. Five statements remain `sorry` in
    `Proofs/Merge.lean`, all known-false or hypothesis-defective, with compiling witnesses
    in `Proofs/Counterexamples.lean` and `Proofs/Lattice.lean`.
  - Remaining: those five. Everything else M9 named is done.
- **M10 — executable layer.** A `Finset`-based interpreter, a decidable congruence
  closure, and a refinement *biconditional* between the interpreter and `ProgramStep`.
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
    pattern and joins them (`Env.UnionAll`); the enumerator assigns
    the whole query's free variables at once and restricts per pattern with `Env.canon`.
    `Env.agree_canon` shows they agree up to `Env.Agree`, which is all `RunRules` can see.
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
  set. The interpreter runs whole programs as `#guard`s in `Examples.lean`, including the
  two-round `Wrapper` case, which has no hand proof because stating it needs `ValidSubst`
  inversion.

  The chain ends at

  ```lean
  theorem exec_programStep {p : Program} (hdecl : p.CtorDecls) {D : Database} :
      (exec p).map FDatabase.toDatabase = some D ↔ ProgramStep Database.empty p D
  ```

  **One** hypothesis, which arrived when the spec's command stepping became a relation, and
  it is not decoration: `Falsity.exec_programStep_needs_ctorDecls` exhibits
  `(function f () i64 :merge 7) (set (f) 0)` — a program whose only offence is a `:merge`
  declaration — where the row collides with *itself*, since `MergeStep` has no `a ≠ b`
  guard, so `ProgramStep` reaches two distinct states and `exec` returns at most one. A
  second hypothesis `p.SetLegal` sat here until the induction was re-examined: what it
  maintained was `Database.CtorRows`, which the refinement does not read, and what the
  refinement does re-establish is `Database.CtorState` — `WF` and `AllConstructors`, which
  a `set` disturbs neither of. Well-formedness came free: `FDatabase.WF` is defined as the
  spec's through `toDatabase`, so every `WF` fact is read through the refinement rather
  than proved by a separate induction.

**M10 is done**, and that is what makes the `#guard`s in `Examples.lean` and the
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
binary. **166 cases pass**: 60 random constructor, 30 random `:merge`, 76 curated (10
constructor, 66 `:merge`).

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

Two findings that the fragment was **not a subset** of egglog's language: a bare variable
was a legal query fact and `expr` action here and egglog's grammar rejects both (34 of the
first 60 cases died on it — now banned via `Expr.IsApp`; "What the port changed" has where
that laxity came from); and `Database.rules` is a `Set`, so a repeated rule is silently
ignored where egglog panics.

**Every case is checked for legality before it is written.** `writeCase` refuses to emit a
program egglog would reject — an illegal `set`, a use whose column counts disagree with the
declaration (`Impl/Check.lean`'s arity check), or a name used at two arities, which the
emitted `datatype` header cannot express. A rejected program is a *missing* case, not a
failing one, so the check aborts rather than skips.

What it does not cover: anything outside the fragment, and value columns, since
`(print-size)` counts key classes and is blind to them.

A performance note that is really a design note: `FDatabase` insertions deduplicate, because
a round's `union` copies every operand's terms and without dedup the per-substitution
`List.toFinset` inside `closureF` goes quadratic. Invisible to `toDatabase`.

- **M11 — the proof encoding.** Parked. See below.

- **M12 — one semantics. ✅ Done.** M0–M8's functions and M9's relations ran side by side
  over the one `Database` and the one `Action`. `Spec/` now defines egglog **once**:
  `Expr.eval`/`evalAction`/`evalActions` are functions, `MergeStep`/`RunStep`/`CmdStep`/
  `ProgramStep` are relations, `Spec/Step.lean` is deleted, and `Cong` is the only
  congruence. What was learned:

  - *Determinism is what reopened it.* Evaluation's uniqueness came to hold with **no**
    hypotheses — no `AllConstructors`, no `NoPrim` — because the only rule that read the
    database was `lookup`, and reading became a query atom. A relation that is a function
    unconditionally can simply be replaced by one.
  - *What must stay a relation.* Everything above an action, for a reason that has nothing
    to do with evaluation: `MergeStep` chooses **which** pair of rows collides and in which
    order, and `MergeClosure` chooses how many steps to take.
  - *The cost, as it came out.* Going the functional way below an action was right: the
    `Option` algebra `Proofs/{Eval,Match,Step,Scope,Interp}` is built on survived, and
    `Impl/Merge.lean` lost its whole evaluator, action and matching layer to
    `Impl/Interp.lean`'s. `Proofs/Scope.lean` paid for it: `Expr.eval` returns `none` at a
    lookup and at a mis-sorted primitive, so `Evaluable` threads a `Signature` beside
    `Scoped`'s scope, and `programStep_isSome` takes both.
  - *The recovery, intact.* `exec_programStep` is a **biconditional** on the constructor
    fragment, and that is what makes the differential cases bear on the specification
    rather than only on the interpreter. It holds there because that fragment has no
    `.merge` function, so no `MergeStep`, so `ProgramStep` is deterministic
    (`ProgramStep.det`).

## Extending with `:merge` (M9)

The design is [`MERGE.md`](MERGE.md). What this plan originally proposed is kept only for
the record of where it was wrong, since two of the mistakes were instructive:

- **A merge body is an action list, not an expression** — an extension local to this repo
  (`egglog/src/ast/parse.rs`, `9828dbf`); upstream `:merge` takes a single expression, so a
  body that `set`s another table cannot be written there. It is deliberate and discussed in
  the paper, but it means M9's shape is a fact about *our* egglog. So the observable value of a key
  class cannot be a fold over asserted rows, and there is no `SemilatticeSup` to lean on.
  Command stepping became a *relation* instead. (Evaluation did too, for a while, and then
  came back — see "Reading is a query atom".)
- **A non-constructor application is a lookup**, with no `:default` to fall back on.

What did stand: the signature was already in the AST from M1, so `MergeSpec` only had to
become reachable; rows replaced the bare term set, with congruence *as* the functional
dependency; and merge closure carries no termination claim. Base sorts (`i64`, `String`, a
real sort discipline in place of the single untyped `Term`) are still deferred — see "arity
checking" in the current priority.

## Reading is a query atom

**All reading happens in the query; all writing happens in the actions.** An application of
a non-constructor is a *lookup* — it reads a recorded row rather than building a term — and
`Impl/Check.lean`'s `Program.noLookup` says a program contains none, anywhere. The one place
a program reads is the query atom `Pattern.values`, which is egglog's lowered
`f(a…, v…)` and now covers every width: `(= v (f a…))` at one value column,
`(= (values v…) (f a…))` at more.

**What it buys.** Evaluation loses its `lookup` case, so it needs nothing of the database
but its signature and is a **function** again — `Expr.eval : Signature → Expr → Env →
Option Term` — and with it `evalAction`/`evalActions`. That is what closed M12. The one
remaining place the model over-approximates egglog's reads is the query atom itself, which
matches *any* recorded row where egglog matches the current one.

**Where it is stricter than egglog, checked against the binary.** egglog runs
`check_no_function_lookups_in_actions` (`src/typechecking.rs:1325`) on a **rule head** only,
and only for a seminaive rule. Three other positions read there and are rejected here:

| position | egglog | repro |
| --- | --- | --- |
| top-level action | accepted, copies the value | `(set (Copy (A)) (Dist (A)))` |
| `:merge` body | accepted; missing row is `Lookup on Zero failed in the merge function for Dist` | `(function Dist (Math) i64 :merge (max old (Zero)))` |
| nested in a query fact | accepted, flattened to two atoms | `(F (Dist k))` |

The first two are `Context::Full` and `Context::Write`, neither of which runs the check; the
third is egglog's query flattening, which this model does not have *as syntax*. Each has a flat
equivalent — `(rule ((= v (Dist k))) ((set (Copy k) v)))` for the first — so the loss is
notation, not expressiveness, except in the `:merge` body, where a body that reads another
table genuinely cannot be written.

Flattening's *effect* on a constructor operand is modelled, and has to be: `Matches.values`
adds the atom's operands to the database before consulting congruence, so `(Dist (G (A) (B)))`
matches a row written at `(G (B) (A))` after `(union (A) (B))` exactly as the flattened
`G(a, b, x), Dist(x, o)` does — the intermediate class is found by matching rather than by
having been built. `DiffTest.lean`'s `read-unbuilt-key*` cases pin it in both directions.

**What it exposed in `Encoding/Encode.lean`.** `encodeBuild` interns an application by `set`ting
the view and then *reading it back* with `(let x (@fView c…))` — a lookup in a rule head,
which egglog refuses. egglog does the same job with `set-if-empty-<View>!`, registered as a
**primitive** (`src/proofs/proof_fresh.rs`), and `expr_has_function_lookup` flags only
`ResolvedCall::Func`. So `encode` emits rule heads the real system rejects, and the fix is
the one egglog made: a `Prim`-style get-or-insert, which is a write. Recorded in
`Encoding/Encode.lean`, not done — it is M11 work.

## The minimal proof encoding (M11-min) — the road not taken

**A design record, superseded.** `Encoding/Encode.lean` builds the *full* encoding —
`@UF`, per-constructor views, rebuild rules, path compression — and the three theorems
were stated over that, then deleted (`ENCODING.md`). Two things below survived and are
current: "Proved against the specification", and the side condition. The rest is kept
because it is the cheapest sketch of what a union-find-free encoding would look like, if
the full one turns out to be too much.

**Proved against the specification, not against the Rust.** That is the decision that makes
this tractable, and it did carry over: no differential testing against real egglog, no
matching its row counts, no conversion layer. The claim is about our `encode` and our
`Cong`.

### What it would have dropped

Everything the real encoding needs in order to be *fast* — and all of which `encode` in
fact has:

- **No union-find, no canonical ids, no leader lookups.** Terms are their own ids — the
  "natural" term a rule builds is the id. No `@UF_<Sort>`, no `ordering-min`/`ordering-max`.
- **No view tables and no rebuilding.** Nothing is ever re-keyed.
- **No proof skeletons.** No nested `@Proof` terms, no `get-fresh!`, no `@Ast`.

Only the third held: `encode` has no skeletons, and structural fresh ids are what replaced
`get-fresh!`.

### What it keeps

The property we actually want — *every equality has a rule firing behind it, and every
recorded proof is valid* — via source constructors for terms and, per constructor `C`, a
view table `@CView : (S…) → (S, Proof)` whose `:merge` resolves congruence and records why.
That needs `:merge` (so not the `:no-merge` fragment) and multi-column outputs, which is
what `Action.set`'s `List Expr` and `Pattern.values` were built for; and it stays inside
reads-in-query/writes-in-actions, since a merge body has `old*`/`new*` bound by the
collision and there are no canonical ids to look up.

### The side condition that makes it work

Since the source constructors carry over, built-in congruence still applies to them in the
target — which would mean some equalities have no rule behind them, defeating the point.
That collapses to nothing **provided `encode` emits no `union` actions**: with `eqs` empty,
`Cong` on the target is syntactic equality. So "emits no `union`" is a syntactic property of
`encode` that makes the target's built-in congruence vacuous — the one M11 side condition
that survived both the congruence collapse and the deletion, and the one a restatement gets
for free, since `Cong` reads neither `rows` nor `sig`.

### What a proof value is

egglog's **user-facing** `Proof`, not `RawProof` — `CHECKER.md`, "Node kinds", has the
eight `Justification`s and what checking each one needs. It maps onto `Cong` almost one for
one, which is why checking is a structural induction with no conversion layer — the payoff
for `Cong` being inductive rather than a computed closure, and why dropping the skeletons
costs nothing (they exist to make proofs *small*, not checkable).

| `Justification` | `Cong` |
| --- | --- |
| `Fiat` | `assert`, and `refl` for top-level terms |
| `Rule` | a rule firing — `ValidQuerySubst` plus `RunRules` |
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
  to some `t` added at the top level." `Cong.refl`'s `a ∈ db.terms` is exactly that
  discipline.

### The invariant is a precondition of the encoding, not just a style rule

`ProofEncodingUnsupportedReason` (`src/proofs/proof_encoding_helpers.rs:851`) lists
**`FunctionLookupInAction`** — "action contains a function lookup. Finding the output of a
function is only supported in queries" — and **`UnsafeSeminaive`** — "Arbitrary RHS database
reads are not representable by the term/proof encoding." egglog's own encoder *refuses* a
program that reads on a right-hand side. So "reads in the query, writes in the actions" is
not merely egglog's default typechecking rule; it is what the proof encoding requires in
order to exist.

Its three theorems are the next section's, restricted. Its cost is size: without
canonicalization the encoded database is much larger — transitivity and congruence generate
quadratically many `@Eq` rows and nothing dedups them. Fine for a semantics, which is about
what is *derivable*, but row-count claims are out.

## Path to the full proof-encoding theorem (M11)

With M9 in place, the encoding becomes a translation between two instances of the same
semantics. **This is what was built, stated, and then cut back to the encoder alone**:
`Encoding/Encode.lean`'s `encode` survives; the three theorems below were stated over it
and deleted. [`ENCODING.md`](ENCODING.md) has why and what a restatement must avoid;
[`CHECKER.md`](CHECKER.md) scopes the checker half.

Three theorems, in increasing order of what they buy:

1. **Every proof the encoding writes is accepted by the checker** — for every `@Proof` row
   in the state `ProgramStep` reaches on `encode P`, `Checks` holds. About the *encoder*,
   with no reference to the source semantics, so it is what would catch a proof row written
   with the wrong column or a `@Congr` at the wrong child position.
2. **The checker is sound** — `Checks p` and `p` concludes `a = b` gives
   `Cong src ⟦a⟧ ⟦b⟧`. With (1), every stored proof witnesses a real equality.
3. **Simulation** — `Cong src a b` iff `a` and `b` share an `@UF` leader in the target.
   `⇐` is (1)+(2) at the union-find; `⇒` is completeness and needs the rebuild to have
   saturated. All three were stated with `src`/`tgt` the two states
   `ProgramStep Database.empty` reaches on `P` and `encode P`; the shape carries over, and
   what does not is `Rebuilt` as the saturation hypothesis for (3).

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

Other omissions, unaddressed since the port: schedules, extraction, containers.

## Verification

- `cd semantics && lake build` — the whole development typechecks. This is the check that
  must stay green.
- `make lean-difftest` — 166 cases against the real egglog binary. Watch the profile
  distribution, not only the pass count.
- `make lean-check` additionally fails on any `sorry`. It **currently fails by design**:
  5 statements are deliberately unproved, all in `Proofs/Merge.lean`, with witnesses in
  `Proofs/Counterexamples.lean` and `Proofs/Lattice.lean`. Use it to check that a change
  adds no *new* `sorry`.
- Axioms, on every change: `lean_verify` or `#print axioms` against the table in "Current
  priority". A green build does not catch an axiom leak.
- `Tests/Examples.lean` compiling *is* the M7 suite — each check is a closed proof or a
  `#guard`.

## `set` legality is a separate predicate, for now

The shape of a constructor's rows — output column is the application itself — is what
`Cong.fd` needs to make the table's functional dependency derivable congruence, and it is
what a `set` on a constructor destroys. egglog restricts `set` the same way: it is a type
error (`egglog/src/constraint.rs`). A constructor is a declaration with no merge
specification, so the condition is `mergeOf f ≠ none` — which admits `:no-merge` and
rejects an undeclared name, both checked against the binary.

That is `Action.SetLegal`/`Program.SetLegal` in `Spec/Scope.lean`, **beside** `Scoped`
rather than inside it, for one reason: `Scoped` relates syntax to a `Scope`, this relates
it to a `Signature`, and folding them together would put a signature argument on every
lemma in `Proofs/Scope.lean` that none of them would use. `Spec/Scope.lean` now runs all
four front-end checks — `Scoped`, `Evaluable`, `SetLegal`, `DeclsFresh` — over one walk
(`Check`), which is where the sharing went instead; they stay four predicates because the
theorems take different subsets, `programStep_isSome` wanting `Scoped` and `Evaluable`
where the row invariants want `SetLegal`.

**What `SetLegal` actually buys, and what it does not.** It is not a hypothesis of the
refinement theorem: `exec_programStep` re-establishes `Database.CtorState` — `WF` and
`AllConstructors` — and a `set` disturbs neither. What it maintains is `Database.CtorRows`,
which lives one level up in `Database.CtorFragment` (`CtorState` plus `CtorTerms`, legal
rules, and the rows), and that is what the functional dependency needs. The chain is
machine-checked end to end: `ProgramStep.ctorRows` carries `CtorRows` across a
constructor-fragment run, `Database.CtorRows.fd_hyp` turns it into `Cong.fd`'s row-shape
hypothesis, and `ProgramStep.out_union_cong` concludes that a constructor's outputs at one
key class are congruent at any state such a program reaches. **That chain is the whole
argument that `Spec/` needs no `fd` rule**, and until those two lemmas landed it existed
only in docstrings — `Cong.fd`'s hypothesis was never discharged by a proof term.

**`SetLegal` alone would not be enough either**, and the gap is not about actions.
Declaring `f` a `:merge` function makes the constructor row `f ↦ (f)` *already in the
database* collide with itself, and `MergeStep` then writes whatever the body computes there
— a non-constructor row, with no `set` anywhere. Hence the second, independent condition
`Cmd.CtorDecl`, which *is* a hypothesis of the refinement. Two counterexamples, for the two
things it protects: `Proofs/Step.lean`'s `exists_mergeStep_not_ctorRows` for `CtorRows`, and
`Falsity.exec_programStep_needs_ctorDecls` for `exec_programStep` itself, where the
self-collision makes the specification reach two states and the interpreter one.

## Arity checking

egglog fixes a function's column counts at declaration and checks every use against them.
`FnDecl` recorded both counts from M1, but until the check existed nothing read them outside
`Tests/Egg.lean`'s renderer, so the model accepted programs egglog's typechecker throws out.

egglog's check is one equation on the lowered atom: for an atom headed by `f`,
`|args| = |inputs f| + |outputs f|` (`constraint.rs`, `get_atom_application_constraints`), reported
as `TypeError::Arity`, "Arity mismatch, expected {expected} args". What each surface form
contributes to `|args|` is what makes the one equation say different things:

* an *expression* `(f a…)` — a top-level action, a rule head, a merge body, an argument — and a
  *query fact* `(f a…)` or `(= e (f a…))` each append exactly one fresh output variable, so both
  need `|a| = arity f` and `outArity f = 1`. A two-column function is rejected in all of those
  positions; the binary answers `expected 2 args: (Dist k)`.
* `(set (f a…) v)` appends the value list — one entry for a bare `v`, `|v…|` for `(values v…)` —
  so it needs `|a| + |v…| = arity f + outArity f`.
* the row atom `Pattern.values` appends the read values and needs the same sum. It has no single
  surface form: egglog writes it `(= v (f a…))` at one value column and `(= (values v…) (f a…))` at
  more, and answers "Unbound function values" if the tuple form is used on a one-column function.
  `Tests/Egg.lean` renders whichever fits, so the check is on the columns and not on the notation.

The last two are modelled by the stronger split `|a| = arity f` and `|v…| = outArity f`. egglog's
sum really does admit moving a column across the divide — with every sort `i64`,
`(= (values v) (Dist k j))` is accepted for `(function Dist (i64) (i64 i64) …)` — but only because
the sorts happen to agree. The model is untyped, so the sum alone would let it accept a program
whose meaning it then gets wrong. **This is the one place the check is stricter than egglog's.**

Two declaration-side rules from the same pass:

* a `:merge` result has one expression per value column — `TupleMergeArity`, "The :merge of tuple-output
  function {name} has {actual} columns but the function has {expected} output columns" — and must be
  a `(values …)` at all for a tuple-output function (`TupleMergeNotValues`);
* a constructor has exactly one value column — `TupleOutputNotAllowed`, "Function {0} has a tuple
  output, which is only allowed for plain functions (not constructors, relations, or view tables)".

A merge body is checked against the signature *including* the function being declared, so it may
`set` its own table; a forward reference to a function declared later is instead "Unbound function".
Both checked against the release binary.

**Why a static check and not a premise.** Arity is a typechecking error, raised per command by
`get_atom_application_constraints` before that command runs — the same pass, on the same AST node,
that raises `SetConstructorDisallowed` ten lines above it, which is what `Action.SetLegal` already
models. Two alternatives were rejected. A premise on `Expr.eval` would reject at *run* time what
egglog rejects statically, and would put a hypothesis on every lemma in `Proofs/Merge.lean`. A state
invariant "every row has its declared width" is the *derived* form and is what would let
`Impl/Merge.lean`'s row reads be proved total, but it belongs inside `Database.WF` and needs
preservation lemmas through `evalAction` and `MergeStep`; it is the follow-on, not this.

**`Bool`, unlike `Scoped` and `SetLegal`.** Those are `Prop`s with no computable counterpart, so
`Tests/Egg.lean` restates `SetLegal` as `illegalSets` and the two can drift. `arityOk` is defined
once and `ArityOk` reads it, so the difftest's check and the statement a proof would use are the
same definition — and deciding it needs no instance through the `List Expr` nesting.

Two things are deliberately not covered, both because `arityOk` reads the signature and nothing
else. That every *undeclared* name is used at one arity: a name with no entry has no declared
column counts to disagree with, so `Tests/Egg.lean`, which invents the `datatype` header from uses,
carries that half as `Program.arityConflicts`. (That a program must declare before it uses is
`Program.Evaluable`'s business, and `Program.declared` is how the difftest supplies the
declarations.) And a primitive's arity, which egglog also checks ("Arity mismatch, expected 2 args:
(min old new 3)"): `Prim.ofName` lives in `Spec/Term.lean` and is never in the signature, so this
is permissive rather than wrong.

A `Pattern.values` atom does **not** want the `SetLegal` companion restriction, and extending that
family to the query would be wrong rather than merely premature. It is the model's only read and
covers every width, so at one value column it is `(= v (f a…))` — what an ordinary constructor fact
lowers to, and legal egglog — and demanding `sig.mergeOf f ≠ none` there would reject it. What is
real about "egglog recognizes the tuple form only for a tuple output" is already enforced from the
other side: `Pattern.arityOk` pins `|v…| = outArity f` and `FnDecl.arityOk` gives a constructor
`outArity = 1`, so a *wide* read can never name a constructor.
