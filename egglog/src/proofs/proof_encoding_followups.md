# Follow-ups after the minimal proof encoding

Work deliberately left out of the encoding-rework PR, which is already large.
`proof_encoding_rework.md` is that PR's plan and record; this file is what comes
next, with the evidence for each so nobody has to re-derive it.

Where a number appears here it was measured on `math-microbenchmark.egg` under
`--proofs -j 1` unless said otherwise, against that PR's final state.

## 1. A write-only relation still gets a full table

Every table is a `SortedWritesTable` (`egglog-bridge/src/lib.rs:748`), so a proof
relation pays for FD key semantics over its key columns, sorted storage,
dedup-on-merge, a rebuild column list, and a merge callback.

None of that is needed for one:

* No rule body joins a proof relation. Verified independently twice — every
  occurrence of `@Sym` / `@Trans` / `@Congr` / `@Rule_k` / `@RebuildEq_k` /
  `@DisplacedShared*` / `@Fiat` / `@MergeIdx` / `@MergeRow` in the generated
  program is inside a `(set …)`.
* There is no functional dependency to enforce. Every row's output is a fresh id
  from `get-fresh!`, so keys are unique by construction.
* Nothing unions a `@Proof` value, so there is nothing to rebuild.
* Extraction reaches these rows only by following a proof id it already holds, so
  a row nothing names is unreachable rather than merely unread.

**The cost is not in Apply.** `Instr::Insert` is already a plain append into a
per-table staging buffer; FD enforcement and merge dispatch happen in
`SortedWritesTable::merge`, and index maintenance is lazy, on read during Search.
So look in Merge and in index construction, not in the write.

**Supporting evidence that Merge is not paying for row *volume*.** Packing each
merge collision's `Sym` + `Trans` into one row halved merge-body proof rows
(corpus-wide 2920 statements to 1472; 2 rows per collision to 1) and moved merge
time by only **-116 ms of 2.02 s, 5.7%** (`a932b22` to `70479df`, 8 rounds,
disjoint intervals). Merge cost is therefore mostly per-row machinery rather than
the number of proof rows, which is exactly what a cheaper table for these
relations would address.

**Two scoping corrections to make before acting.** "Term tables are write-only"
is true only of the proof relations above:

* `<S>Proof` (`@MathProof`) **is read** — rebuild heads look it up action-side
  (`(let @pv13 (@MathProof c0_))`), which is 8% of Apply on its own.
* The FD view tables (`@AddView`, `@NumView`) and `@UF_<S>` are queried in every
  rule body and are not candidates.

## 2. `stage_batch` on the merge path

The Apply work hoisted three per-row costs out of `Instr::Insert` / `Remove`: the
`NotificationList::notify` (an `ArcSwap` guard plus a `ConcurrentVec::read`, for
an idempotent dirty flag), the `Mask::iter_dynamic` pool round-trip that every
table wider than four columns paid to hold one row, and the mutation-buffer
resolution. That was **-31% Apply** (1.848 s to 1.267 s; `eggcc-2mm` 0.348 s to
0.235 s).

Merge functions, container rebuild and `TableAction::insert` all still go through
`ExecutionState::stage_insert` one row at a time, so they still pay all three.
`ExecutionState::stage_batch` now exists. Every proof relation is 5-9 columns
wide, so the `iter_dynamic` path applies.

This is the best-evidenced remaining lever on Merge, and it is independent of
item 1.

## 3. Updating a row in place

A view rebuild emits a delete and an insert for the same logical row:

```
(delete (@AddView c0_ c1_))
(set (@AddView c0_canon_ c1_canon_) (values e2_canon_ @pv32))
```

Eight such pairs in a two-constructor program. An in-place update would drop the
delete. Sizing: `Instr::Remove` is **34 ms, 2% of Apply** (0.74 M row-lanes at
45 ns), so the Apply win is small on its own — the open question is whether it
also avoids re-sorting and re-dedup in Merge, which is where item 1 says the cost
lives. Worth measuring together with item 1 rather than separately.

Note the delete must stay ordered before the insert: when only the e-class moved,
the canonical key equals the old one, so deleting afterwards would drop the row
just written.

## 4. `get-fresh!` as an instruction

9.6 M calls at 12 ns each, ~110 ms, about 8% of Apply — all `dyn invoke` overhead
around one `fetch_add`. It is *not* a dispatch-on-string problem: the sort name is
a constant `QueryEntry` resolved at rule-build time and never hashed at runtime,
and 12 ns is the `invoke_batch` floor.

`WriteVal::IncCounter` and `Instr::ReadCounter` already exist, so the lowering
machinery is there; the work is threading the primitive through typechecking into
the rule builder.

## 5. Deferred from the rework plan

* **Phase 3b** — siting the top-level actions, a per-base-sort `Fiat`, then
  deleting the `@Ast` sort. All three wait on one decision: which program the
  `Fiat` site index counts against, since `lower_inputs` runs before
  `remove_globals` and the encoder's site counter lives after it.
* **Phase 5** — re-enable CSE as a pass over the *encoded* program (it currently
  runs before proof encoding and reshapes rule heads, so the encoder and the
  checker would see different heads), repair term mode, and restore the two `dd`
  nightly endpoints.
* **The encoder reads `BuildSites`.** The full "one head traversal parameterized
  by `Option<bindings>`" unification was prototyped and rejected — it added 174
  net lines and cost 2 extra `RuleLink` rows per nested-`rewrite` firing, because
  the encoder's fold and the reconstructor's fold never run on the same head and
  so share no contract. What *is* duplicated is the position bookkeeping:
  `record_bridge`'s order against `BuildSites::bridge_order`, and
  `nat_conn.get(arg)` against `BuildSites::children`. Both are already computed
  statically by `build_sites`. That is the smaller, differently-shaped refactor.

## 6. Known and not fixed

* A non-eq container built in a rule head passes `file_supports_proofs` and then
  panics in the checker (`Fiat proof claims 10 = 10, which is not established by
  globals`), because `reflexive_value_term` recognizes neither the container head
  nor a non-eq container as a value. Pre-existing; no corpus file does it.
* `Mask::iter_dynamic`'s per-row pool round-trip is still on the
  `LookupOrInsertDefault` and external-function paths, so a future wide-arity hot
  instruction will re-pay what the Apply work removed from `Insert`.
* `set-if-empty` and `view-proof` each take an `RwLock::read()` plus a
  `HashMap<String, _>` lookup **per row** in `ActionRegistry`, worth ~43 ms (3%).
  Measured and rejected: `EGraph::remove_last_table` can replace or remove a
  name's `TableAction`, so a memo can go stale, and making it safe needs a
  generation counter threaded outside the lock.

## 7. How to measure without fooling yourself

* **Harness node count: `grep -c "PROOF-RECONSTRUCT "`, with the trailing space.**
  It is 13392. Without the space the pattern also matches the 1034
  `PROOF-RECONSTRUCT-DETAIL` lines and gives 14426 — and because the overcount is
  deterministic it reproduces across commits and reads as a stable baseline.
* Six of the largest corpus files (`eggcc-2mm`, `hardboiled_conv1d_32`,
  `integer_math`, `math-microbenchmark`, `math-microbenchmark-mini`,
  `web-demo/eqsolve`) do not reproduce their own *proof-table* row counts, since
  those take a row per merge collision. The e-graph is deterministic:
  `(print-size)` and every rule's `num matches` reproduce exactly. Diff the
  `(print-size)` block alone — a whole-output diff is dominated by timing lines
  and a hash-ordered rule report, and looks nondeterministic on every file.
* A contended box cannot resolve a 100 ms phase effect. A -219 ms merge result
  taken under load became -116 ms when the same pair was re-run alone. Check load
  before trusting a timing, and prefer a single-file run at more rounds over a
  six-file run when the effect is small.
* `perf`, `gdb` and `samply` do not work in the container (seccomp blocks
  `perf_event_open`). Deterministic instrumentation inside
  `ExecutionState::run_instrs` — the function the engine's own Apply timer wraps —
  reproduced the reported Apply total to within 3%, and is the way to get a
  breakdown here.
