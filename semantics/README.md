# EgglogSemantics

A Lean 4 model of egglog's semantics, ported from the Redex model in
[egglog PR #324](https://github.com/egraphs-good/egglog/pull/324). The goal is to model
egglog as cleanly as possible for a paper, and then prove things about an implementation.
Proving things about egglog's proof encoding is the eventual payoff, and is **parked**.

**Which egglog.** This models egglog *as extended in this repo*, not a released one. Two
extensions are load-bearing and are part of what the paper discusses:

| extension | upstream `egraphs-good/egglog` | here |
| --- | --- | --- |
| multi-output columns — `(function Pair (Math) (i64 i64) …)` | `parse error: expected output sort` | accepted |
| `set` inside a `:merge` body — `:merge (<action>* <result>)` | `:merge` takes a single expression | accepted |

Checked against upstream `c92a910` (v2.0.0). The second is why M9 makes a merge a *step
relation on databases* rather than a function combining two values — a body that writes
rows cannot be modelled as a fold. `make lean-difftest`'s oracle is this repo's binary, so
it validates against the extended language.

**Picking this up?** Start with [`PLAN.md`](PLAN.md), "Current priority" — what we are
working on now, what is parked, the two interpreter contracts, and how to check a change.

The rest of `PLAN.md` has what the port changes and why, and the milestones.
[`MERGE.md`](MERGE.md) is the `:merge` design (M9). Two files are parked with M11:
[`ENCODING.md`](ENCODING.md), what was learned from the encoding's theorems before they were
deleted, and [`CHECKER.md`](CHECKER.md), what a Lean model of egglog's proof checker would cost.

One thing worth knowing before reading any of it: `Spec/` is append-only and `Impl/` is
not. The reference implementation deletes superseded merge rows because egglog does, so the
contract between them is a **containment**, not an equality — except on the constructor
fragment, where the merge phase is the identity and `exec_programStep` still holds.

## Layout

The tree separates *what is being claimed* from *why it holds*, so the first can be
read closely and the second skimmed.

| | contents | theorems |
| --- | --- | --- |
| `EgglogSemantics/Spec/` | the semantics — what an egglog program means | none |
| `EgglogSemantics/Impl/` | the reference implementation, which computes it | none |
| `EgglogSemantics/Proofs/` | everything proved about the two, one file per subject | all |
| `EgglogSemantics/Tests/` | example programs as proofs and `#guard`s, and the `.egg` emitter | a few |
| `EgglogSemantics/Encoding/` | **parked M11** — the encoder `encode` and nothing else; its theorems were deleted, and [`ENCODING.md`](ENCODING.md) is what survives them | none |

`Spec/` and `Impl/` hold **definitions only** — no `theorem` appears in either. The
one exception the language forces is a proof needed to *make* a definition: the
`decreasing_by` on `Impl/Closure.lean`'s `closure`, and decidability instances. Those
are inlined rather than pulled out into named lemmas, so nothing in `Spec/` or `Impl/`
is there for a proof's sake.

Reading order for `Spec/`: `Syntax` → `Term` → `Database` → `Congruence` → `Eval` →
`Match` → `Scope` → `Merge`. The semantics is defined **once**, relationally: `Merge`
holds the matching relation and the step relations, and there is no functional
duplicate of either. `Impl/` has `Closure` and `Interp`, with `Merge` adding only M9's merge
phase and `Check` the two front-end checks that are `Bool` rather than `Prop`.

Each `Proofs/X.lean` is about `Spec/X.lean` or `Impl/X.lean`, with three exceptions worth
knowing about. `Proofs/Counterexamples.lean` and `Proofs/Lattice.lean` hold compiling
witnesses that particular statements are **false** — `sorry`-free and in the build, so a
refuted statement cannot quietly come back. `Proofs/Step.lean` is about `Spec/Merge.lean`'s
step relations, split from `Proofs/Merge.lean` only because `Proofs/Interp.lean` sits
between them.
`Proofs/Interp.lean` holds `exec_programStep`, the biconditional that ties spec and
implementation together.

## Building

```sh
lake exe cache get     # prebuilt Mathlib binaries
lake build
```

or, from the workspace root:

- `make lean-check` — builds and fails on any `sorry`. It **currently fails by design**:
  5 statements are deliberately unproved, all in `Proofs/Merge.lean`. Use it to check a
  change adds no *new* one.
- `make lean-difftest` — runs the interpreter and egglog on the same generated programs and
  compares per-function row counts, for the constructor fragment and for M9's `:merge`
  functions. 166 cases. Needs a release `egglog` binary.

Requires [`elan`](https://github.com/leanprover/elan); the toolchain is pinned in
`lean-toolchain` and Mathlib in `lakefile.toml` / `lake-manifest.json`.

## Editing with Claude Code

The workspace `.mcp.json` declares a [`lean-lsp-mcp`](https://pypi.org/project/lean-lsp-mcp/)
server pointed at this directory, which gives per-declaration diagnostics without a full
`lake build`, and `lean_verify` for auditing a theorem's axioms — a stronger `sorry` check
than grepping, since it traces into Mathlib. It needs `uvx` and `elan` on `PATH`, and the
server caches imports: after editing a file's *dependency*, rebuild through the server
rather than the shell or its answers go stale.
