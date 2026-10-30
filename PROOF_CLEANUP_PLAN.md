# Slotted proof cleanup plan

PR: https://github.com/saulshanabrook/egglog-encoding/pull/141

The source program is the authority for proofs. The intended result is an
understandable proof format, a small slotted checker that shares ordinary
checking with egglog, and minimal compilation metadata.

## Constraints

- Check the original slotted program, with rewrites desugared to rules and their
  original `:when` conditions in the body. Preserve nested expressions, binder
  semantics, declaration-scoped globals, sorts, and source names. Do not add
  generated matching conditions or replacement axioms to the source theory.
  Expand primitive guard evidence only in a temporary rule during checking, as
  accepted in the guard-node design below.
- Do not change the normal proof checker's semantics. Refactoring and exposing
  existing checking code are allowed.
- Ordinary propositions are exact equalities. Equivariance applies a finite
  permutation to both endpoints of a checked equality.
- Alpha derives `a = c` from `a = b` when `b` and `c` are alpha-equivalent.
  Preserve the exact left endpoint, free names, binding scopes, constructor heads,
  payloads, and carrier sort. Require a premise establishing term existence.
- RHS-only slots are chosen by the proof. Validate freshness against all other
  bindings and captured globals; accept any fresh candidate. Do not generate
  trusted freshness facts or require a particular name.
- Keep the earlier Makefile, `supports_proofs`, and Group cleanups separate.
- Apply `.claude/skills/tidy-diff-docs/SKILL.md`; keep LANGUAGE.md focused on usage.

## Stages

1. **Establish the shared checker boundary.** Expose single-step checking without
   changing normal traversal, validation, or caching. Exercise ordinary rules
   with conditions, equivariance, Alpha, nested binders, fresh slots, captured
   globals, and multiple sorts. Report findings before changing source metadata.
2. **Retain the original program.** Keep native parsed source commands in
   execution order and preserve push/pop scope. Reconstruct flattened rules
   through the compiler's lowering. Remove source text from e-graph metadata
   tables; retain only necessary origin and generated-name mappings.
3. **Remove the parallel source representation.** Use egglog's Expr, Fact, Rule,
   and Command types and type resolution. Share constructor/binder information
   with the slotted frontend. Remove the remaining Condition/Rewrite/Rhs model.
4. **Extend the ordinary proof format.** Use an enum with `Ordinary(egglog::proof::Proof)`,
   `Alpha`, `Equivariance`, and primitive guard evidence. Reuse ordinary equality
   propositions, justifications, IDs, and printing. Keep claims and the store in
   format.rs, the checker in its own
   file, and tests in separate files.
5. **Make renaming-guard evidence explicit.** Ordinary proof premises establish
   equalities to representatives; a slotted validator checks their permutation.
   Existence alone must never establish `renaming-=`.
6. **Separate checking from lifting.** Keep encoded row names, matching frames,
   generated variables, and flattening compensation out of the checker. Use
   explicit Alpha when bound spellings change; ordinary steps stay exact.
7. **Delete superseded paths and validate.** Preserve proof snapshots, minimized
   lifting regressions, supported benchmark coverage, and default proof fuzzing.
   Cover malformed permutations, capture, nonfresh slots, incorrect sorts,
   altered guards, scoped globals, and encoded replay. Run root `make check`.

## Checker boundary: implemented

- `ProofStore::check_step` takes a premise-checking callback. Ordinary traversal
  uses it with the same premise order and success-only cache as before.
- The production slotted checker delegates Sym, Trans, Congr, and Proj to this
  API. It retains carrier and well-formedness checks locally.
- Rule applications delegate to the ordinary checker after expanding primitive
  evidence into operand equalities and a validated primitive call. Source scopes,
  sorts, and RHS freshness remain local.
- Alpha is implemented in the format, checker, printer, normalizer, and lifting.
  Source axioms retain their original binder spellings. Refreshed spellings are
  derived from those axioms using Alpha and ordinary proof steps.
- Rule premises match exactly; implicit alpha matching was removed. Lifting
  supplies Alpha steps where needed, including repeated names in nested scopes.
- Claim and ClaimKind live in format.rs. Source syntax uses egglog's
  S-expression reader; structural AST conversion preserves slotted identifiers.
- Source rules now use native type resolution, as described below.

### Primitive guard nodes: implemented and validated

Keep one premise per original rule-body fact. `SlottedProof::Primitive` carries
its source predicate name and ordinary equality proofs for its operands.
`renaming-=` permits `a = ar` and `b = br`; the primitive validator compares
`ar` and `br` modulo alpha-equivalence and an injective free-slot renaming.
Other guards require reflexive operand proofs, preserving their existing term
validation. Primitive evidence cannot be used as an equality.

Only during checking, expand a guard into operand equality facts and a primitive
call on fresh witness variables. Add those witnesses to a temporary substitution,
then delegate the complete Rule step to `ProofStore::check_step`. The primitive
call's result is Unit, justified by ordinary literal reflexivity. Original source
rules, printed clauses, and substitutions retain their source form. Ordinary
checker semantics are unchanged. Restore its fact/action helpers to their original
private methods; only the single-step API is needed by the slotted checker.

Validators use the complete constructor binding information, including later
declarations. Captured globals cannot be overridden. Generated witness variables
must avoid all source and captured names; freshness of RHS slots is checked
against the original substitution before guard expansion.

Root `make check` passed in an isolated worktree excluding the unrelated nested
checkout. It covered 295 Python tests, the full Rust workspace, 43 compatible
slotted fixtures, 31 runtime/differential checks, 24 generated benchmark proofs,
and all seven default proof-fuzz profiles (200 cases). After the final printer
and review cleanups, `make nits`, all 100 experimental unit tests, 23 proof
integration tests, and the 43-fixture proof corpus passed again.

Claude Fable's read-only review found no correctness blocker. Follow-up cleanup
shares the guard-name table, removes the obsolete fact/action API changelog claim,
and tests rejection of bare equality evidence for a guard. Regression coverage
also includes both nonreflexive representatives, captured globals, later binder
declarations, witness-name collisions, wrong carrier sorts, and guard evidence
misused as equality. Snapshots show one premise per original guard line.

Validation logs: `/tmp/slotted-guard-node-check.log` and
`/tmp/slotted-guard-node-review-check.log`. Review:
`/tmp/slotted-guard-node-fable-review.txt`.

## Source cleanup: implemented

- Retain native source declaration, let, union, and rewrite commands through
  structural `slotted-source` records. No rule strings or flattened-rule JSON
  remain in e-graph tables. Source recording follows execution and push/pop scope.
- Reconstruct flattened native rewrites and generated names through the same
  compiler lowering used for encoding. Claims carry native expressions.
- Replay declarations incrementally so later carriers cannot change an earlier
  bare-slot union's sort or rule resolution. Share the frontend's constructor and
  binder model.
- Replace Condition/Rewrite/Rhs with native resolved Facts, union Actions, and
  Rules. A source rule retains only its native rule and captured globals.
- Resolve through egglog's typechecker with typed initial bindings for globals
  and RHS-only slots. Type inference receives the expected carrier/Unit context
  for plain facts; temporary constraints are removed before storing the rule.
- Preserve the slotted frontend's identifiers, including `_`, keyword-like
  variables, and `$`-prefixed payload variables. Resolve payload locals and
  captured globals separately when their spellings overlap.
- Guard nodes group ordinary equality proof references, one per operand. The
  ordinary checker invokes their primitive validators after temporary expansion.
- The format, claims, and witnesses are in format.rs; checking is in checker.rs.
  Encoded names and flattening compensation stay in lifting. Ordinary checker
  semantics remain unchanged.
- Production tests cover the former checker-adapter prototype; the duplicate
  test-only checker has been removed. LANGUAGE.md remains a usage reference.

## Previous-stage validation

The seven checker-adapter integration tests pass, including Alpha composed with
ordinary steps, malformed Alpha, equivariance, original `:when`, guards, and
captured globals. The production slotted corpus passes all 43 compatible files;
11 `subst` fixtures remain explicitly unsupported.

Independent read-only review found no semantic change in ordinary checking.
It caught a sort-name regression in the adapter, which is fixed and covered by
an end-to-end test. No soundness blocker remains in the reviewed checker boundary.

Root `make check` passed in an isolated worktree containing these changes, excluding
the unrelated nested checkout from Python discovery. Coverage includes 295 Python
tests, the full Rust workspace, 40 production proof unit tests, seven adapter
tests, the compatible slotted corpus, 31 runtime checks, 24 generated benchmark
proof runs, and all seven default proof-fuzz profiles (200 cases total). The final
sort-name regression also asserts that a proof is actually produced.

Validation logs: `/tmp/slotted-production-alpha-final-check.log` and
`/tmp/slotted-production-alpha-final-regression.log`.

## Source-cleanup validation

Root `make check` passed in an
isolated worktree matching the working files, excluding the unrelated nested
checkout from Python discovery. It covered formatting, linting, types, doc links,
295 Python tests, the full Rust workspace, all 23 production proof integration
tests, 43 compatible slotted proof fixtures, 31 runtime checks, 24 generated
benchmark proof runs, and all seven default proof-fuzz profiles (200 cases total).
Unsupported `subst` fixtures and incompatible no-aliasing benchmarks remain
explicit skips.

Regression coverage includes parsed/printed replay, original guards, declaration
scope, native variable names, constructor/guard name collisions, and attempts to
override captured globals. The full run caught a malformed `:when` diagnostic
regression; restoring the frontend's existing option validation fixed it.
Independent review found no remaining blocker in the source/checker boundary.

Validation log: `/tmp/slotted-native-proof-final-check.log`.

## Format correction: implemented and validated

The earlier completion report overstated format reuse: checking was shared, but
ordinary proof variants were still duplicated. That stage introduced an enum
wrapping the original `Proof`, with Alpha and Equivariance. The subsequent guard
node stage adds primitive evidence without introducing a separate equality type.

- Reuse `Proposition`, `ProofId`, ordinary justifications, dependency traversal,
  and printing. Ordinary checker semantics remain unchanged.
- Remove `SlottedPremise`; validate renaming guards using ordinary equality
  evidence and structural slot correspondence.
- Name the encoding pass `lift_slots`, retain `unflatten`, and name their shared
  coordinate bookkeeping `coordinates`. Proof lifting names the whole pipeline.
- Keep proof-module tests in separate files.

Root `make check` passed on this representation: 295 Python tests, the full Rust
workspace, 23 proof integration tests, 43 compatible source fixtures, 31 runtime
checks, 24 generated benchmark proofs, and seven proof-fuzz profiles (200 cases).
The isolated validation worktree matches the working files and excludes the
unrelated nested checkout from Python discovery.

Claude Fable reviewed the diff through the installed CLI and found no correctness
blocker. Its recommendations are applied: check all premise references before
dispatch, reject unsupported primitive guards, remove redundant helper and map
layers, and use consistent module visibility and test-file placement. New
checker-level cases cover binder scope and non-injective renaming guards. The
final `make nits slotted-proof-tests` run passed, as did all 95 experimental unit
tests and 23 proof integration tests after these refinements.

Validation logs: `/tmp/slotted-proof-wrapper-final-check.log`,
`/tmp/slotted-proof-wrapper-review-check.log`, and
`/tmp/slotted-proof-wrapper-review-unit.log`. Review:
`/tmp/slotted-proof-wrapper-fable-review.txt`.

`MalformedStep` now exposes structured error variants. Its regression checks
that invalid step construction reports the conflicting inputs without changing
the store. Root `make check` passed again, including all 96 experimental unit
tests. Validation log: `/tmp/slotted-malformed-step-check.log`.
