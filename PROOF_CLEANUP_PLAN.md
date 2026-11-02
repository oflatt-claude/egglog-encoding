# Slotted proof cleanup plan

PR: https://github.com/saulshanabrook/egglog-encoding/pull/141

The source program is the authority for proofs. The format, checker contract,
and lifting derivations are documented in
[the proof guide](egglog-experimental/src/slotted/PROOFS.md).

## Agreed constraints

- Check original slotted rewrites, desugared to rules with their original
  `:when` conditions. Preserve nested expressions, declaration scopes, source
  names, and binder semantics.
- Reuse egglog's ordinary proof checker without changing its semantics.
  Every stored proof states an ordinary equality. Alpha and equivariance are
  explicit steps; `RenamingEq` is a typed rule premise, expanded only for checking.
- Accept any fresh RHS-only slot name. Validate freshness against other bindings
  and captured globals rather than trusting generated freshness facts.
- Keep compilation metadata out of the checker. The resolved program is
  independent of proof arenas; derive the checker context from it.
- Keep tests in separate files and language reference docs focused on usage.
  Apply the repository's tidy-diff-docs skill to changed documentation.

## Final cleanup checklist

- [x] Separate type resolution from the materialized proof context, use resolved
  expressions directly, and share global/local collision handling.
- [x] Split slot lifting by responsibility and classify generated rules with an enum.
- [x] Derive corpus proof expectations from source checks and classify unsupported
  substitution without matching diagnostic text.
- [x] Remove the unused egglog source-program accessor.
- [x] Retain this checklist and the agreed constraints instead of development logs.
- [x] Run root `make check`, preserving proof snapshots and covering supported
  fixtures, benchmarks, and default proof fuzzing.

## Alignment with the ordinary proof compiler

The ordinary pipeline registers primitives, resolves source commands, applies
proof normal form, and preserves that typed program for checking before
instrumenting a separate copy. See `resolve_command_before_proofs` and
`resolve_command_inner` in [egglog/src/lib.rs](egglog/src/lib.rs).

| Responsibility | Ordinary proofs | Slotted proofs |
| --- | --- | --- |
| Primitive validators | Attached during type resolution | Attached during source resolution using the query's visible binder declarations |
| Guard normal form | A compiler pass over resolved queries | Shared `proof_form_fact` helper, called while lifting and checking each rule application |
| Checking context | Prepared for the proof traversal | One context reused for ordinary steps and expanded source rules |
| Preserved source | Resolved commands retained before instrumentation | Source syntax recorded and resolved during extraction |

Further simplifications, in dependency order:

- [ ] Prepare normalized rule bodies and the expansion of `RenamingEq` once per
  source program. Keep original rules for source-level proofs; instantiate only
  auxiliary bindings and premise representatives for each rule application.
- [ ] Preserve resolved source and flattening results at the compiler boundary,
  so extraction consumes those pass outputs directly. This requires a structured
  compiler result alongside the current serialized command interface.

Binding-aware Alpha, Equivariance, and fresh-slot validation remain slotted
semantics. The ordinary checker continues to own rule and equality validation.
