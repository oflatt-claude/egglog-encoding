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
