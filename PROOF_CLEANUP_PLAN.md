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
| Guard normal form | A compiler pass over resolved queries | Prepared with the checking context using `proof_form_fact`; rule steps instantiate bindings |
| Checking context | Prepared for the proof traversal | One context reused for ordinary steps and expanded source rules |
| Preserved source | Resolved commands retained before instrumentation | Resolved source and flattened rules retained by compilation at each proof query |
| Flattening | Ordinary query normalization precedes instrumentation | Forward transformation and proof unflattening live together in `slotted/flatten/` |

Both encodings replace implicit equality maintenance with generated tables and
rules. Slotted encoding additionally tracks slot maps, binding scopes, and
symmetry groups. Applying ordinary proof instrumentation to that lowered program
is a valid composition of passes. Its proofs then need slot lifting and
unflattening to reach the original source rules; those inverse transformations
remain necessary even with a cleaner compiler interface.
The ordinary proof pass's saved source is already the lowered slotted program.
Slotted must preserve its own typed input before its own lowering pass.

The compiler returns a `CompiledProgram` with lowered commands, resolved source
programs, flattened rewrites, generated-name mappings, and structured proof
requests. `run` handles proof queries in command order, using the retained source
visible at each query. Text output serializes only lowered commands. Encoded
replay supplies the original source through `--slotted-source`, following the
ordinary proof mode's explicit checking-program contract.

Compiler-boundary cleanup:

- [x] Retain original resolved programs and flattening outputs during compilation.
- [x] Execute compiled inputs through the shared CLI, preserving push/pop,
  successive inputs, command order, and declaration-scoped globals.
- [x] Remove source records, source-datum transport, JSON query metadata, and the
  replay compiler. Proof requests refer to retained data by ID.
- [x] Prepare proof-normal-form rule bodies and `RenamingEq` expansion with the
  checking context, leaving only proof-specific bindings and premises to each step.
- [x] Support encoded replay with an explicit original source program.
- [x] Validate the compiler boundary, unchanged proof snapshots, scopes, replay,
  and rejection of altered checking programs with root `make check`.

Binding-aware Alpha, Equivariance, and fresh-slot validation remain slotted
semantics. The ordinary checker continues to own rule and equality validation.
