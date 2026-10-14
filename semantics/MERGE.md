# Merge semantics

The specification in [Step.lean](EgglogSemantics/Spec/Step.lean) supports functions with
multiple output columns and action blocks in their merge bodies.
[Impl/Merge.lean](EgglogSemantics/Impl/Merge.lean) supplies an executable interpreter;
[Proofs/Merge.lean](EgglogSemantics/Proofs/Merge.lean) proves its refinement contract.

## Entries and reads

A constructor's entry is the term `f(args)`. A merge function's entry is
`f(args ++ outputs)`, with the key/output split given by its declaration. `Database.eqs`
records equations, and `Database.terms` consists of the terms related to themselves by
`Cong`. Building an entry records it and its subterms through reflexive equations.

Value expressions evaluate constructors, `min`, literals, and variables under a signature and
environment. A complete atom such as `(LowerBound expr bound)` reads a function row in a
query and records one in an action. Its declaration determines where the key columns end
and the output columns begin. Entry atoms cannot be children of value expressions or
operands of equality and union.

`Database.Out` permits any recorded output at a congruent key. Since the specification
keeps old entries, this need not be the implementation's current output. Equality patterns
retain a held witness congruent to both evaluated sides: `(= term term)` succeeds only
when that class exists in the database.

The model has integer and Boolean literals but no general sort system. Static scope,
declaration, union, and write checks live in [Scope.lean](EgglogSemantics/Spec/Scope.lean).
The executable `arityOk` and `noLookup` checks in
[Check.lean](EgglogSemantics/Impl/Check.lean) are used before differential-test emission.
Arity checking requires an entry atom's full column count to match the declaration.
Nested expressions use constructor arities and must evaluate as values. These checks are
separate from the step relation; the interpreter indexes an entry only when its columns
have the declared width.

## Collisions and command steps

`MergeStep.collide` takes two entries with congruent keys and conflicting outputs. It
installs the `mergeEnv` parameters, runs the body actions, evaluates one result expression
per output column, and records the resulting entry. Body actions can build terms, assert
unions, or write other tables. Single-column merges bind `old` and `new`; multi-column
merges bind `old0`, `new0`, and so on. The ambient environment is restored afterward.

`FnDecl.unchangedWidth` determines which output columns count as a change. An explicit
`identityVals` takes precedence; otherwise an action block compares all output columns.
Equal compared prefixes skip the body. A single-expression merge has no default skip,
since a merge such as `(+ old new)` can change a value even when its inputs are equal.
The congruence tables have a single output column and compare it directly.

`MergeClosure` permits any finite sequence of merge steps. Every command ends in a merge
phase, including a declaration, a rule registration, and a top-level action. A `run`
fires the named ruleset against the pre-state and then merges. A `saturate` repeats rounds
until both rule firing and merging leave the specification state unchanged.

## The executable row index

`FDatabase.rows` is a finite index in addition to the terms and equations retained by
`toDatabase`. The interpreter replaces colliding rows and removes displaced rows from
this index. Terms and equations remain recorded, so the denotation still grows even
when the current row index shrinks.

For a collision, `mergeOneWith` prefers the row at the canonical key as the resident row;
insertion order breaks the remaining tie. `mergeOneOriented` passes that resident row as
`old` and the arriving row as `new`. `noConflict` implements the unchanged-column test.
`mergeRound` processes collisions, and `mergeSaturateF` repeats until the state settles.
Fuel exhaustion returns `none`, rather than a partially settled result.

Term ordering (`Term.blt`) is structural. It does not reproduce Rust's allocated value
ordering. Programs that observe which representative `min` selects can therefore differ,
even in row counts.

## Interpreter contracts

For constructor programs, `exec_programStep` relates `exec` to `ProgramStep` by an
if-and-only-if. It requires `p.CtorDecls` and either `p.NoSaturate` or a successful
interpreter execution. The latter condition accounts for the interpreter's finite
saturation fuel. See [Proofs/Interp.lean](EgglogSemantics/Proofs/Interp.lean).

For merge programs, the proved statement is:

```lean
theorem execM_contained {p : Program} (hns : p.NoSaturate)
    (hp : FDatabase.empty.ProgramLegal p)
    (hcond : p.UnionFree ∨ p.OrderingFree) {d : FDatabase} (h : execM p = some d) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ d.toDatabase.Recorded db
```

`Recorded` allows the interpreter's information to be represented up to congruence in a
reachable specification state. It does not identify the two states or establish that the
interpreter computes every output the specification permits. The union-free arm keeps
congruence diagonal; the ordering-free arm permits unions while excluding `min`, which
compares terms structurally and so breaks congruence-stable evaluation.

`NoSaturate` is required by this refinement proof: an interpreter fixpoint need not be a
specification fixpoint when the specification permits more matches. The
[encoding correspondence theorem](ENCODING.md#proof-status) separately handles
successful saturating target executions.

There is also no general theorem that the interpreter computes the greatest recorded
output of a lattice merge. `Database.Current` defines that notion;
[Lattice.lean](EgglogSemantics/Proofs/Lattice.lean) and
[Counterexamples.lean](EgglogSemantics/Proofs/Counterexamples.lean) retain counterexamples
to stronger candidate contracts and unrestricted ordering transports.

## Differential testing

[DiffTest.lean](DiffTest.lean) includes curated and generated merge programs and emits
them through [Tests/Egg.lean](EgglogSemantics/Tests/Egg.lean). `make lean-difftest` compares
per-function row counts with the workspace's Rust egglog binary. Fixtures that guard on
an output value make selected value differences observable as additional rows.

Row-count agreement does not establish equality of table contents. The corpus covers a
restricted collection of merges; current-value reads, representative choices, and
order-sensitive bodies can expose differences between the model and Rust. The
interpreter theorem and the differential tests provide distinct checks, each within its
stated scope.
