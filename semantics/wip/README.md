# Work in progress: declaration-time global resolution

`decl-time-globals.patch` implements the specification fix for a measured
divergence from real egglog: our `Spec/` resolves a rule's query variables
against the environment at **firing** time, so a top-level `let` arriving after
a rule captures that rule's query variable. egglog resolves per command
(`lib.rs:2588-2620`), rewrites only an already-`is_global_ref` reference
(`ast/remove_globals.rs:72-79`), and checks a rule's pattern names in a clone
(`ast/check_shadowing.rs:60-66`), so such a name stays an ordinary match
variable forever.

Measured, with `(rule ((Wrapper g)) ((Hit))) (let g (Zz)) (Wrapper (Bb))`:
real egglog gives `Hit 1`, our spec gives `Hit 0` — the spec under-fires. With
head `(Hit g)` the binary prints `(Hit (Bb))`, so `evalLocalActions`' env order
is backwards too once the query is resolved at declaration.

The patch covers `Spec/`, `Impl/` and `Proofs/` and **builds green** there. It
is not applied because `Encoding/` does not yet follow; the blocking question is
recorded in `Encoding/Complete.lean` at the `glob-late` section. In short: the
whole encoding development pairs a source rule with its program text, and
declaration-time resolution breaks that pairing on one in-domain shape — a
global whose definition is a literal, which `Expr.substGlobals` deliberately
refuses to substitute (substituting yields a bare-literal pattern, which
`Pattern.Grounded` excludes and `encodeQueryExpr` emits no atom for) but which
the specification's resolution must substitute.

Resolving it needs an owner decision between two encoder changes: emit an atom
for a bare-literal pattern, or substitute literals and re-derive
`Pattern.Grounded` under `Query.VarsKeyed`.
