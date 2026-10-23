# The slotted language

`egglog-experimental --slotted` compiles programs with slots and binders to
ordinary egglog tables and rules, then evaluates them through the normal CLI.
A slotted term denotes an e-class together with a renaming of its free slots.
Two terms can therefore belong to the same class without denoting the same
variables.

```bash
cargo build -p egglog-experimental
target/debug/egglog-experimental --slotted egglog-experimental/tests/slotted/paper/figure-3.egg
target/debug/egglog-experimental --slotted --mode desugar egglog-experimental/tests/slotted/paper/figure-3.egg
```

File arguments, stdin, serialization, and timing reports use the normal CLI.
Includes resolve relative to the invocation directory. Successive inputs share
compiler state. `push` and `pop` restore declarations, globals, rewrites, and
the e-graph. A failed complete REPL input restores both compiler and e-graph
state, including changes from earlier commands in that input.

The slotted flag cannot be combined with term or proof encoding.

## Rust API

Compile source with `Compiler` and evaluate its output with `new_egraph()`:

```rust
use egglog_experimental::slotted::{Compiler, new_egraph};

let mut compiler = Compiler::default();
let program = compiler.compile(None, r#"
    (datatype Expr (Lam Expr Expr :binder 0))
    (let id (Lam $a $a))
    (run 0)
    (check (= id (Lam $b $b)))
"#)?;
let mut egraph = new_egraph();
egraph.parse_and_run_program(None, &program)?;
# Ok::<(), Box<dyn std::error::Error>>(())
```

Reuse the compiler and e-graph together for successive inputs. A compilation
error leaves the compiler unchanged. Applications embedding the two APIs are
responsible for restoring both states if evaluation fails; the CLI implements
that rollback for REPL inputs.

## Declaring constructors and binders

```text
(datatype Expr
  (Lam Expr Expr :binder 0)
  (Let Expr Expr Expr :binder 1)
  (App Expr Expr)
  (Num i64))
```

The equivalent long form uses `(sort Expr)` followed by declarations such as
`(constructor Lam (Expr Expr) Expr :binder 0)`.

Every declared equality sort is a **carrier** for slotted terms. Programs may
have several carriers, including through `datatype*`, but a constructor's term
children must have the same carrier as its result. Cross-carrier edges are
rejected. A rewrite, its side patterns, and both sides of a union or equality
check must also use one carrier.

Every carrier accepts slot literals such as `$a` or `$a0` as terms, including
sorts with no user constructors. No variable declaration is needed. Slots take
their sort from context; `Var` is an ordinary name, not a built-in sort.

`:binder` lists the positions that bind slots, counting carrier columns and
skipping payload columns. Those positions must be distinct, contiguous, and
followed by the term child they cover. A binder has the same sort as the other
children but must be supplied a slot literal: compound terms, globals, and
pattern variables are rejected in binder positions. Multiple binder columns act
as nested binders around that one covered child; other children remain outside
their scope. For `Let` above, the initializer is outside the binder and the body
is inside it.

Payload columns currently support `i64` and `String`. Payloads carry no slots.
Container-valued constructor columns and extraction options such as `:cost`,
`:unextractable`, and `:internal-term-constructor` are unsupported. A bare slot
needs a constructor context to determine its carrier when several carriers exist.

## Slots, terms, and globals

Slot names may contain letters, digits, and underscores: `$a`, `$a0`, and
`$outer_var` are valid. A slot in a carrier column denotes a variable term; in a
binder column it declares a bound variable. Ground names persist across inputs,
subject to binder shadowing. Slot names in a rewrite are local to that rule.

Renaming a bound slot preserves alpha-equivalence:

```slotted
(datatype Expr (Lam Expr Expr :binder 0) (App Expr Expr))
(let id (Lam $a $a))
(let constant (Lam $a $a0))
(run 0)
(check (= id (Lam $renamed $renamed)))
(check (!= id constant))
(check (free-names-are constant $a0))
```

`let` binds a global to a constructed term. Globals are referenced by their bare
names; `$` always introduces a slot. A global name starting with `$` is rejected,
and a global cannot currently store a bare slot invocation such as `(let v $x)`.

```slotted
(datatype M (IConst) (Mul M M) (Lam M M :binder 0))

(let j (IConst))
(rewrite (Mul a j) a :name "id-right")

; `k` is a global and `$k` is a slot -- the two never read alike
(let k (IConst))
(rewrite (Lam $k (Mul k $k)) k :name "slot-not-global")

(let mj (Mul (IConst) (IConst)))
(let ek (Lam $bound (Mul (IConst) $bound)))
(run 5)

(check (= mj (IConst)))
(check (= ek (IConst)))
```

Nullary constructors require parentheses, as in `(IConst)`. A bare name in a
rewrite denotes a global if one is already bound; otherwise it denotes a pattern
variable. Pattern variables may also use egg's `?name` spelling: `x` and `?x`
denote the same pattern variable.

## Equations and rewrites

`(union a b)` asserts equality in the slots written by the terms. It can introduce
symmetries or remove dependence on a slot. For example, equating `F($a,$b)` with
`F($b,$a)` gives the class a swap symmetry; equating it with `F($b,$c)` makes
both slots redundant.

A rewrite asserts an equation for each match:

```text
(rewrite (Lam $x (App f $x)) f
         :name "eta"
         :when ((not-free $x f)))
```

The right-hand side may be a matched variable or a constructed term.
`:name` names the rule. Only the default user ruleset is supported; `:ruleset`
is rejected. Express a bidirectional rewrite as two `rewrite` commands.

### Side patterns and guards

`:when` takes one list containing all the facts. Multiple `:when` clauses and a
bare fact without the surrounding list are rejected.

The predicates below work in both `check` and rewrite `:when` clauses. Checks
use ground terms or globals; guards use matched pattern variables. Slot names in
guards refer to the rule's pattern slots.

| Predicate | Meaning |
| --- | --- |
| `(= a b)` | Equal terms, preserving their free-variable identities |
| `(!= a b)` | Different terms at the time of the query |
| `(renaming-= a b)` | Equal modulo a renaming of free variables |
| `(renaming-!= a b)` | Different even modulo renaming |
| `(free $x a b)` | `$x` occurs free in at least one listed term |
| `(not-free $x a b)` | `$x` occurs free in none of the listed terms |
| `(free-names-are a $x $y)` | `a` depends on exactly these free variables; no names means closed |

A guard may also introduce a constructor pattern with `(= v (Ctor ...))`, or
require a constructor term to exist with `(Ctor ...)`. Free-name predicates can
use constructor patterns as their term arguments too.

The four comparisons between bound pattern variables have the same meaning as
in `check`. Ordinary equality preserves free-slot identities and allows known
class symmetries; equality modulo renaming compares only the classes. For example:

```slotted
(datatype Expr (Pair Expr Expr) (Related Expr Expr))
(let pair (Pair $a $b))
(rewrite (Pair a b) (Related a b) :when ((renaming-= a b)))
(run 1)
(check (= pair (Related $a $b)))
(check (renaming-= $a $b))
(check (!= $a $b))
```

Replacing the rule's `renaming-=` with `=` would prevent this match. Repeating a
pattern variable, as in `(Pair a a)`, also requires the same invocation. Patterns
can be renamed consistently, but their shared variables retain these constraints.

Disequality is non-monotonic: terms that differ now may be unioned later, and a
previously admitted match is not withdrawn. Literal payloads and payload pattern
variables are supported. Computing payloads or calling payload primitives in a
rewrite is unsupported.

A rewrite's left side may be a constructor pattern or a variable bound by its
side patterns. An unbound left-hand variable is rejected:

```slotted
(datatype U (F U U) (G U) (N))
(let start (F (N) (N)))
(rewrite child (G child) :when ((= parent (F child other))))
(run 1)
(check (= (N) (G (N))))
```

Side patterns may nest, and their variables need not appear on the left:

```slotted
(sort U)
(constructor Null () U)
(constructor Succ (U) U)
(constructor Prev (U) U)

; fires only where x is at least three deep, and returns what is under the third Succ
(rewrite (Prev x) y :when ((= x (Succ (Succ (Succ y))))) :name "reach-in")

(let s3 (Prev (Succ (Succ (Succ (Null))))))
(let s2 (Prev (Succ (Succ (Null)))))
(run 10)

(check (= s3 (Null)))
(fail (check (= s2 (Null))))     ; two deep, so the condition fails and the rule does not fire
```

Sharing a pattern variable between patterns joins their matches. Here `m` joins
the load to the store, and `p` requires the same address:

```slotted
(sort U)
(constructor Num (i64) U)
(constructor Mem0 () U)
(constructor Store (U U U) U)
(constructor LoadFrom (U U) U)

; the value a store wrote, read back at the same address: `m` and `p` join the patterns
(rewrite (LoadFrom m p) v :when ((= m (Store m0 p v))) :name "load-after-store")

(let m1 (Store (Mem0) (Num 7) (Num 42)))
(let got (LoadFrom m1 (Num 7)))
(let other (LoadFrom m1 (Num 8)))
(run 4)

(check (= got (Num 42)))
(fail (check (= other (Num 42))))    ; a different address, so `p` does not join
```

Repeating a slot literal in independent binder columns does not equate their
bodies. Share a body pattern variable to require that relationship:

```slotted
(sort U)
(constructor Num (i64) U)
(constructor Lam (U U) U :binder 0)
(constructor Pair (U U) U)
(constructor Fired () U)

; `$x` twice relates the two lambdas not at all
(rewrite (Pair f g) (Fired) :when ((= f (Lam $x c))
                                   (= g (Lam $x d))) :name "inert")

(let unrelated (Pair (Lam $bound (Num 1)) (Lam $bound (Num 2))))
(run 4)

(check (= unrelated (Fired)))        ; fires, though the two lambdas are unrelated
```

Different slot literals in one rewrite are required to remain distinct. Thus
`(F $x $y)` does not match `F($a,$a)`. A slot appearing only on the right-hand
side is fresh; `:fresh $s` may state this explicitly but is not required.

When a rewrite places a matched term under a binder, it must guard against
capture if the term was matched outside that binder. For example:

```text
(rewrite (Pair (Lam $y body) e) (Lam $y (Pair body e))
         :when ((not-free $y e)))
```

Without this guard, a free variable of `e` may become bound. The shipped rule
libraries check for these capture guards.

**Known scope limitation.** Explicit slot occurrences are currently lowered into
one rule-global slot namespace. A pattern such as `(Let $x $x $x)` uses the same
spelling for a free initializer slot and a binder, which can cause a missed match.
Write `(Let $free $bound $bound)` to distinguish those roles. This limitation is
tracked in [issue #81](https://github.com/saulshanabrook/egglog-encoding/issues/81).

### Nested-matcher compatibility

`--slotted --slotted-no-aliasing` restricts matching to the reference nested
matcher's aliasing policy. It adds a disequality constraint over non-pattern
slots while preserving sharing already present in child edges. It requires one
nested left-hand pattern and rejects additional equality side patterns. Ground
checks retain their ordinary meaning.

## Running and checking

`(run N)` performs N rounds of user rewrites, with slotted maintenance saturated
around each round. Matching reads a snapshot before actions are applied.
`(run 0)` performs maintenance without applying user rewrites. `run-schedule` and
`run-report` are rejected because they could bypass the required maintenance.

Checks query the current graph without applying rewrites or adding terms:

```slotted
(sort U)
(constructor Lam (U U) U :binder 0)
(constructor Mult (U U) U)
(constructor Null () U)

(let k (Lam $bound $c))              ; lam $bound. $c -- returns $c, ignores its argument
(let id (Lam $bound $bound))             ; lam $bound. $bound
(let m (Mult $a (Null)))
(run 0)

(check (free-names-are k $c))             ; k depends on $c, and on nothing else
(check (free-names-are id))               ; the identity depends on no slot: its own is bound
(check (free $a m))                  ; m depends on this variable
(check (not-free $a k id))           ; neither function depends on it
(check (renaming-!= k m))        ; and they are not equal, under any renaming
```

Term equality respects free-variable identities; equality modulo renaming does
not. These constant functions return different free variables:

```slotted
(sort U)
(constructor Lam (U U) U :binder 0)
(let p (Lam $bound $c))
(let q (Lam $bound $d))
(run 0)
(check (renaming-= p q))   ; equal modulo a renaming: both are "a constant function"
(check (!= p q))           ; but not equal: one returns $c, the other $d
```

A symmetry can make different slot spellings denote equal terms:

```slotted
(sort U)
(constructor F (U U) U)
(rewrite (F x y) (F y x) :name "comm")
(let a (F $a $b))
(let b (F $b $a))
(run 5)
(check (= a b))
```

Within each carrier, all variable terms belong to one class. Consequently,
`renaming-=` between bare slots always holds, even when ordinary equality does not:

```slotted
(sort U)
(constructor F (U U) U)
(let a (F $a $b))                 ; something for the graph to hold
(run 0)
(check (renaming-= $c $d))        ; holds -- both are the variable class
(check (!= $c $d))                ; also holds -- they are different variables
```

Use `(fail (check ...))` to assert that a check fails. Write each slotted
assertion in its own `check`. The adjacent [encoding description](ENCODING.md)
explains the internal tables and invariants.

## Extraction

`(extract term)` currently extracts an encoded term through the class leader:

```slotted
(sort U)
(constructor Lam (U U) U :binder 0)
(let p (Lam $bound $c))
(let q (Lam $bound $d))
(run 0)
(extract q)      ; q's node is canonicalised away, so this extracts through the leader
```

The output contains renamings and binder-marker children and uses the leader's
slot frame, which may differ from the requested term's frame. Its cost is egglog's
encoded-tree cost. There is no conversion
back to slotted source syntax yet. This command is useful for inspecting a class;
source-level extraction remains unsupported. Benchmark goals check target
membership independently of extraction.

## Examples and validation

Every complete `slotted` code block in this guide runs in `cargo test`, along
with the Rust API doctest and the regression programs under `tests/slotted/`.
Shared rule libraries are in `tests/slotted/languages/`; case studies are in
`benches/slotted/`. A small representative set of fixtures also snapshots the
compiler output. Reference comparisons and paper evaluation tools live in the
workspace's `slotted/` directory.
