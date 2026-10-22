# The slotted language

`egglog-experimental --slotted` compiles programs with slots and binders to
ordinary egglog tables and rules, then evaluates them through the normal CLI.
A slotted term denotes an e-class together with a renaming of its free slots.
Two terms can therefore belong to the same class without denoting the same
variables.

```bash
cargo build -p egglog-experimental
target/debug/egglog-experimental --slotted slotted/tests/paper/figure-3.egg
target/debug/egglog-experimental --slotted --mode desugar slotted/tests/paper/figure-3.egg
```

File arguments, stdin, serialization, and timing reports use the normal CLI.
Includes resolve relative to the invocation directory. Successive inputs share
compiler state. `push` and `pop` restore declarations, globals, rewrites, and
the e-graph. A failed complete REPL input restores both compiler and e-graph
state, including changes from earlier commands in that input.

The slotted flag cannot be combined with term or proof encoding. Use
`--slotted-encoded` to evaluate code that has already been lowered.

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

Every carrier accepts slot literals such as `$a` or `$0` as terms, including
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

Numbered ground slots are signed 64-bit integers: `$01` and `$+1` mean `$1`,
and `$-0` means `$0`. Named and numbered slots are distinct. Source spellings
do not affect alpha-equivalence:

```slotted
(datatype Expr (Lam Expr Expr :binder 0) (App Expr Expr))
(let id (Lam $a $a))
(let constant (Lam $a $a0))
(run 0)
(check (= id (Lam $renamed $renamed)))
(check (!= id constant))
(check (slots constant $a0))
```

`let` binds a global to a constructed term. Globals are referenced by their bare
names; `$` always introduces a slot. A global name starting with `$` is rejected,
and a global cannot currently store a bare slot invocation such as `(let v $7)`.

```slotted
(datatype M (IConst) (Mul M M) (Lam M M :binder 0))

(let j (IConst))
(rewrite (Mul a j) a :name "id-right")

; `k` is a global and `$k` is a slot -- the two never read alike
(let k (IConst))
(rewrite (Lam $k (Mul k $k)) k :name "slot-not-global")

(let mj (Mul (IConst) (IConst)))
(let ek (Lam $0 (Mul (IConst) $0)))
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
symmetries or remove dependence on a slot. For example, equating `F($0,$1)` with
`F($1,$0)` gives the class a swap symmetry; equating it with `F($1,$2)` makes
both slots redundant.

A rewrite asserts an equation for each match:

```text
(rewrite (Lam $x (App f $x)) f
         :name "eta"
         :when ((not-free $x f)))
(rewrite (Let t $x body) (subst body $x t) :name "beta")
```

The right-hand side may be a matched variable, a constructed term, or `subst`.
`:name` names the rule. Only the default user ruleset is supported; `:ruleset`
is rejected. Express a bidirectional rewrite as two `rewrite` commands.

### Side patterns and guards

`:when` takes one list containing all the facts. Multiple `:when` clauses and a
bare fact without the surrounding list are rejected.

| Fact | Meaning |
| --- | --- |
| `(free $x a b)` | `$x` occurs among the free slots of at least one listed term |
| `(not-free $x a b)` | `$x` occurs in none of the listed terms |
| `(= v (Ctor ...))` | An additional constructor pattern rooted at `v` |
| `(= a b)` | Identify two matched terms |
| `(Ctor ...)` | Require a matching constructor term |
| `(!= a b)` | Require different invocations at match time |

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

(let unrelated (Pair (Lam $0 (Num 1)) (Lam $0 (Num 2))))
(run 4)

(check (= unrelated (Fired)))        ; fires, though the two lambdas are unrelated
```

Different slot literals in one rewrite are required to remain distinct. Thus
`(F $x $y)` does not match `F($0,$0)`. A slot appearing only on the right-hand
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

### Substitution

`(subst body $x t)` performs capture-avoiding substitution for `$x` in one
smallest source term extracted from `body`'s class, then adds the result. Ties
use a deterministic canonical spelling from the rewrite round's snapshot.
Binder markers do not contribute to source-tree cost. A binder for `$x` shadows
the substitution in its covered child; conflicting private binders are refreshed
to avoid capturing free slots of `t`.

### Nested-matcher compatibility

`--slotted --slotted-no-aliasing` restricts matching to the reference nested
matcher's aliasing policy. It adds a disequality constraint over non-pattern
slots while preserving sharing already present in child edges. It requires one
nested left-hand pattern and rejects additional equality side patterns. Ground
checks retain their ordinary meaning. Substitution still uses the same
deterministic snapshot policy as the default encoding.

## Running and checking

`(run N)` performs N rounds of user rewrites, with slotted maintenance saturated
around each round. Matching reads a snapshot before actions are applied.
`(run 0)` performs maintenance without applying user rewrites. `run-schedule` and
`run-report` are rejected because they could bypass the required maintenance.

The following claims are accepted in `check`:

| Claim | Meaning |
| --- | --- |
| `(= a b)` | Equal terms in the slots written by the source |
| `(!= a b)` | Different terms in those slots |
| `(renaming-= a b)` | Equal modulo some renaming of free slots |
| `(renaming-!= a b)` | Different even modulo renaming |
| `(slots a $x $y)` | The class depends on exactly these slots; no arguments means closed |
| `(holds a Ctor)` | The class contains a node of this constructor |
| `(not-holds a Ctor)` | The class contains no node of this constructor |

```slotted
(sort U)
(constructor Lam (U U) U :binder 0)
(constructor Mult (U U) U)
(constructor Null () U)

(let k (Lam $0 $3))              ; lam $0. $3 -- returns $3, ignores its argument
(let id (Lam $0 $0))             ; lam $0. $0
(let m (Mult $1 (Null)))
(run 0)

(check (slots k $3))             ; k depends on $3, and on nothing else
(check (slots id))               ; the identity depends on no slot: its own is bound
(check (holds m Mult))           ; m's class contains a Mult node
(check (not-holds k Mult))       ; k's class does not
(check (renaming-!= k m))        ; and they are not equal, under any renaming
```

Term equality respects free-variable identities; equality modulo renaming does
not. These constant functions return different free variables:

```slotted
(sort U)
(constructor Lam (U U) U :binder 0)
(let p (Lam $0 $3))
(let q (Lam $0 $4))
(run 0)
(check (renaming-= p q))   ; equal modulo a renaming: both are "a constant function"
(check (!= p q))           ; but not equal: one returns $3, the other $4
```

A symmetry can make different slot spellings denote equal terms:

```slotted
(sort U)
(constructor F (U U) U)
(rewrite (F x y) (F y x) :name "comm")
(let a (F $1 $2))
(let b (F $2 $1))
(run 5)
(check (= a b))
```

Within each carrier, all variable terms belong to one class. Consequently,
`renaming-=` between bare slots always holds, even when ordinary equality does not:

```slotted
(sort U)
(constructor F (U U) U)
(let a (F $1 $2))                 ; something for the graph to hold
(run 0)
(check (renaming-= $3 $4))        ; holds -- both are the variable class
(check (!= $3 $4))                ; also holds -- they are different variables
```

Use `(fail (check ...))` to assert that a check fails. Unrecognized check facts
and commands are passed to egglog and operate on the encoded representation;
they are not automatically given slotted semantics. Use `--mode desugar` to
inspect that representation. The adjacent `ENCODING.md` explains its tables,
invariants, and reference-comparison requirements.

## Extraction

`(extract term)` currently extracts an encoded term through the class leader:

```slotted
(sort U)
(constructor Lam (U U) U :binder 0)
(let p (Lam $0 $3))
(let q (Lam $0 $4))
(run 0)
(extract q)      ; q's node is canonicalised away, so this extracts through the leader
```

The output contains renamings and binder-marker children and uses the leader's
slot frame, which may differ from the requested term's frame. Its cost is egglog's
encoded-tree cost, not the source-tree cost used by `subst`. There is no conversion
back to slotted source syntax yet. This command is useful for inspecting a class;
source-level extraction remains unsupported. Benchmark goals check target
membership independently of extraction.

## Graph export

`(slotted-export "graph.json")` writes the logical slotted e-graph after the
preceding commands. Run `(run 0)` first to settle maintenance without applying
user rewrites. Export does not run additional rules. For example:

```slotted
(sort U)
(constructor Lam (U U) U :binder 0)
(let identity (Lam $x $x))
(run 0)
(slotted-export "/tmp/slotted-language-example.json")
```

The document uses `egraph-serialize` with slot and symmetry annotations and a
`counts` field. It preserves all live constructor rows and reads native tables
without the visualization limits of `--to-json`. It rejects inconsistent frames,
edges, or groups. Rust callers can use [`export::export`] on an `egglog::EGraph`;
[`export::export_named`] also supports explicit operator correspondences for a
single untyped reference language. This graph export does not extract a source term.

## Examples and validation

Every complete `slotted` code block in this guide runs through the Rust CLI in
`make slotted-check`; the Rust API example above is a doctest in `make check`.
Regression programs live under `slotted/tests/`, shared languages under
`slotted/languages/`, and evaluation inputs and generators under
`slotted/benchmarks/`. Compiler output is also checked with `insta` snapshots.
