# The slotted language

What `slotted/slotted-egglog.py` accepts, and how it differs from egglog.

A file here is an egglog program with a few additions. Run one directly:

```
python3 slotted/slotted-egglog.py slotted/tests/paper/figure-3.egg
python3 slotted/slotted-egglog.py slotted/tests/paper/figure-3.egg --desugar   # see the egglog
```

The additions exist because a slotted term is not an egglog value. A term denotes a
class **together with** a renaming — an *invocation* — and egglog has no notion of
that. Everything below is either a way to write such a term, or a way to ask a question
about one. **Every other egglog command means what it always meant** and is passed
through untouched: `push`, `pop`, `print-size`, `print-function`, `query-extract`, and
whatever egglog gains next.

---

## Declaring a language

```
(constructor Lam (U U) U :binder 0)
(constructor Let (U U U) U :binder 1)
(constructor App (U U) U)
(constructor Num (i64) U)
```

A `U` column is a slotted child. Any other column is a payload and carries no slots.
`:binder` names the child positions whose slot the node binds, counting over the `U`
columns only — so `Lam` binds the slot in its first child, and `Let` binds the slot in
its second.

A binder covers the column *after* the one it binds, which is what wrapping a single
child in `Bind` means. So `Let`'s bound slot is stripped from its third column and not
from its first: `let x = x in f x` keeps the value's occurrence free.

There is no `(datatype …)`; a constructor is declared one per line, and the file needs
no include — the compiler emits the machinery for exactly the constructors declared.

## Writing terms

```
(let id (Lam $0 $0))                    ; lam $0. $0
(let k  (Lam $0 $3))                    ; lam $0. $3, which keeps $3 free
(let t  (App (Num 0) $7))
```

`$n` is a slot. In a binder column it **is** the bound slot; anywhere else it is an
occurrence of that slot. Writing `$0` twice in one term means the same slot twice.

## Asserting an equation

```
(union a b)
```

Egglog's `union` equates two values. This one equates two *terms*, which is a different
and stronger thing: it is how a class acquires a symmetry, and how a slot becomes
redundant. Unioning `f($0,$1)` with `f($1,$0)` gives that class the swap; unioning
`f($0,$1)` with `f($1,$2)` leaves the class with no slots at all, because it cannot
depend on any of them.

## Rules

```
(rewrite (Lam $x (App ?f $x)) ?f
         :name eta
         :when (not-free $x ?f))

(rewrite (Sum ?e1 $k $v (Sing $k $v)) ?e1)

(rewrite (Let ?t $x ?body) (subst ?body $x ?t) :name beta)
```

`?x` is a pattern variable standing for a subterm; `$x` is a slot literal the match
solves for. `:when (free $x ?f)` and `:when (not-free $x ?f)` are side conditions on
whether a slot is among a variable's free slots — the reference's
`subst[v].slots().contains(…)`.

`:fresh $s` names a slot the right-hand side binds that the pattern never mentions, so
the compiler mints one. `:name` names the rule.

`subst` is the one right-hand-side head that is not a constructor. `(subst ?body $x ?t)`
is `?body[(var $x) := ?t]` — the reference's `b[x := t]`. It is a *call*, so there is
nothing to build; `slotted/tests/sdql-beta.egg` explains what the compiler emits for it.

## Running

```
(run 3)
```

Three user-rule steps, with the machinery saturated around each. Saturating between
steps is not optional: the invariants have to hold before the next user rule looks at
the graph.

## Asking questions

Egglog's `check` asks about values. These ask about terms.

| claim | means |
| --- | --- |
| `(renaming-= a b)` | `a` and `b` are **equal** — the same term, once renamings are taken into account |
| `(renaming-!= a b)` | they are not |
| `(eclass-= a b)` | `a` and `b` are in one **e-class**, but not necessarily at the same slots |
| `(eclass-!= a b)` | they are not |
| `(slots a $5 $6)` | `a`'s class depends on exactly these slots (`(slots a)` means none) |
| `(holds a Mult)` | `a`'s class contains a `Mult` node |
| `(not-holds a Mult)` | it does not |

### Why two kinds of equality

Because a term is a class *and* a renaming, and the two questions come apart. Take two
alpha-variants whose free slot is renamed:

```
(let p (Lam $0 $3))
(let q (Lam $0 $4))
(check (eclass-= p q))        ; one class: both are "a constant function"
(check (renaming-!= p q))     ; not equal: one returns $3, the other $4
```

`eclass-=` holds and `renaming-=` does not. The e-class is the same shape; the terms are
not the same term.

The other direction matters too. `renaming-=` is not "syntactically identical" — it is
equality *modulo* everything the e-graph knows, including a class's symmetries. If
commutativity has put the swap in `f`'s group, then

```
(check (renaming-= (F $1 $2) (F $2 $1)))
```

holds, because by Def. 6 two invocations of a class agree when the renaming between
them lies in that group.

The case that pins the distinction down is the reference's own
`fgh::transitive_symmetry` — see `slotted/tests/paper/fgh-transitive-symmetry.egg`.
After `f($1,$2) = g($2,$1)` and `g($1,$2) = h($1,$2)`, the terms `f($1,$2)` and
`h($1,$2)` are in one class but differ by the swap, so they are `eclass-=` and
`renaming-!=`, while `f($1,$2)` and `h($2,$1)` are `renaming-=`.

### Dropping to the encoded level

A `check` whose claim is none of the above is passed through to egglog, so a test can
ask about the encoding itself without leaving the language:

```
(check (RenamesToLeader a m l))
```

`(RenamesToLeader f m l)` is `f = m*l`, with `m` carrying `l`'s slots to `f`'s. That
relation is what `renaming-=` and `eclass-=` are defined in terms of: `renaming-=` asks
for **one** renaming reaching both terms from the leader, `eclass-=` lets each have its
own.

## Extraction and printing

`(extract a)` encodes its argument and hands it to egglog, so what you see is the node
as the encoding **stores** it — renamings spelled out:

```
(extract a)     (F (map-of 0 2) (Var 0) (map-of 0 1) (Var 0))
```

That is `f($2,$1)`. There is no pretty-printer back to slotted syntax yet.

## What `ok` tells you

A run reports what it did, because "ok" means different things for different files:

```
ok   figure-3.egg   4 terms, 1 union, 3 claims
ok   array.egg      8 rules, nothing asked -- a rule library, included by other files
```

The second has no terms and no claims, so nothing was checked — it only loaded.

## Files

| path | what it is |
| --- | --- |
| `slotted/tests/` | programs in this language, run by `slotted/run-slotted-tests.py` |
| `slotted/tests/paper/` | one file per test in the reference's own suites |
| `slotted/encoding/` | the encoding itself, written by hand at the encoded level, plus the tutorial that explains it |
| `slotted/slotted-egglog.py` | the compiler; its module docstring is the short form of this file |
| `slotted-user-rules.md` | how a rule is compiled, and why each piece is there |
