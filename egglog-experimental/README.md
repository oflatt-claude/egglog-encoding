# egglog-experimental

This repo implements several experimental extensions to the core [`egglog`](https://github.com/egraphs-good/egglog).
Currently, this can be thought of as a standard library to `egglog`.

You can use the egglog [Zulip](https://egraphs.zulipchat.com/#narrow/stream/375765-egglog) to ask questions and suggest improvements to this repo.

## Trying it out

The easiest way to try out `egglog-experimental` is to use the [web demo](https://egraphs-good.github.io/egglog-demo), which builds on top of latest egglog-experimental.

To install egglog-experimental binary locally, you need to install `cargo` and run

```
git clone git@github.com:egraphs-good/egglog-experimental.git
cargo install --path=egglog-experimental
```

To use it in a Rust project, you can add it as a dependency in a `Cargo.toml` file.

```
egglog-experimental = "3.0"
```

## Documentation

Check out the crate documentation (built locally) for the current list of implemented extensions, API details, and demo links.
Releases are coordinated with compatible releases of egglog.

## Constructor injectivity

Mark a constructor with `:injective` to infer equal arguments when two of its
results are equal. Schedule the shared `injectivity` ruleset explicitly:

```lisp
(datatype Term (Leaf String))
(constructor Wrap (Term) Term :injective)
(union (Wrap (Leaf "a")) (Wrap (Leaf "b")))
(run-schedule (saturate injectivity))
(check (= (Leaf "a") (Leaf "b")))
```

Datatype variants also accept the annotation, for example
`(datatype Term (Leaf String) (Wrap Term :injective))`. It combines with
`:cost` and `:unextractable`. Equality-sort arguments are unioned; differing
primitive arguments trigger a panic when the ruleset runs. Container arguments
are currently rejected at declaration. Injectivity applies within each marked
constructor and does not require different constructors to have different
results. The generated rules support term encoding and proof testing.

Executable examples cover [mixed arguments](tests/injectivity/injectivity-basic.egg),
[recursive propagation](tests/injectivity/injectivity-recursive.egg), and
[mutually recursive datatypes](tests/injectivity/injectivity-datatypes.egg).
