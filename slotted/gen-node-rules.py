#!/usr/bin/env python3
"""Write the arity-dependent half of the slotted machinery.

Every rule that pattern-matches an e-node has to name each column, so it cannot be
written once for all shapes in egglog. It *can* be written once, and it is:
`slotted/slotted-encoder.py` holds the emitter, and this picks what to
emit and where it goes.

Two kinds of output. `GENERIC` is the string-headed encoding in
`target/slotted/slotted-node-rules.egg`, where the operator is a payload column so any
operator can be written without regenerating. Each `slotted/languages/*.egg`
gets a per-language encoding with one constructor per operator, the shape the
reference crate's `define_language!` produces. Both include
`enc.prelude()` and `enc.multi_sort_core()`, the same two the compiler emits, so a
generated file carries its whole machinery and includes nothing.

Add a constructor to `GENERIC` below, or a language file, and re-run. Do not
edit the output.

    python3 slotted/gen-node-rules.py
"""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
enc = __import__("slotted-encoder")

CHILD, BINDER = enc.CHILD, enc.BINDER
SYMBOLS = enc.carrier_symbols((enc.CARRIER_SORT,))
read_language = enc.read_language

# The generic, string-headed encoding, and the file it is written to. One constructor
# per arity with the operator in a payload column, so any operator can be written
# without regenerating anything. The compiler does not know this family: to it these
# are constructors like any others, and a payload column is a payload column.
GENERIC = {
    # The nullary leaf. The hand-written core used to declare it; the generated
    # machinery stands alone, so it declares its own.
    "Null": [],
    "App2": ["String", CHILD, CHILD],
    "App3": ["String", CHILD, CHILD, CHILD],
    "App4": ["String", CHILD, CHILD, CHILD, CHILD],
    "Num": ["i64"],
    "Sym": ["String"],
    "Scale": ["i64", CHILD],  # keeps the mixed payload/child case exercised
}
GENERIC_FILE = "target/slotted/slotted-node-rules.egg"

# Here the operator is in a payload rather than the constructor, so a binder cannot be
# declared structurally -- `App2` is not a binder, `App2 "lambda"` is. `emit` takes the
# pairs and pins them by head string.
GENERIC_BINDERS = (("lambda", "App2"), ("let", "App3"))


def machinery():
    """The carrier-independent prelude and the one carrier these files encode over."""
    return enc.prelude() + "\n\n" + enc.multi_sort_core(SYMBOLS)


def emit(spec, binders=()):
    """This file's constructors, over the single carrier the generated files declare."""
    return enc.emit(spec, sort=enc.CARRIER_SORT, symbols=SYMBOLS[enc.CARRIER_SORT], binders=binders)


def string_headed(head, ctor, ref=None):
    """The `Op` for one operator of this family, for a term language over it.

    A binder is not structural here, so `GENERIC_BINDERS` pins it by head string, and
    reading that same table is what keeps a term language from disagreeing with the
    rules this file emits.
    """
    sig = list(GENERIC[ctor])
    if (head, ctor) in GENERIC_BINDERS:
        sig[next(i for i, c in enumerate(sig) if c in enc.SLOTTED)] = BINDER
    return enc.Op(head, ctor, sig, pays=[f'"{head}"'], ref=head if ref is None else ref)


# Per-language encodings: one constructor per operator, the shape the reference crate's
# `define_language!` produces, with no head to indirect through.
#
# A language's constructors are declared WHERE ITS RULES ARE where it has rules, so
# there is one place for them: `sdql` is declared at the top of its slotted source, and
# only the neutral language the fuzzer generates terms in, which has no rules at all,
# still has a file to itself.
LANG_DIR = pathlib.Path("slotted/languages")
SOURCES = {
    "sdql": pathlib.Path("slotted/languages/sdql.egg"),
    "array": pathlib.Path("slotted/languages/array.egg"),
    "toy": LANG_DIR / "toy.egg",
}

LANGUAGES = {name: read_language(p) for name, p in SOURCES.items()}


def main():
    generic = pathlib.Path(GENERIC_FILE)
    generic.parent.mkdir(parents=True, exist_ok=True)
    generic.write_text(
        enc.in_slotted_ruleset(
            enc.MACHINERY_HEADER + ";;;\n;;; The generic, string-headed encoding: one constructor per"
            " arity, the operator in a\n;;; payload column.\n\n"
            + machinery()
            + "\n\n"
            + "\n".join(emit(GENERIC, GENERIC_BINDERS))
        )
    )
    print(f"wrote {generic} ({len(GENERIC)} constructors, string-headed)")

    # A language file carries its own machinery rather than the generic string-headed
    # encoding: none of them uses an `App<n>`, so including it would declare a whole
    # constructor family none of their rules can name.
    for lang, spec in LANGUAGES.items():
        p = pathlib.Path(f"target/slotted/slotted-lang-{lang}.egg")
        body = enc.MACHINERY_HEADER + f";;;\n;;; Language: {lang}\n\n" + machinery() + "\n\n" + "\n".join(emit(spec))
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(enc.in_slotted_ruleset(body))
        print(f"wrote {p} ({len(spec)} constructors, one per operator)")


if __name__ == "__main__":
    main()
