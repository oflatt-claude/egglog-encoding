#!/usr/bin/env python3
"""Write the arity-dependent half of the slotted machinery.

Every rule that pattern-matches an e-node has to name each column, so it cannot be
written once for all shapes in egglog. It *can* be written once, and it is:
`slotted/slotted-encoder.py` holds the emitter, and this picks what to
emit and where it goes.

Two kinds of output. `GENERIC` is the string-headed encoding in
`slotted-tests/generated/slotted-node-rules.egg`, where the operator is a payload column so any
operator can be written without regenerating. Each `slotted/languages/*.egg`
gets a per-language encoding with one constructor per operator, the shape the
reference crate's `define_language!` produces. Both include
`slotted-tests/slotted-egraph-encoding-11.egg`, which is hand-written and holds the
constructor-independent half -- the sorts, the union-find rules, `Var` normalisation --
plus the ONE constructor family it works through as a worked example.

That family is arity 2, and `HANDWRITTEN` names it: its rules are hand-written there
rather than emitted here, so a reader gets a whole constructor's machinery in one
file. `slotted-encoder.handwritten_region()` returns what would be emitted for it, and
`slotted/check-handwritten-encoding.py` asserts the two agree, so the
worked example cannot drift away from what every other arity gets.

Add a constructor to `GENERIC` in the encoder, or a language file, and re-run. Do not
edit the output.

    python3 slotted/gen-node-rules.py
"""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
enc = __import__("slotted-encoder")

# Re-exported: `check-handwritten-encoding.py` loads this module by path and asks it
# for `HANDWRITTEN` and `handwritten_region()`.
CHILD, BINDER = enc.CHILD, enc.BINDER
GENERIC, GENERIC_BINDERS, HANDWRITTEN = enc.GENERIC, enc.GENERIC_BINDERS, enc.HANDWRITTEN
CORE = enc.CORE
MACHINERY, GENERIC_FILE = enc.MACHINERY, enc.GENERIC_FILE
read_language, emit = enc.read_language, enc.emit
handwritten_region = enc.handwritten_region

# Per-language encodings: one constructor per operator, the shape the reference crate's
# `define_language!` produces, with no head to indirect through.
#
# A language's constructors are declared WHERE ITS RULES ARE where it has rules, so
# there is one place for them: `sdql` is declared at the top of its slotted source, and
# only the neutral language the fuzzer generates terms in, which has no rules at all,
# still has a file to itself.
LANG_DIR = pathlib.Path("slotted/languages")
SOURCES = {
    "sdql": pathlib.Path("slotted-tests/sdql.egg"),
    "array": pathlib.Path("slotted-tests/array.egg"),
    "toy": LANG_DIR / "toy.egg",
}

LANGUAGES = {name: read_language(p) for name, p in SOURCES.items()}


def main():
    generic = pathlib.Path(GENERIC_FILE)
    generic.write_text(
        enc.in_slotted_ruleset(
            enc.MACHINERY_HEADER + ";;;\n;;; The generic, string-headed encoding: one constructor per"
            " arity, the operator in a\n;;; payload column. Arity 2 is hand-written in the"
            " file included below.\n\n"
            f'(include "{MACHINERY}")\n\n' + "\n".join(emit(GENERIC, GENERIC_BINDERS, omit=HANDWRITTEN))
        )
    )
    print(f"wrote {generic} ({len(GENERIC)} constructors, string-headed)")

    # A language file includes the hand-written half DIRECTLY, not the generic
    # encoding: none of them uses a string-headed `App<n>`, so including it would
    # declare a whole constructor family none of their rules can name. `CORE` is what
    # the hand-written half does provide -- `Var` and `Null` -- so a language may
    # still declare those for the record.
    for lang, spec in LANGUAGES.items():
        p = pathlib.Path(f"slotted-tests/generated/slotted-lang-{lang}.egg")
        body = (
            enc.MACHINERY_HEADER + f";;;\n;;; Language: {lang}\n\n"
            f'(include "{MACHINERY}")\n\n' + "\n".join(emit(spec, provided=CORE))
        )
        p.write_text(enc.in_slotted_ruleset(body))
        print(f"wrote {p} ({len(spec)} constructors, one per operator)")


if __name__ == "__main__":
    main()
