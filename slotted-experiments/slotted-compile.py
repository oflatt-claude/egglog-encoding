#!/usr/bin/env python3
"""Compile a test written in the SLOTTED language down to plain egglog.

A slotted test declares its own constructors at the top and then talks about terms,
rules and classes -- never about renamings, edges or `(Var 0)`. This turns that into a
self-contained egglog program: the hand-written core, the machinery for exactly the
constructors declared, and the compiled body. The output includes no generated file,
so there is no build artifact on the path between a test and running it.

THE LANGUAGE

    (constructor Sum (U U U U) U :binder 1 2)   the language, inline. A `U` column is
                                                a slotted child; `:binder` names the
                                                child positions whose slot it binds.

    (let r (Sing Null Null))                    name a term
    (let a (Sum r $5 $6 Null))                  a `$n` in a binder column is the bound
                                                slot; in any other child column it is
                                                a variable occurrence

    (rewrite (Sum ?e1 $k $v (Sing $k $v)) ?e1)  a rule, in terms
    (rewrite lhs rhs :when (not-free $x ?f))    ... with a slot side condition

    (run 3)                                     three user-rule steps, with the
                                                machinery saturated around each

    (check (same a b))                          a and b are ONE slotted class
    (check (not-same a b))                      and are not
    (check (slots a $5 $6))                     a's class depends on exactly these

    (push) (pop)                                scope terms, as in egglog

`same` is the point of the whole exercise: two values are one slotted class when they
reach a common leader, which is not egglog equality -- classes equal up to a renaming
stay distinct values. Writing `(= a b)` would test the wrong thing, so it is not
offered.

Usage:
    ./slotted-compile.py SRC.egg              write the compiled program to stdout
    ./slotted-compile.py SRC.egg -o OUT.egg   ... or to a file
    ./slotted-compile.py SRC.egg --run        compile to a temp file and run egglog
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "slotted-experiments"))
enc = __import__("slotted-encoder")

CORE_FILE = "slotted-tests/slotted-egraph-encoding-11.egg"
TOKEN = re.compile(r'\(|\)|"[^"]*"|;[^\n]*|[^\s()]+')
SLOT = re.compile(r"\$\w+\Z")


def parse(text):
    """Every top-level form, as nested lists of tokens. Comments are dropped."""
    toks = [t for t in TOKEN.findall(text) if not t.startswith(";")]
    pos, out = [0], []

    def go():
        t = toks[pos[0]]
        pos[0] += 1
        if t != "(":
            return t
        form = []
        while toks[pos[0]] != ")":
            form.append(go())
        pos[0] += 1
        return form

    while pos[0] < len(toks):
        out.append(go())
    return out


class Terms(enc.TermLang):
    """The test's language, plus the names its `let`s bind.

    A name stands for a term already built, so it writes as `$name` -- but its parent
    still needs the SLOTS to put in the edge, which is why a bound name cannot be an
    opaque value here.
    """

    def __init__(self, ops):
        super().__init__(ops)
        self.bound = {}

    def slots(self, t):
        return self.slots(self.bound[t[1]]) if t[0] == "name" else super().slots(t)

    def enc(self, t):
        return f"${t[1]}" if t[0] == "name" else super().enc(t)


class Source:
    """One slotted test: its language, and its body in order."""

    def __init__(self, path):
        self.path = path
        # repo-relative, so a snapshot does not carry the checkout it was built in
        self.relpath = path.resolve().relative_to(ROOT).as_posix()
        self.spec = {}
        self.body = []
        for form in parse(path.read_text()):
            if isinstance(form, list) and form and form[0] == "constructor":
                self.spec.update(enc.read_language_form(form))
            else:
                self.body.append(form)
        assert self.spec, f"{path.name}: no (constructor ...) declaration"
        self.lang = Terms({c: enc.Op(c, c, sig) for c, sig in self.spec.items()})

    # ------------------------------------------------------------------ terms
    def term(self, form, column=enc.CHILD, ground=True):
        """A slotted term as the encoder's tuple form.

        A `$s` means different things in the two settings, and the difference is real
        rather than a spelling. In a GROUND term it is a particular slot -- an integer
        the encoding writes into a renaming -- and in a binder column it IS the bound
        slot, while anywhere else it is a variable occurrence. In a PATTERN it is a
        slot LITERAL, a name the match has to solve for, which the encoder takes as the
        `$s` string in either column.
        """
        if isinstance(form, str):
            if SLOT.match(form):
                if not ground:
                    return form
                slot = int(form[1:]) if form[1:].isdigit() else form[1:]
                return slot if column is enc.BINDER else ("var", slot)
            if form in self.spec:  # a nullary constructor, written bare
                return (form,)
            if form.startswith("?"):
                return form
            assert form in self.lang.bound, f"{self.path.name}: {form!r} is not bound"
            return ("name", form)
        head, args = form[0], form[1:]
        assert head in self.spec, f"{self.path.name}: unknown constructor {head!r}"
        kinds = self.lang[head].arg_kinds()
        assert len(args) == len(kinds), f"{self.path.name}: {head} takes {len(kinds)} arguments, given {len(args)}"
        return (
            head,
            *(self.term(a, k, ground) if k in enc.SLOTTED else a for a, k in zip(args, kinds, strict=True)),
        )

    def encode(self, form, column=enc.CHILD):
        """A ground term as the egglog expression for its value."""
        t = self.term(form, column)
        return "(Var 0)" if t[0] == "var" else self.lang.enc(t)


def compile_source(src):
    out = [
        f";;; COMPILED from {src.relpath} by slotted-experiments/slotted-compile.py.",
        ";;;",
        ";;; A SNAPSHOT: committed so a change in the compiler shows up as a diff, never",
        ";;; edited by hand, and rewritten by `check-slotted.py --update`. This is what",
        ";;; running that test runs, and the only file it includes is the hand-written core.",
        "",
        f'(include "{CORE_FILE}")',
        "",
        enc.in_slotted_ruleset("\n".join(enc.emit(src.spec, provided=enc.CORE))),
    ]
    rules = 0
    for form in src.body:
        head = form[0] if isinstance(form, list) else form
        if head in ("push", "pop"):
            out.append(f"({head})")
        elif head == "let":
            _, name, body = form
            out.append(f"(let ${name} {src.encode(body)})")
            src.lang.bound[name] = src.term(body)
        elif head == "rewrite":
            out.append(compile_rewrite(src, form))
            rules += 1
        elif head == "run":
            out.append(schedule(int(form[1]), rules))
        elif head in ("check", "fail"):
            out.append(compile_check(src, form))
        else:
            raise SystemExit(f"{src.path.name}: cannot compile {head!r}")
    return "\n".join(out) + "\n"


def schedule(steps, rules):
    """The phased schedule: the machinery saturated around each user-rule step.

    With no rules there is nothing to interleave, so one saturation is the whole run.
    """
    if not rules or steps == 0:
        return "(run-schedule (saturate (run slotted)))"
    return (
        f"(run-schedule (saturate (run slotted))\n              (repeat {steps} (seq (run) (saturate (run slotted)))))"
    )


def compile_rewrite(src, form):
    """`(rewrite lhs rhs [:when (cond ...)] [:lead N])` through the encoder's recipe.

    `:lead` names the atom the query starts from, counting over the flattened pattern.
    It defaults to 0 -- the pattern's outermost node -- which is what every shipped
    generator pins, so a rule compiled here is the same text as the committed generated
    one. The answer may not depend on the lead, and a test can say another to check
    that: leading anywhere below the root makes the atoms above it come out
    child-before-parent, which is the fresh-root case.
    """
    _, lhs, rhs, *rest = form
    conds, lead = [], 0
    while rest:
        if rest[0] == ":lead":
            lead = int(rest[1])
        elif rest[0] == ":when":
            want, slot, *pvars = rest[1]
            assert want in ("free", "not-free"), f"unknown condition {want!r}"
            conds.append((want == "free", slot, [p.lstrip("?") for p in pvars]))
        else:
            raise SystemExit(f"{src.path.name}: expected :when or :lead, got {rest[0]!r}")
        rest = rest[2:]
    root, atoms = enc.flatten(src.lang, src.term(lhs, ground=False))
    order = enc.connected_order(src.lang, atoms, first=lead)
    return enc.compile_rule(
        src.lang, order, ("build", root, enc.rhs_of(src.lang, src.term(rhs, ground=False))), conds=conds
    )


def compile_check(src, form):
    """A claim about slotted classes, not about egglog values."""
    negated = form[0] == "fail"
    if negated:
        assert form[1][0] == "check", f"{src.path.name}: fail takes a check"
        form = form[1]
    claim = form[1]
    kind, args = claim[0], claim[1:]
    if kind in ("same", "not-same"):
        a, b = (src.encode(x) for x in args)
        body = f"(check (RenamesToLeader {a} _m1 _l) (RenamesToLeader {b} _m2 _l))"
        if (kind == "not-same") != negated:
            return f"(fail {body})"
        return body
    if kind == "slots":
        a = src.encode(args[0])
        slots = " ".join(f"{s[1:]} {s[1:]}" for s in args[1:])
        body = (
            f"(check (= (ClassSlots {a}) (map-of {slots})))" if slots else f"(check (= (ClassSlots {a}) (map-empty)))"
        )
        return f"(fail {body})" if negated else body
    raise SystemExit(f"{src.path.name}: unknown claim {kind!r}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src", type=pathlib.Path)
    ap.add_argument("-o", "--out", type=pathlib.Path)
    ap.add_argument("--run", action="store_true", help="compile and run egglog on it")
    args = ap.parse_args()

    text = compile_source(Source(args.src))
    if args.out:
        args.out.write_text(text)
    elif not args.run:
        sys.stdout.write(text)

    if args.run:
        with tempfile.NamedTemporaryFile("w", suffix=".egg", delete=False) as f:
            f.write(text)
            path = f.name
        r = subprocess.run(
            [str(ROOT / "target" / "debug" / "egglog"), path], capture_output=True, text=True, cwd=ROOT, timeout=1800
        )
        if r.returncode != 0:
            err = [line for line in r.stderr.splitlines() if "ERROR" in line]
            print(f"FAIL {args.src.name}: {(err[-1] if err else r.stderr.strip())[:300]}")
            # kept only on failure, which is when there is something to read in it
            print(f"     compiled program kept at {path}")
            return 1
        pathlib.Path(path).unlink(missing_ok=True)
        print(f"ok   {args.src.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
