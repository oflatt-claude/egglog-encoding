"""Accepted source forms, rejected forms, and repeatable compilation."""

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import test_program as driver  # noqa: E402

FORMS_TMP = ROOT / "target" / "slotted" / "forms.egg"

L = "(datatype M ($Var) (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n"

#: (expected verdict, what, program)
PROBES = [
    # ---- facts in a rule body -----------------------------------------------------
    ("ok", "a nested call as the pattern", L + '(rewrite (Add (Mul x y) z) (Nil) :name "r")\n'),
    ("ok", "(= v <call>), a second pattern", L + '(rewrite (Add x y) (Nil) :when ((= x (Mul p q))) :name "r")\n'),
    ("ok", "(= x y), two variables identified", L + '(rewrite (Add x y) (Nil) :when ((= x y)) :name "r")\n'),
    ("ok", "(!= x y)", L + '(rewrite (Add x y) (Nil) :when ((!= x y)) :name "r")\n'),
    ("ok", "a bare call, meaning it exists", L + '(rewrite (Add x y) (Nil) :when ((Mul x y)) :name "r")\n'),
    ("refused", "a nullary constructor without its parens", L + "(let n Nil)\n"),
    ("ok", "a payload literal", L + '(rewrite (Add x y) (Nil) :when ((= x (N 2))) :name "r")\n'),
    ("ok", "a payload variable", L + '(rewrite (Add x y) (Nil) :when ((= x (N i))) :name "r")\n'),
    ("ok", "free/not-free on a slot", L + '(rewrite (Lam $v b) (Nil) :when ((not-free $v b)) :name "r")\n'),
    ("refused", "an i64 primitive over payloads", L + '(rewrite (Add x y) (Nil) :when ((> x y)) :name "r")\n'),
    # ---- the right-hand side ------------------------------------------------------
    ("ok", "builds a term", L + '(rewrite (Add x y) (Mul y x) :name "r")\n'),
    ("ok", "a variable", L + '(rewrite (Add x y) x :name "r")\n'),
    ("ok", "a fresh slot, with no annotation", L + '(rewrite (Add x y) (Lam $s (Add x y)) :name "r")\n'),
    ("refused", "computing a payload", L + '(rewrite (Add (N i) (N j)) (N (+ i j)) :name "r")\n'),
    # ---- rewrite options ----------------------------------------------------------
    ("ok", ":name, as a string literal", L + '(rewrite (Add x y) (Nil) :name "r")\n'),
    ("refused", ":ruleset", "(ruleset rs)\n" + L + '(rewrite (Add x y) (Nil) :ruleset rs :name "r")\n'),
    ("refused", ":subsume", L + '(rewrite (Add x y) (Nil) :subsume :name "r")\n'),
    # ---- declarations -------------------------------------------------------------
    ("ok", "datatype", L + "(let a (N 1))\n(run 0)\n"),
    (
        "ok",
        "sort plus constructor",
        "(sort M)\n(constructor N (i64) M)\n(let a (N 1))\n(run 0)\n",
    ),
    ("ok", "relation", L + "(relation R (M M))\n"),
    ("ok", "function with :merge", L + "(function Cost (M) i64 :merge (min old new))\n"),
    ("refused", "constructor :cost", "(sort M)\n(constructor N (i64) M :cost 5)\n"),
    (
        "ok",
        "datatype*, with independent homogeneous sorts",
        "(datatype* (A (A0) (F A)) (B (B0) (G B)))\n(let a (F (A0)))\n(let b (G (B0)))\n(run 0)\n",
    ),
    # ---- other rule forms ---------------------------------------------------------
    ("refused", "rule", L + "(rule ((= a (Nil))) ())\n"),
    ("refused", "birewrite", L + '(birewrite (Add x y) (Add y x) :name "r")\n'),
    ("refused", "set, which needs rule", L + "(function C (M) i64 :no-merge)\n(rule ((= a (Nil))) ((set (C a) 1)))\n"),
    # ---- commands -----------------------------------------------------------------
    ("ok", "push and pop", L + "(push)\n(let a (Nil))\n(pop)\n"),
    (
        "ok",
        "extract, selecting either carrier",
        "(datatype* (A (A0)) (B (B0)))\n(let a (A0))\n(let b (B0))\n(run 0)\n(extract a)\n(extract b)\n",
    ),
    ("ok", "print-size", L + "(let a (Nil))\n(run 0)\n(print-size)\n"),
    ("refused", "run-schedule, which would skip the phasing", L + "(let a (Nil))\n(run-schedule (run 1))\n"),
    # Generated roots and temporaries must not capture source pattern names.
    (
        "ok",
        "a source variable named like the generated root",
        L + "(let start (Add $1 $2))\n(rewrite (Add _p b) (Mul b _p))\n(run 1)\n(check (= start (Mul $2 $1)))\n",
    ),
    (
        "ok",
        "a sigiled source variable named like the generated root",
        L + "(let start (Add $1 $2))\n(rewrite (Add ?_p b) (Mul b ?_p))\n(run 1)\n(check (= start (Mul $2 $1)))\n",
    ),
    (
        "ok",
        "a source variable named like a nested temporary",
        L + "(let start (Add (Mul $1 $2) $3))\n(rewrite (Add (Mul _t1 b) c) (Mul c _t1))\n(run 1)\n"
        "(check (= start (Mul $3 $1)))\n",
    ),
    (
        "ok",
        "a source variable named like a side-pattern root",
        L + "(let start (Add $1 $2))\n(let other (Mul $1 $2))\n"
        "(rewrite (Add _fact0 b) (Mul b _fact0) :when ((Mul _fact0 b)))\n(run 1)\n"
        "(check (= start (Mul $2 $1)))\n",
    ),
    (
        "ok",
        "a source variable named like a guard root",
        L + "(let start (Lam $1 $2))\n"
        "(rewrite (Lam $v _cond0) (App _cond0 _cond0) :when ((not-free $v (Lam $v _cond0))))\n(run 1)\n"
        "(check (= start (App $2 $2)))\n",
    ),
    (
        "ok",
        "a source variable named like a nested side-pattern temporary",
        L + "(let start (Add (Mul (Mul $1 $2) $3) $4))\n"
        "(rewrite (Add a _w0_1) (Mul _w0_1 p) :when ((= a (Mul (Mul p q) r))))\n(run 1)\n"
        "(check (= start (Mul $4 $1)))\n",
    ),
    (
        "ok",
        "equivalent numbered slot spellings",
        L + "(let start (Add $01 $+1))\n(let zero (Add $-0 $+0))\n(run 0)\n"
        "(check (slots start $1))\n(check (= start (Add $1 $1)))\n"
        "(check (slots zero $0))\n(check (= zero (Add $0 $0)))\n",
    ),
    (
        "ok",
        "constructor names colliding with derived RHS locals",
        "(datatype U ($Var) (Start U) (F U) (F_slots U) (F_edge U) (Pair U U))\n"
        "(let start (Start $0))\n"
        "(rewrite (Start a) (Pair (F a) (Pair (F_slots a) (F_edge a))))\n"
        "(run 1)\n(check (= start (Pair (F $0) (Pair (F_slots $0) (F_edge $0)))))\n",
    ),
]


EGGLOG = ROOT / "target/debug/egglog-experimental"


def verdict_of(program):
    FORMS_TMP.write_text(program)
    r = subprocess.run(
        [str(EGGLOG), "--slotted", str(FORMS_TMP)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=1800,
    )
    out = r.stdout + r.stderr
    if "Traceback (most recent call last)" in out or "panicked" in out:
        return "CRASH", next((ln for ln in reversed(out.splitlines()) if ln.strip()), "")[:80]
    if r.returncode == 0:
        return "ok", ""
    return "refused", next((ln for ln in out.splitlines() if ln.strip()), "")[:80]


def forms():
    FORMS_TMP.parent.mkdir(parents=True, exist_ok=True)
    repeatable_compilation()
    bad = []
    for want, what, program in PROBES:
        got, detail = verdict_of(program)
        if got == want:
            print(f"  {got:8} Rust: {what}")
        else:
            print(f"  {'CHANGED':8} Rust: {what}: expected {want}, got {got}\n           {detail}")
            bad.append(what)
    FORMS_TMP.unlink(missing_ok=True)
    n_ok = sum(1 for w, _, _ in PROBES if w == "ok")
    print(f"\n{len(PROBES) - len(set(bad))}/{len(PROBES)} egglog forms behave as recorded ({n_ok} accepted; Rust CLI)")
    return 1 if bad else 0


def repeatable_compilation():
    program = (
        L
        + """
(push)
(let y (Nil))
(pop)
(rewrite (Add x y) (Add y x))
(let x (Nil))
(let seed (Add (N 1) (N 2)))
(run 1)
(check (= seed (Add (N 2) (N 1))))
"""
    )
    with tempfile.TemporaryDirectory(prefix="slotted-compile-") as tmp:
        path = Path(tmp) / "source.egg"
        path.write_text(program)
        full = driver.compile_source(program)
        driver.compile_source.cache_clear()
        assert full == driver.compile_source(program)
        compiled = path.with_name("compiled.egg")
        compiled.write_text(full)
        run = subprocess.run(
            [ROOT / "target/debug/egglog-experimental", "--slotted-encoded", compiled],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert run.returncode == 0, run.stderr
    print("  ok       repeated Rust compilation preserve source scopes")


REFUSALS_TMP = ROOT / "target" / "slotted" / "refusal.egg"

LANG = "(datatype M ($Var) (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n"

#: (what is refused, program, a phrase the message must carry)
CASES = [
    ("a slot in a sort without $Var", "(datatype M (F M)) (let bad (F $a))", "does not declare $Var"),
    (
        "a binder without a variable variant",
        "(datatype M (Lam M M :binder 0))\n",
        "must declare $Var",
    ),
    ("a term in a ground binder column", LANG + "(let bad (Lam (Null) (Null)))\n", "takes a slot literal"),
    (
        "a global in a binder column",
        LANG + "(let alias (Succ $a))\n(let bad (Lam alias (Null)))\n",
        "takes a slot literal",
    ),
    (
        "a pattern variable in a binder result column",
        LANG + "(rewrite (Succ x) (Lam x x))\n",
        "takes a slot literal",
    ),
    (
        "a variable variant with columns",
        "(datatype M ($Var M) (N))\n",
        "$Var takes no columns or options",
    ),
    ("an out-of-range numeric slot", LANG + "(let bad (Succ $9223372036854775808))\n", "signed 64-bit"),
    ("an empty slot name", LANG + "(let bad (Succ $))\n", "invalid slot literal"),
    ("a global named with a `$`", LANG + "(let $I (IConst))\n", "must not start with $"),
    (
        "a global bound to a bare slot invocation",
        LANG + "(let v $7)\n",
        "cannot currently store",
    ),
    (
        "a bare `:when` fact without the list",
        LANG + '(rewrite (Mul a b) a :when (= a (Succ p)) :name "r")\n',
        "takes a list of facts",
    ),
    (
        "several `:when` clauses",
        LANG + '(rewrite (Mul a b) a :when ((= a (Succ p))) :when ((= b (Succ q))) :name "r")\n',
        "one list",
    ),
    (
        "egglog's `:cost`, which extraction here would not honour",
        "(sort M)\n(constructor Succ (M) M :cost 5)\n",
        "option :cost is not supported",
    ),
    (
        "an unknown declaration option",
        "(sort M)\n(constructor Succ (M) M :wat 1)\n",
        "option :wat is not supported",
    ),
    # egglog refuses the bare spelling in both positions -- `Unbound symbol` where a term
    # is wanted, `Shadowing is not allowed` where a rule variable would be -- so reading
    # it as a call here was a divergence that bought nothing.
    ("a nullary constructor without its parens, in a term", LANG + "(let n Null)\n", "needs parentheses"),
    (
        "a nullary constructor without its parens, in a pattern",
        LANG + '(rewrite (Succ Null) (Null) :name "r")\n',
        "needs parentheses",
    ),
    (
        "a negative binder position",
        "(sort M)\n(constructor F (M M) M :binder -1)\n",
        "binder position",
    ),
    (
        "an out-of-range binder position",
        "(sort M)\n(constructor F (M M) M :binder 2)\n",
        "binder position",
    ),
    (
        "duplicate binder positions",
        "(sort M)\n(constructor F (M M) M :binder 0 0)\n",
        "duplicate",
    ),
    (
        "non-contiguous nested binders",
        "(sort M)\n(constructor F (M M M M) M :binder 0 2)\n",
        "contiguous",
    ),
    (
        "a binder without a covered child",
        "(sort M)\n(constructor F (M M) M :binder 1)\n",
        "following child",
    ),
    (
        "a cross-sort slotted child",
        "(sort A)\n(sort B)\n(constructor A0 () A)\n(constructor B0 () B)\n(constructor F (A B) A)\n",
        "cross-sort slotted children",
    ),
    # A sort named after one of the machinery's own declarations is a double declaration,
    # which is the only naming a program may not use. Naming one after a rule VARIABLE
    # used to be refused too, because the carrier was substituted into a hand-written
    # file's text; the machinery is generated now, so `(sort m)` and `(sort N)` are fine.
    (
        "a sort the machinery already declares",
        "(sort Idx)\n(constructor F (Idx) Idx)\n",
        "is reserved",
    ),
    (
        "a cross-sort union",
        "(datatype* (A (A0)) (B (B0)))\n(let a (A0))\n(let b (B0))\n(union a b)\n",
        "cannot compare terms of different equality sorts",
    ),
    (
        "a global used at the wrong sort",
        "(datatype* (A (A0)) (B (B0) (G B)))\n(let a (A0))\n(let bad (G a))\n",
        "expected B",
    ),
    (
        "a cross-sort equality check",
        "(datatype* (A (A0)) (B (B0)))\n(check (= (A0) (B0)))\n",
        "cannot compare terms of different equality sorts",
    ),
    (
        "a cross-sort renaming equality check",
        "(datatype* (A (A0)) (B (B0)))\n(check (renaming-= (A0) (B0)))\n",
        "cannot compare terms of different equality sorts",
    ),
    (
        "a holds check naming a constructor from another sort",
        "(datatype* (A (A0)) (B (B0)))\n(check (holds (A0) B0))\n",
        "holds compares different carrier sorts",
    ),
    (
        "a cross-sort rewrite result",
        '(datatype* (A (A0)) (B (B0)))\n(rewrite (A0) (B0) :name "bad")\n',
        "B0 produces B, expected A",
    ),
    (
        "a cross-sort side pattern",
        '(datatype* (A (A0)) (B (B0)))\n(rewrite (A0) (A0) :when ((B0)) :name "bad")\n',
        "cross-sort multipatterns",
    ),
    (
        "an ambiguous top-level slot comparison",
        "(datatype* (A (A0)) (B (B0)))\n(check (= $0 $1))\n",
        "no equality-sort context",
    ),
    (
        "a multi-sort encoding-name collision",
        "(sort A)\n(sort B)\n(constructor SlottedVar_0 () A)\n(constructor B0 () B)\n",
        "reserved by the slotted",
    ),
    (
        "a duplicate equality sort declaration",
        "(sort A)\n(sort A)\n(constructor A0 () A)\n",
        'sort "A" is declared more than once',
    ),
    (
        "a duplicate constructor declaration",
        "(sort A)\n(constructor A0 () A)\n(constructor A0 () A)\n",
        'constructor "A0" is declared more than once',
    ),
    (
        "a payload-layout name collision",
        "(sort U)\n(constructor SlottedPayloadLayout () U)\n",
        "reserved by the slotted",
    ),
    (
        "a machinery phase ruleset collision",
        LANG + "(ruleset slotted-group)\n",
        "reserved by the slotted",
    ),
    ("a program that declares nothing", "(run 1)\n", "no equality sort is declared"),
    (
        "a named ruleset that the slotted schedule cannot select",
        LANG + '(ruleset custom)\n(rewrite (Succ a) a :name "custom-rule" :ruleset custom)\n',
        "named rulesets are not supported",
    ),
    (
        "a pattern variable in a binder column",
        LANG + "(rewrite (Lam x (Succ x)) (Null))\n",
        "takes a slot literal",
    ),
    ("a sort with no constructors", "(sort A)\n(run 1)\n", "no constructors declared"),
    (
        "an unbound rewrite root",
        LANG + '(rewrite x (Mul x x) :name "r")\n',
        "needs a constructor pattern",
    ),
    (
        "egglog's `rule`, which this language does not have",
        LANG + "(rule ((= a (Null))) ())\n",
        "not supported by the slotted frontend",
    ),
    (
        "a payload variable the right-hand side names and no pattern binds",
        '(sort M)\n(constructor N (i64) M)\n(constructor A (M M) M)\n(rewrite (A x y) (N j) :name "r")\n',
        "is not bound",
    ),
]


def refusals():
    REFUSALS_TMP.parent.mkdir(parents=True, exist_ok=True)
    bad = []
    for what, program, phrase in CASES:
        REFUSALS_TMP.write_text(program)
        r = subprocess.run(
            [str(ROOT / "target/debug/egglog-experimental"), "--slotted", str(REFUSALS_TMP)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=600,
        )
        out = r.stdout + r.stderr
        if r.returncode == 0:
            print(f"  FAIL {what}: accepted")
            bad.append(what)
        elif "Traceback (most recent call last)" in out or "panicked" in out:
            print(f"  FAIL {what}: refused with a traceback, not a message")
            bad.append(what)
        elif phrase not in out:
            print(f"  FAIL {what}: message lacks {phrase!r}\n       {out.strip().splitlines()[-1][:120]}")
            bad.append(what)
        else:
            print(f"  ok   {what}")
    REFUSALS_TMP.unlink(missing_ok=True)
    print(f"\n{len(CASES) - len(bad)}/{len(CASES)} refusals hold, with a message")
    return 1 if bad else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("forms", "refusals"))
    args = parser.parse_args()
    checks = {"forms": forms, "refusals": refusals}
    return checks[args.check]()


if __name__ == "__main__":
    sys.exit(main())
