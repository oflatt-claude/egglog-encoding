"""Check which egglog declaration, rule, and command forms the frontend accepts.

Each program must either execute successfully or fail with a diagnostic,
according to its recorded verdict. Tracebacks are failures in either case.

Run with `python3 slotted/checks/check-egglog-forms.py`."""

import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TMP = ROOT / "target" / "slotted" / "forms.egg"
sys.path.insert(0, str(ROOT / "slotted"))
sc = __import__("slotted-egglog")

L = "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n"

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
    ("ok", "sort plus constructor", "(sort M)\n(constructor N (i64) M)\n(let a (N 1))\n(run 0)\n"),
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
        "(datatype U (Start U) (F U) (F_slots U) (F_edge U) (Pair U U))\n"
        "(let start (Start $0))\n"
        "(rewrite (Start a) (Pair (F a) (Pair (F_slots a) (F_edge a))))\n"
        "(run 1)\n(check (= start (Pair (F $0) (Pair (F_slots $0) (F_edge $0)))))\n",
    ),
]


COMPILERS = {
    "Rust": [str(ROOT / "target/debug/egglog-experimental"), "--slotted"],
    "Python": [sys.executable, "slotted/slotted-egglog.py"],
}


def verdict_of(program, compiler):
    TMP.write_text(program)
    r = subprocess.run(
        [*COMPILERS[compiler], str(TMP)],
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


def main():
    TMP.parent.mkdir(parents=True, exist_ok=True)
    repeatable_compilation()
    bad = []
    for want, what, program in PROBES:
        for compiler in COMPILERS:
            got, detail = verdict_of(program, compiler)
            if got == want:
                print(f"  {got:8} {compiler}: {what}")
            else:
                print(f"  {'CHANGED':8} {compiler}: {what}: expected {want}, got {got}\n           {detail}")
                bad.append(what)
    TMP.unlink(missing_ok=True)
    n_ok = sum(1 for w, _, _ in PROBES if w == "ok")
    print(
        f"\n{len(PROBES) - len(set(bad))}/{len(PROBES)} egglog forms behave as recorded "
        f"({n_ok} accepted; both compilers)"
    )
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
        src = sc.Source(path)
        full = sc.compile_source(src)
        own = sc.compile_source(src, own_only=True)
        assert full == sc.compile_source(src)
        assert own == sc.compile_source(sc.Source(path), own_only=True)
        assert not src.lang.bound
        compiled = path.with_name("compiled.egg")
        compiled.write_text(full)
        run = subprocess.run(
            [ROOT / "target/debug/egglog-experimental", "--slotted-encoded", compiled],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert run.returncode == 0, run.stderr
        # This CLI path emits a snapshot and runs the full program in one invocation.
        snapshot = path.with_name("snapshot.egg")
        run = subprocess.run(
            [sys.executable, ROOT / "slotted/slotted-egglog.py", path, "--own-only", "--run", "-o", snapshot],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert run.returncode == 0, run.stdout + run.stderr
        assert snapshot.read_text() == own
    print("  ok       repeated compilation and CLI snapshots preserve source scopes")


if __name__ == "__main__":
    sys.exit(main())
