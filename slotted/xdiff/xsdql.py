#!/usr/bin/env python3
"""Differential tester for the reference `sdql` language and its rewrite rules.

The 44-rule SDQL port had no external validation: every other differential check
in `slotted/` runs on the toy language or on the paper's array
language, and the SDQL rules were only ever self-checked against
`slotted/tests/sdql-rewrites.egg`. This compares them against the reference
`slotted-egraphs` implementation, the same way `xarray.py` does for the array
language.

The two sides:

  reference   the rule's own pattern text from `sdql_rules()` in
              `slotted-egraphs/benches/sdql.rs`, flattened into the same
              `MultiPattern` atoms as the encoding by default. `XSDQL_FLAT=0`
              instead exercises the reference benchmark's nested `Rewrite` path.
              Both are tested; the flattened path is the like-for-like oracle.
  encoding    the compiled rule LIFTED VERBATIM out of
              `target/slotted/slotted-sdql-rules.egg` by its `:name`, so what runs is the
              generated artifact and not a re-derivation of it.

`beta` is compiled too. Its right-hand side becomes `slotted-subst` plus the frame
plumbing needed to return an invocation rather than only an e-class. The focused
known-encoding-limitations mode pins capture, extraction, and lexical-flattening
divergences so they remain visible without making the ordinary agreement suite green
on a known-wrong answer.

Usage:
    ./xsdql.py                every case: each rule firing, and each guard blocking
    ./xsdql.py iso [prefix]   the stronger check: a witnessed isomorphism of the two
                              final e-graphs, via `isomorphism.py`
    ./xsdql.py nested         run the corpus through the reference's nested matcher
    ./xsdql.py show <name>    one case's spec, its egg program, and both answers
    ./xsdql.py list           the cases and the rules they exercise
    ./xsdql.py known-encoding-limitations
                              executable witnesses for known encoding gaps
"""

import functools
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from xdiff import EGGLOG, ROOT, XMULTI, parse_same_class, slotenc  # noqa: E402

RUN_TIMEOUT = int(os.environ.get("XSDQL_TIMEOUT", "180"))

# The generated encoding rules. Lifted by `:name`, never rewritten.
RULES_EGG = ROOT / "target" / "slotted" / "slotted-sdql-rules.egg"
# `target/slotted/slotted-lang-sdql.egg` is the SDQL language plus the machinery it includes.
MACHINERY = "target/slotted/slotted-lang-sdql.egg"


# --------------------------------------------------------------------- sdql terms
# term := ('var', slot) | ('num', n) | ('sym', name)
#       | (op, kid...)                for an ordinary operator
#       | ('lambda', slot, body)
#       | ('sum', range, slot, slot, body)
#       | ('merge', range1, range2, slot, slot, slot, body)
#       | ('let', value, slot, body)
#
# The encoding of one is NOT written here: `slotted-encoder.py` owns `slots` /
# `edge` / `enc` / `sexpr` / `shift`, and the columns it walks are read off
# `slotted/languages/sdql.egg` -- the same file `gen-sdql-rules.py`
# compiles the rules against. So a term cannot come to disagree with the rule that
# has to match it about a node's arity, its payload columns, or which of its
# children it binds: `sum`, `merge` and `let` bind their columns 1&2, 2&3&4 and 1
# because that file's `:binder` says they do, and nothing here restates it.
#
# Terms take their columns in the reference's surface order, which is where its
# `Bind<>` layers put the bound slots: `Sum(AppliedId, Bind<Bind<AppliedId>>)`
# prints as `(sum ?R $k $v ?body)`.
#
# What that file does not say is the NAMING -- what the reference calls each
# constructor -- because that is a fact about the harness and not about the
# encoding. `languages/sdql.ref` beside it says that, including the two
# workarounds below.

# `let` is the one tag the oracle could not keep: `xmulti`'s language already has
# the array `Let(Bind<AppliedId>, AppliedId) = "let"`, a different node, and
# `define_language!` dispatches on the tag alone. See the comment in
# `xmulti/src/main.rs`.

# Every `Symbol` payload is written with this prefix on the REFERENCE side, and
# without it on the encoding side.
#
# The reference's parser reads a leaf by trying the operator tags FIRST -- the
# generated `from_syntax` is a `match` on the token -- and only falls through to
# the payload types for a token that is no tag at all. So a payload spelled like
# a tag is not a payload:
#
#     (binop add ?a ?b)    the array `Add(AppliedId, AppliedId) = "add"` arm, which
#                          then wants two children and has none -> a parse ERROR
#     (binop null ?a ?b)   the array `Null() = "null"` arm, which wants none --
#                          it parses, as `Binop(Null, ?a, ?b)`, SILENTLY not the
#                          `Symbol("null")` the encoding builds
#
# `sdql_rules()` uses the payload symbols `mult`, `add`, `sub`, `getf`, `singf`
# and `uniquef`, two of which (`add`, `sub`) are array tags. Prefixing every one
# of them makes the payload namespace disjoint from the tag namespace by
# construction, so no rule can hit either case. The spelling is opaque -- only
# `Symbol(x) == Symbol(y)` is ever asked -- and the prefix is applied to every
# symbol on that side, terms and rules alike, so the two e-graphs stay isomorphic
# and the probe partitions stay comparable.
# The language is declared where its rules are: `slotted/languages/sdql.egg` holds both,
# and `sdql.ref` beside it says what the reference calls each constructor.
SDQL_SRC = ROOT / "slotted" / "languages" / "sdql.egg"
# The language file says what the constructors are; the `.ref` beside it says what the
# reference calls them, including the two workarounds above. `slotenc.language` checks
# that the two name the same constructors, so an operator added to one and not the other
# is an error here rather than a corpus that quietly stops covering the language the
# rules were compiled from.
LANG = slotenc.language(SDQL_SRC, SDQL_SRC.with_suffix(".ref"))

CORR = slotenc.read_correspondence(SDQL_SRC.with_suffix(".ref"))
OPS = {op: (ctor, tag) for op, (ctor, tag, _) in CORR.items()}
SYM_PREFIX = CORR["sym"][2]
LET_TAG = CORR["let"][1]
assert SYM_PREFIX and LET_TAG != "let", "sdql.ref lost one of the two workarounds above"

enc, sexpr, shift = LANG.enc, LANG.sexpr, LANG.shift

sc = __import__("slotted-egglog")


def check_term(t):
    """Walk a term so future per-node validation has one central hook.

    A bound name may also occur free in an uncovered column: `Bind<T>` covers only
    its wrapped body, and the generated binder machinery renames the bound occurrence
    away from that free one.  Such collisions used to be excluded here, hiding exactly
    the scope boundary the differential suite needs to compare.
    """
    for x in t[1:]:
        if isinstance(x, tuple):
            check_term(x)


# ---------------------------------------------------------------------- the rules
# Read from `slotted/languages/sdql.egg` and rendered in the oracle's syntax, which is
# where the two spelling workarounds above come from -- `Let`'s tag and `Symbol`'s
# prefix are in `sdql.ref`, so neither is applied by hand here.
#
# A cond is (want, '$slot', [pvar...]) and reads "the slot is / is not among the slots
# of any listed variable", which is what the reference's guards test: every SDQL guard
# is `!subst[v].slots().contains(&Slot::named(s))`, so `notin` with one variable, and
# two of them conjoined for the two bound slots.


class Rule:
    """One rewrite, with each side already in the oracle's own syntax.

    Derived from `slotted/languages/sdql.egg` rather than restated: `pat_sexpr` renders a
    pattern with `op.ref` for every operator and `op.ref_prefix` for a payload leaf,
    which is where `sdql-let` and the `sym:` prefix come from. Deriving them, rather
    than keeping a hand-written copy here, is what stops them drifting from the rules
    that actually run.
    """

    def __init__(self, name, lhs, rhs, conds=(), atoms=None, egg=None):
        self.name = name
        self.lhs = lhs
        self.rhs = rhs
        self.conds = list(conds)
        #: `(root, atoms)` from `slotenc.flatten`, or None where the pattern has no
        #: atom spelling; see `atom_lines`.
        self.flat = atoms
        # Ordinary cases lift the generated rule by name. A focused compiler
        # limitation may instead carry the exact rule text compiled for its synthetic
        # multipattern; keeping that exceptional path explicit prevents it from
        # weakening the generated-artifact check above.
        self.egg = egg

    def atom_lines(self):
        """The pattern as `atom` lines, or None where it has no atom spelling."""
        if self.flat is None:
            return None
        return slotenc.atom_lines(LANG, *self.flat)

    def spec_lines(self, flat=False):
        # `rhs <root> <pattern>`: on the nested path the root is unused (the whole
        # pattern is the root), so it is written `_`.
        spelled = self.atom_lines() if flat else None
        if spelled is None:
            out = ["rule", f"nested {self.lhs}", f"rhs _ {self.rhs}"]
        else:
            root, atoms = spelled
            out = ["rule", *atoms, f"rhs {root} {self.rhs}"]
        for want, slot, pvars in self.conds:
            out.append(f"cond {'in' if want else 'notin'} {slot} {' '.join(pvars)}")
        return out


#: The rules, read from `slotted/languages/sdql.egg` -- the same file `gen-sdql-rules.py`
#: compiles -- with each side rendered in the oracle's syntax. The cases below ask for
#: one by name.
def _load_rules():
    src = sc.Source(SDQL_SRC)
    out = {}
    for form in sc.parse(SDQL_SRC.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        r = sc.rewrite_parts(src, form)
        # `:when (= ...)` contributes PATTERN ATOMS, and this builds its own rule object
        # from `lhs`/`conds` alone, so one would be dropped in silence and the reference
        # would be asked a different question than the encoding. Teach `Rule` about extra
        # atoms before using one in this language.
        assert not r["equalities"], f"{r['name']}: `:when (= ...)` is not supported here yet"
        lhs_term, rhs_term = (src.term(side, ground=False) for side in (r["lhs"], r["rhs"]))
        lhs, rhs = (slotenc.pat_sexpr(LANG, slotenc.rhs_of(LANG, t)) for t in (lhs_term, rhs_term))
        # the same flattening the encoder does, so the reference can be asked the
        # flattened question rather than the nested one
        try:
            atoms = slotenc.flatten(LANG, lhs_term)
        except Exception:
            atoms = None
        out[r["name"]] = Rule(r["name"], lhs, rhs, conds=r["conds"], atoms=atoms)
    return out


RULES = _load_rules()

#: Ask the reference the FLATTENED question, which is the like-for-like comparison: the
#: encoding flattens every rule, and the two pattern languages are not the same one -- a
#: nested pattern records which variables sit under a binder and a multipattern does not
#: (upstream issue #48). Comparing our flat encoding against the reference's NESTED
#: matcher therefore attributes that difference to the encoding.
#:
#: `XSDQL_FLAT=0` restores the nested comparison. The pinned PR #46 fixes the former
#: nested matcher gaps, and the suite exercises both paths; the separate
#: `reference-limitations` mode records the remaining flat-only lexical gap.
FLAT = os.environ.get("XSDQL_FLAT", "1") == "1"


@functools.cache
def egg_rule(name):
    """The compiled rule of that name, lifted out of the generated file."""
    text = RULES_EGG.read_text()
    i = 0
    while True:
        j = text.find("\n(rule ", i)
        if j < 0:
            raise KeyError(f"no compiled rule named {name!r} in {RULES_EGG}")
        j += 1
        depth, k, instr = 0, j, False
        while k < len(text):
            c = text[k]
            if instr:
                instr = c != '"'
            elif c == '"':
                instr = True
            elif c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    break
            k += 1
        block = text[j : k + 1]
        if block.endswith(f':name "{name}")'):
            return block
        i = k + 1


# ---------------------------------------------------------------------- the cases
class Case:
    def __init__(
        self,
        name,
        rule,
        terms,
        probes,
        want,
        rounds=3,
        ref_want=None,
        why=None,
        unions=(),
        flat=None,
    ):
        self.name = name
        self.rule = rule
        self.terms = list(terms)
        self.unions = list(unions)
        self.probes = list(probes)
        # the partition both sides must report, so a case that agrees on a
        # collapsed or empty answer still fails
        self.want = want
        self.rounds = rounds
        # A RECORDED DIVERGENCE: the reference is expected to answer `ref_want`
        # while the encoding answers `want`, for the reason in `why`. Both sides
        # are pinned, so either one moving is still a failure -- this documents a
        # known difference, it does not stop comparing.
        self.ref_want = ref_want
        self.why = why
        # `None` follows the ordinary suite-wide choice. Focused limitations pin the
        # matcher they exercise: beta is the reference benchmark's nested rewrite,
        # while the conjunctive query necessarily uses MultiPattern.
        self.flat = flat
        assert (ref_want is None) == (why is None), "a divergence needs its reason"
        for t in self.terms + self.probes + [t for pair in self.unions for t in pair]:
            check_term(t)

    def spec(self, with_rule=True):
        out = [f"rounds {self.rounds}"]
        out += [f"term {sexpr(t)}" for t in self.terms]
        out += [f"union {sexpr(a)} {sexpr(b)}" for a, b in self.unions]
        if with_rule:
            out += self.rule.spec_lines(flat=FLAT if self.flat is None else self.flat)
        out += [f"probe {sexpr(t)}" for t in self.probes]
        return "\n".join(out) + "\n"

    def shifted(self, k):
        return Case(
            self.name + f"+{k}",
            self.rule,
            [shift(t, k) for t in self.terms],
            [shift(t, k) for t in self.probes],
            self.want,
            self.rounds,
            self.ref_want,
            self.why,
            unions=[(shift(a, k), shift(b, k)) for a, b in self.unions],
            flat=self.flat,
        )


def schedule(steps):
    return (
        f"(run-schedule (saturate (run slotted))\n"
        f"              (repeat {steps} (seq (run sdql) (saturate (run slotted)))))"
    )


def egg_program(case, with_rule=True, mult=3):
    out = [f'(include "{MACHINERY}")', "(ruleset sdql)"]
    if with_rule:
        out.append(f";; {case.rule.name}")
        out.append(case.rule.egg if case.rule.egg is not None else egg_rule(case.rule.name))
    # A slotted e-class is not one egglog e-class: two probes are in the same
    # slotted class when they reach a common leader.
    out += [
        "(ruleset probe)",
        "(relation ProbeId (U i64))",
        "(relation SameClass (i64 i64))",
        "(rule ((ProbeId a i) (ProbeId b j)\n"
        "       (RenamesToLeader a m1 l) (RenamesToLeader b m2 l))\n"
        "      ((SameClass i j)) :ruleset probe)",
    ]
    for i, t in enumerate(case.terms):
        out.append(f"(let _t{i} {enc(t)})")
    for i, (a, b) in enumerate(case.unions):
        out.append(f"(let _ua{i} {enc(a)})")
        out.append(f"(let _ub{i} {enc(b)})")
        out.append(f"(union _ua{i} _ub{i})")
    for i, t in enumerate(case.probes):
        out.append(f"(let _p{i} {enc(t)})")
    out.append(schedule(case.rounds * mult))
    for i, _ in enumerate(case.probes):
        out.append(f"(ProbeId _p{i} {i})")
    # The reference gets exactly `rounds * mult` user-rule rounds.  Probe
    # installation must not silently give the encoding that budget a second time.
    out.append("(run-schedule (saturate (run slotted)))")
    out.append("(run-schedule (saturate (run probe)))")
    out.append("(print-function SameClass 100000)")
    return "\n".join(out) + "\n"


def run_reference(case, with_rule=True):
    try:
        r = subprocess.run(
            [str(XMULTI / "target" / "debug" / "xmulti")],
            input=case.spec(with_rule),
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s")
    if r.returncode != 0:
        lines = r.stderr.strip().splitlines()
        diagnostic = next(
            (line for line in lines if "SlotMap::index" in line or "SlotMap::compose" in line),
            next((line for line in lines if "panicked at" in line), lines[-1] if lines else "?"),
        )
        return ("ERROR", diagnostic)
    part, sat = None, True
    for line in r.stdout.splitlines():
        if line.startswith("PARTITION "):
            part = line[len("PARTITION ") :].strip()
        elif line.startswith("SATURATED "):
            sat = line.split()[1] == "yes"
    if part is None:
        return ("ERROR", "no PARTITION line")
    return ("OK" if sat else "UNSATURATED", part)


def run_reference_limitations():
    """Pin reference behavior that is known not to model nested lexical scope.

    `MultiPattern` flattens the two lexical roles of surface `$x` into one global
    slot. The target correctly gives the Let binder and its uncovered/free sibling
    different internal names, so the flat matcher rejects a valid match that the
    nested matcher accepts. This matters because the differential oracle normally
    uses the same flattened question as the encoding: agreement can otherwise hide
    their shared false negative.
    """
    prefix = "rounds 2\nterm (let $a (var $a) (var $b))\nrule\n"
    flat = prefix + "atom p let $x body value\natom body var $x\natom value var $x\nrhs p null\ngoal null\n"
    nested = prefix + "nested (let $x (var $x) (var $x))\nrhs _ null\ngoal null\n"

    def goal(spec):
        try:
            proc = subprocess.run(
                [str(XMULTI / "target" / "debug" / "xmulti")],
                input=spec,
                capture_output=True,
                text=True,
                timeout=RUN_TIMEOUT,
            )
        except subprocess.TimeoutExpired:
            return "TIMEOUT"
        if proc.returncode != 0:
            return "ERROR: " + (proc.stderr.strip().splitlines()[-1] if proc.stderr.strip() else "?")
        return next(
            (line.removeprefix("GOAL ") for line in proc.stdout.splitlines() if line.startswith("GOAL ")), "MISSING"
        )

    flat_goal, nested_goal = goal(flat), goal(nested)
    ok = flat_goal == "no" and nested_goal == "yes"
    label = "ok" if ok else "FAIL"
    print(f"  {label:<4} multipattern-binder-free  flat={flat_goal}, nested={nested_goal}")
    print(f"\n{int(ok)}/1 pinned-reference limitations reproduced")
    return 0 if ok else 1


def run_encoding(case, with_rule=True, keep=None, mult=3):
    prog = egg_program(case, with_rule, mult)
    path = keep or (ROOT / f"xsdql-tmp-{os.getpid()}-{mult}.egg")
    path.write_text(prog)
    try:
        r = subprocess.run([str(EGGLOG), str(path)], capture_output=True, text=True, timeout=RUN_TIMEOUT, cwd=ROOT)
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s (kept at {path})")
    if r.returncode != 0:
        err = [x for x in r.stderr.splitlines() if "ERROR" in x]
        msg = err[-1] if err else r.stderr.strip()[:600]
        return ("ERROR", f"{msg}\n    (kept at {path})")
    if not keep:
        path.unlink(missing_ok=True)
    return ("OK", parse_same_class(r.stdout, len(case.probes)))


def check_case(case, shift_check=True):
    """Compare both sides. Returns a list of failure strings."""
    fails = []
    # 1. the machinery alone: with no rule the two must already agree, so a
    #    difference below is attributable to the rule and not to the encoding.
    rs, rv = run_reference(case, with_rule=False)
    es, ev = run_encoding(case, with_rule=False)
    if rs != "OK" or es != "OK":
        return [f"{case.name}: baseline ref={rs}:{rv} enc={es}:{ev}"]
    if rv != ev:
        return [f"{case.name}: BASELINE differs (machinery, not the rule)\n    ref {rv}\n    enc {ev}"]
    baseline = rv

    rs, rv = run_reference(case)
    es, ev = run_encoding(case)
    if rs == "TIMEOUT" or es == "TIMEOUT":
        return [f"{case.name}: timeout ref={rs} enc={es}"]
    if rs == "UNSATURATED":
        fails.append(f"{case.name}: reference hit its round cap (bounded comparison)")
    elif rs != "OK":
        return [f"{case.name}: reference crashed: {rv}"]
    if es != "OK":
        return fails + [f"{case.name}: encoding crashed: {ev}"]
    recorded = case.ref_want is not None
    if rv != ev and not (recorded and rv == case.ref_want and ev == case.want):
        fails.append(f"{case.name}: MISMATCH vs reference\n    ref {rv}\n    enc {ev}")
    if recorded and rv == ev:
        fails.append(f"{case.name}: the recorded divergence is GONE -- both sides now say {rv}")
    if case.want is not None and ev != case.want and not fails:
        fails.append(
            f"{case.name}: the encoding agrees, but not on the expected partition\n    want {case.want}\n    got  {ev}"
        )
    # A case whose rule never changed the partition compared the machinery, not the
    # rule -- and a "blocked" case that changed it never blocked anything.
    fired = ev != baseline
    if not fails and (case.want == FIRED) != fired:
        fails.append(
            f"{case.name}: the rule "
            f"{'fired' if fired else 'did not fire'}, which is not what "
            f"the case tests\n    baseline  {baseline}\n"
            f"    with rule {rv}"
        )

    # 2. the encoding at twice the steps: a moving answer means it had not settled,
    #    so the comparison was between two different amounts of work.
    if not fails:
        ds, dv = run_encoding(case, mult=6)
        if ds == "OK" and dv != ev:
            fails.append(
                f"{case.name}: encoding not settled or nondeterministic\n"
                f"    {case.rounds * 3} steps {ev}\n"
                f"    {case.rounds * 6} steps {dv}"
            )

    # 3. slot-renaming invariance, per side.
    if shift_check and not fails:
        sh = case.shifted(40)
        xs, xv = run_reference(sh)
        ys, yv = run_encoding(sh)
        if xs in ("OK", "UNSATURATED") and xv != rv:
            fails.append(f"{case.name}: REFERENCE not slot-renaming invariant\n    {rv}\n    {xv}")
        if ys == "OK" and yv != ev:
            fails.append(f"{case.name}: ENCODING not slot-renaming invariant\n    {ev}\n    {yv}")
    if not fails:
        tag = f"  DIVERGES, ref {rv}" if recorded else ""
        print(f"  ok  {case.name:<24} {'fired' if fired else 'NO-OP':<6} {ev}{tag}")
    return fails


# --------------------------------------------------------------------- shorthands
def V(n):
    return ("var", n)


FIRED = "[0,1][2] missing[[]]"
BLOCKED = "[0][1][2] missing[[]]"


def compiler_regression_cases():
    """Synthetic MultiPatterns that directly exercise the generic compiler.

    They use SDQL constructors only as a convenient shared language.  Keeping the
    exact `compile_rule` output on the encoding side makes these positive tests of
    compiler behavior rather than generated-artifact coverage.
    """
    out = []

    # An ordinary-child slot literal is flattened from `(var $x)`. The reference
    # carries that variable in its substitution, even after the surrounding class
    # has made the slot redundant, so final refinement may merge another carried
    # slot onto `$x`. The side condition makes that alternative load-bearing.
    atoms = [
        ("?r", "add", [("sl", "$x"), ("pv", "b0")], []),
        ("?r", "mult", [("pv", "a1"), ("pv", "b1")], []),
        ("?r", "sub", [("pv", "a2"), ("pv", "b2")], []),
    ]
    atoms = slotenc.connected_order(LANG, atoms, first=0)
    conds = [(True, "$x", ["a2"])]
    multi_egg = slotenc.compile_rule(
        LANG,
        atoms,
        ("build", "?r", ("unique", ("pv", "a2"))),
        conds=conds,
        tail=' :ruleset sdql :name "compiler-carried-slot-refinement")',
    )
    multi_rule = Rule(
        "compiler-carried-slot-refinement",
        "synthetic conjunctive pattern",
        "(unique ?a2)",
        conds=conds,
        atoms=("?r", atoms),
        egg=multi_egg,
    )
    n = ("num", 99)
    redundant_nodes = [
        ("add", V(0), V(1)),
        ("mult", V(2), V(3)),
        ("sub", V(4), V(5)),
    ]
    out.append(
        Case(
            "carried-slot-refinement",
            multi_rule,
            redundant_nodes,
            [n, ("unique", V(4)), ("null",)],
            FIRED,
            rounds=2,
            unions=[(node, n) for node in redundant_nodes],
            flat=True,
        )
    )

    # Repeated occurrences of one pvar independently unify modulo the class's
    # symmetry group. The middle occurrence needs the swap, while the first and
    # third need the identity; sharing one symmetry witness cannot match this row.
    a = ("add", V(0), V(1))
    swapped = ("add", V(1), V(0))
    symmetry_source = ("add", V(2), V(3))
    symmetry_target = ("add", V(3), V(2))
    repeated = ("subarray", a, swapped, a)
    atoms = [("?r", "subarray", [("pv", "x"), ("pv", "x"), ("pv", "x")], [])]
    repeated_egg = slotenc.compile_rule(
        LANG,
        atoms,
        ("build", "?r", ("unique", ("pv", "x"))),
        tail=' :ruleset sdql :name "compiler-repeated-pvar-symmetry")',
    )
    repeated_rule = Rule(
        "compiler-repeated-pvar-symmetry",
        "synthetic repeated-variable pattern",
        "(unique ?x)",
        atoms=("?r", atoms),
        egg=repeated_egg,
    )
    out.append(
        Case(
            "repeated-pvar-symmetry",
            repeated_rule,
            [repeated],
            [repeated, ("unique", a), ("null",)],
            FIRED,
            rounds=2,
            unions=[(symmetry_source, symmetry_target)],
            flat=True,
        )
    )
    return out


def cases():
    out = []

    # --- Repeated names in nested Bind layers mean lexical shadowing, not one
    # simultaneous binder. The innermost layer captures the body occurrence.  This
    # baseline comparison caught the flattened encoding leaving the private binder
    # columns identified with each other.
    out.append(
        Case(
            "nested-binder-shadowing",
            RULES["eq-comm"],
            [],
            [
                ("sum", ("null",), 5, 5, V(5)),
                ("sum", ("null",), 6, 7, V(7)),
                ("sum", ("null",), 6, 7, V(6)),
                ("merge", ("null",), ("null",), 5, 5, 5, V(5)),
                ("merge", ("null",), ("null",), 6, 7, 8, V(8)),
                ("merge", ("null",), ("null",), 6, 7, 8, V(6)),
            ],
            "[0,1][2][3,4][5] missing[[]]",
        )
    )

    # --- a plain binary rule, and the symmetry it puts on the class.
    # The second child is a payload leaf, not a second variable: `(eq (var $1)
    # (var $2))` and `(eq (var $2) (var $1))` are ONE class before any rule runs,
    # since swapping two free slots is a renaming and the partition compares class
    # identity. That case tests nothing, so the children are made distinguishable.
    out.append(
        Case(
            "eq-comm",
            RULES["eq-comm"],
            [("eq", V(1), ("num", 5))],
            [("eq", V(1), ("num", 5)), ("eq", ("num", 5), V(1)), ("get", V(1), ("num", 5))],
            FIRED,
        )
    )

    # --- a payload literal the RIGHT-hand side builds: `(binop mult ?a ?b)`
    out.append(
        Case(
            "mult-app1",
            RULES["mult-app1"],
            [("mult", V(1), V(2))],
            [("mult", V(1), V(2)), ("binop", ("sym", "mult"), V(1), V(2)), ("binop", ("sym", "add"), V(1), V(2))],
            FIRED,
        )
    )

    # --- the payload symbol `add`, which is also an operator tag in `xmulti`'s
    # array language: without `SYM_PREFIX` the reference cannot parse this rule.
    out.append(
        Case(
            "add-app1",
            RULES["add-app1"],
            [("add", V(1), V(2))],
            [("add", V(1), V(2)), ("binop", ("sym", "add"), V(1), V(2)), ("binop", ("sym", "sub"), V(1), V(2))],
            FIRED,
        )
    )

    # --- a payload literal in a LEFT-hand child position, on a 3-child node
    out.append(
        Case(
            "mult-app2",
            RULES["mult-app2"],
            [("binop", ("sym", "mult"), V(1), V(2))],
            [("binop", ("sym", "mult"), V(1), V(2)), ("mult", V(1), V(2)), ("binop", ("sym", "add"), V(1), V(2))],
            FIRED,
        )
    )

    # --- and the same rule blocked by the payload: `add` is not `mult`.
    # The control cannot be the `mult` binop -- the rule fires on that one and it
    # would land in probe 1's class.
    out.append(
        Case(
            "mult-app2-blocked",
            RULES["mult-app2"],
            [("binop", ("sym", "add"), V(1), V(2))],
            [("binop", ("sym", "add"), V(1), V(2)), ("mult", V(1), V(2)), ("binop", ("sym", "sub"), V(1), V(2))],
            BLOCKED,
        )
    )

    # --- a `Num` literal in a left-hand child position, firing and blocked
    out.append(
        Case(
            "add-zero",
            RULES["add-zero"],
            [("add", V(1), ("num", 0))],
            [("add", V(1), ("num", 0)), V(1), ("add", V(1), ("num", 1))],
            FIRED,
        )
    )
    out.append(
        Case(
            "add-zero-blocked",
            RULES["add-zero"],
            [("add", V(1), ("num", 1))],
            [("add", V(1), ("num", 1)), V(1), ("add", V(1), ("num", 2))],
            BLOCKED,
        )
    )

    # --- arity 1, and a `Symbol` the right-hand side builds
    out.append(
        Case(
            "unique-app1",
            RULES["unique-app1"],
            [("unique", V(1))],
            [("unique", V(1)), ("apply", ("sym", "uniquef"), V(1)), ("apply", ("sym", "uniquefx"), V(1))],
            FIRED,
        )
    )

    # --- a nested left-hand side and a nested right-hand side over a `Num`
    out.append(
        Case(
            "get-range",
            RULES["get-range"],
            [("get", ("range", V(3), V(4)), V(7))],
            [
                ("get", ("range", V(3), V(4)), V(7)),
                ("add", V(7), ("sub", V(3), ("num", 1))),
                ("add", V(7), ("sub", ("num", 1), V(3))),
            ],
            FIRED,
        )
    )

    # --- a binder on the left AND two on the right, with `?f` over a payload class
    out.append(
        Case(
            "let-binop3",
            RULES["let-binop3"],
            [("let", V(1), 2, ("binop", ("sym", "mult"), V(2), V(3)))],
            [
                ("let", V(1), 2, ("binop", ("sym", "mult"), V(2), V(3))),
                ("binop", ("sym", "mult"), ("let", V(1), 2, V(2)), ("let", V(1), 2, V(3))),
                ("binop", ("sym", "add"), ("let", V(1), 2, V(2)), ("let", V(1), 2, V(3))),
            ],
            FIRED,
        )
    )

    # --- `let-binop4`: `$x` written for two SIBLING binders, which the two matchers
    # read differently. Asked the FLATTENED question -- the one the encoding actually
    # compiles -- the reference fires it and agrees, on both cases below. Asked the
    # NESTED one (`XSDQL_FLAT=0`) it does not fire at all: the nested matcher gives each
    # binder's bound slot its own fresh name and cannot match a single `$x` against
    # both. That is a fault in the nested matcher, not a fact about the encoding, and
    # upstream PR #46 fixes it -- it makes upstream's own
    # `lambda::redundancy_matching_bug` pass.
    #
    # Its own `tests/lambda/mod.rs` documents the shape, and `let_binop4` in
    # `benches/sdql.rs` has it, so a rule that ships there never fires.
    #
    # The reference's nested matcher gives each `let` node's bound slot its own
    # fresh name and then cannot match the pattern's single `$x` against both, so
    # it reports no match. Its own `tests/multipat/known_bugs.rs` documents this as
    # `lambda::redundancy_matching_bug` and says a flattener "would need to reject or
    # rename patterns that reuse a bound slot outside its binder" -- adding that no
    # rule in that repo has the shape, which `let_binop4` in its own `benches/sdql.rs`
    # contradicts. Flattening asks the weaker, and here the intended, question: two
    # `let`s whose bound slots are IDENTIFIED, which is the only reading that means
    # anything when a binder is alpha-renameable.
    #
    # The encoding's answer is sound, which is the second case's job to show.
    out.append(
        Case(
            "let-binop4-fires",
            RULES["let-binop4"],
            [("binop", ("sym", "mult"), ("let", V(1), 2, V(2)), ("let", V(1), 2, V(1)))],
            [
                ("binop", ("sym", "mult"), ("let", V(1), 2, V(2)), ("let", V(1), 2, V(1))),
                ("let", V(1), 2, ("binop", ("sym", "mult"), V(2), V(1))),
                ("let", V(1), 2, ("binop", ("sym", "add"), V(2), V(1))),
            ],
            FIRED,
        )
    )
    # The capture case: the FIRST `let` binds $2 and the SECOND one's body has $2
    # FREE. Identifying the two binders on the name $2 would capture it and give
    # `mult (var $1) (var $1)`; a name free in neither body is sound. Probe 1 is the
    # sound answer and probe 2 is the captured one, so the partition says which the
    # encoding picked -- and it picks the sound one, because the minted binder avoids
    # the accumulated slots.
    out.append(
        Case(
            "let-binop4-no-capture",
            RULES["let-binop4"],
            [("binop", ("sym", "mult"), ("let", V(1), 2, V(2)), ("let", V(1), 3, V(2)))],
            [
                ("binop", ("sym", "mult"), ("let", V(1), 2, V(2)), ("let", V(1), 3, V(2))),
                ("let", V(1), 9, ("binop", ("sym", "mult"), V(9), V(2))),
                ("let", V(1), 2, ("binop", ("sym", "mult"), V(2), V(2))),
            ],
            FIRED,
        )
    )

    # --- `Sum`: two binders on one node, and slot literals in child positions.
    # The control swaps the two `(var $)` children, which is a DIFFERENT term:
    # the bound slots are ordered, so no renaming turns one into the other.
    out.append(
        Case(
            "sum-sing",
            RULES["sum-sing"],
            [("sum", V(9), 5, 6, ("sing", V(5), V(6)))],
            [("sum", V(9), 5, 6, ("sing", V(5), V(6))), V(9), ("sum", V(9), 5, 6, ("sing", V(6), V(5)))],
            FIRED,
        )
    )

    # --- a right-hand side that builds a `Sum`, i.e. re-binds its two slots
    out.append(
        Case(
            "sum-fact-inv-1",
            RULES["sum-fact-inv-1"],
            [("mult", V(7), ("sum", V(1), 2, 3, ("get", V(2), V(3))))],
            [
                ("mult", V(7), ("sum", V(1), 2, 3, ("get", V(2), V(3)))),
                ("sum", V(1), 2, 3, ("mult", V(7), ("get", V(2), V(3)))),
                ("sum", V(1), 2, 3, ("mult", ("get", V(2), V(3)), V(7))),
            ],
            FIRED,
        )
    )

    # --- `Merge`: three binders on one node, six children, and a built `let`
    lhs = ("sum", V(1), 2, 3, ("sum", V(4), 5, 6, ("ifthen", ("eq", V(3), V(6)), ("get", V(2), V(5)))))
    rhs = ("merge", V(1), V(4), 2, 5, 3, ("let", V(3), 6, ("get", V(2), V(5))))
    # NOT the two ranges swapped: that is the free-slot renaming $1 <-> $4 of
    # probe 1, i.e. the same class. The two key binders swapped reorders the bound
    # slots against the body, which no renaming undoes.
    ctl = ("merge", V(1), V(4), 5, 2, 3, ("let", V(3), 6, ("get", V(2), V(5))))
    out.append(Case("sum-merge", RULES["sum-merge"], [lhs], [lhs, rhs, ctl], FIRED))

    # --- a slot-conditional rule, firing: `$x`,`$y` are not in `?e1`'s slots
    out.append(
        Case(
            "sum-fact-1-fires",
            RULES["sum-fact-1"],
            [("sum", V(1), 2, 3, ("mult", V(7), V(2)))],
            [
                ("sum", V(1), 2, 3, ("mult", V(7), V(2))),
                ("mult", V(7), ("sum", V(1), 2, 3, V(2))),
                ("mult", V(2), ("sum", V(1), 2, 3, V(7))),
            ],
            FIRED,
        )
    )

    # --- and blocked: `?e1` is the first bound slot's variable
    out.append(
        Case(
            "sum-fact-1-blocked",
            RULES["sum-fact-1"],
            [("sum", V(1), 2, 3, ("mult", V(2), V(7)))],
            [
                ("sum", V(1), 2, 3, ("mult", V(2), V(7))),
                ("mult", V(2), ("sum", V(1), 2, 3, V(7))),
                ("mult", V(7), ("sum", V(1), 2, 3, V(2))),
            ],
            BLOCKED,
        )
    )

    # --- blocked on the SECOND bound slot, which is the one an off-by-one misses
    out.append(
        Case(
            "sum-fact-1-blocked-y",
            RULES["sum-fact-1"],
            [("sum", V(1), 2, 3, ("mult", V(3), V(7)))],
            [
                ("sum", V(1), 2, 3, ("mult", V(3), V(7))),
                ("mult", V(3), ("sum", V(1), 2, 3, V(7))),
                ("mult", V(7), ("sum", V(1), 2, 3, V(3))),
            ],
            BLOCKED,
        )
    )

    out.extend(binder_collision_cases())
    out.extend(compiler_regression_cases())
    return out


def binder_collision_cases():
    """Legitimate binder collisions repaired in the pinned reference.

    In each term the bound name is also free in an uncovered column. `Bind<T>` scopes
    only over the body, so the free occurrence must remain.  The encoding is checked
    on a parent pair that would collapse if it lost that occurrence. The former
    reference implementation overwrote and then removed the outer/free weak-shape
    mapping; these cases now run as ordinary comparisons so a regression fails the
    main differential suite.
    """
    shapes = {
        "let": ("let", V(5), 5, ("num", 0)),
        "sum": ("sum", V(5), 5, 6, ("num", 0)),
        "merge": ("merge", V(5), ("num", 0), 5, 6, 7, ("num", 0)),
    }
    return [
        Case(
            f"{name}-free-uncovered",
            RULES["eq-comm"],
            [],
            [("apply", term, V(5)), ("apply", term, V(8))],
            "[0][1] missing[[]]",
        )
        for name, term in shapes.items()
    ]


def known_encoding_limitations():
    """Small witnesses for semantic gaps that must not be mistaken for coverage.

    Each case pins both partitions. Agreement is reported as stale rather than as a
    pass: these belong in the ordinary differential suite once the encoding implements
    the reference behavior.
    """
    ref_subst = "[0,1][2] missing[[]]"
    enc_subst = "[0,2][1] missing[[]]"

    # Capture avoidance must refresh the lambda's private slot, not the free slot in
    # the substituted term. The primitive currently has only flat edge/class pairs and
    # cannot tell which edge is a binder marker.
    capture = ("let", V(0), 1, ("lambda", 0, ("add", V(1), V(0))))
    capture_avoiding = ("lambda", 2, ("add", V(0), V(2)))
    captured = ("lambda", 0, ("add", V(0), V(0)))
    out = [
        Case(
            "subst-capture",
            RULES["beta"],
            [capture],
            [capture, capture_avoiding, captured],
            enc_subst,
            rounds=2,
            ref_want=ref_subst,
            why="slotted-subst does not know which child edges carry bound names",
            flat=False,
        )
    ]

    # A nested binder for the same slot shadows the outer substitution target. The
    # flat encoding walks its marker edge as if it were an ordinary AST child and
    # consequently substitutes below a scope where the reference stops.
    shadow_source = ("let", ("num", 1), 0, ("lambda", 0, V(0)))
    shadow_result = ("lambda", 0, V(0))
    out.append(
        Case(
            "subst-shadowed-target",
            RULES["beta"],
            [shadow_source],
            [shadow_source, shadow_result],
            "[0][1] missing[[]]",
            rounds=2,
            ref_want="[0,1] missing[[]]",
            why="slotted-subst descends through a binder that shadows its target",
            flat=False,
        )
    )

    # The two bodies are one e-class. The pinned oracle's SynExprSubst keeps the source
    # body, and the reference's ExtractionSubst would choose it too: a Bind slot is
    # data in its enclosing e-node, not an AST child, so its costs are 3 versus 4. In
    # the encoding each binder is another edge to Var; counting those markers as
    # children reverses the costs to 5 versus 4 and therefore the result beta builds.
    body_with_two_binders = ("sum", ("null",), 2, 3, V(1))
    body_without_binders = ("add", ("unique", V(1)), ("null",))
    cost_source = ("let", ("num", 0), 1, body_with_two_binders)
    cost_reference = ("sum", ("null",), 2, 3, ("num", 0))
    cost_encoding = ("add", ("unique", ("num", 0)), ("null",))
    out.append(
        Case(
            "subst-binder-cost",
            RULES["beta"],
            [cost_source],
            [cost_source, cost_reference, cost_encoding],
            enc_subst,
            rounds=2,
            ref_want=ref_subst,
            why="slotted-subst counts binder-marker Var edges as extracted AST children",
            unions=[(body_with_two_binders, body_without_binders)],
            flat=False,
        )
    )

    # Flattening erases the distinction between the Let binder/body `$x` and the
    # uncovered/free `$x` in its value. The nested reference matcher gives those
    # lexical roles different identities and matches this target; both the encoding
    # and reference MultiPattern make `$x` globally rigid and miss it. Use the nested
    # path as the oracle here so shared flat incompleteness cannot look like agreement.
    scoped_pattern = ("let", "$x", "$x", "$x")
    root, atoms = slotenc.flatten(LANG, scoped_pattern)
    scope_egg = slotenc.compile_rule(
        LANG,
        atoms,
        ("build", root, ("null",)),
        tail=' :ruleset sdql :name "known-flat-binder-free")',
    )
    scope_rule = Rule(
        "known-flat-binder-free",
        slotenc.pat_sexpr(LANG, slotenc.rhs_of(LANG, scoped_pattern)),
        "null",
        atoms=(root, atoms),
        egg=scope_egg,
    )
    scoped_target = ("let", V(2), 1, V(1))
    out.append(
        Case(
            "flat-binder-free",
            scope_rule,
            [scoped_target],
            [scoped_target, ("null",)],
            "[0][1] missing[[]]",
            rounds=2,
            ref_want="[0,1] missing[[]]",
            why="flattening conflates one surface slot's bound and free lexical roles",
            flat=False,
        )
    )

    return out


def run_known_encoding_limitations():
    limited = known_encoding_limitations()
    bad = 0
    for case in limited:
        baseline = "".join(f"[{i}]" for i in range(len(case.probes))) + " missing[[]]"
        brs, brv = run_reference(case, with_rule=False)
        bes, bev = run_encoding(case, with_rule=False)
        rs, rv = run_reference(case)
        es, ev = run_encoding(case)
        base_ok = brs == bes == "OK" and brv == bev == baseline
        ok = base_ok and rs == es == "OK" and rv == case.ref_want and ev == case.want and rv != ev
        bad += not ok
        if ok:
            print(f"  ok   {case.name:<24} ref {rv}  encoding {ev}")
        elif not base_ok:
            print(f"  FAIL {case.name}: baseline ref={brs}:{brv}, encoding={bes}:{bev}, expected both {baseline}")
        elif rs == es == "OK" and rv == ev:
            print(f"  STALE {case.name}: implementations agree now ({rv}); move it to the ordinary suite")
        else:
            print(
                f"  FAIL {case.name}: ref={rs}:{rv}, expected {case.ref_want}; encoding={es}:{ev}, expected {case.want}"
            )
    print(f"\n{len(limited) - bad}/{len(limited)} known encoding limitations reproduced")
    return 1 if bad else 0


def run_iso(args):
    """A witnessed isomorphism of the two final e-graphs, not just the partition.

    The partition check compares what the PROBES say about each other; this compares
    the whole graph -- every class's slot set, every symmetry group, and a witness
    mapping that has to survive `verify`. sdql is where it matters most: its nodes
    have up to six children and two bound slots, so a structural difference has more
    room to hide behind a probe answer that happens to agree.

    A recorded encoding divergence cannot be compared this way. Those cases disagree
    on purpose, so an isomorphism is not expected to exist and finding none says
    nothing; they are reported as such rather than skipped silently.
    """
    import isomorphism as I

    I.EGG_PROGRAM = egg_program
    I.use_language(LANG)

    cases_ = [c for c in cases() if not args or c.name.startswith(args[0])]
    tally = {"ok": 0, "FAIL": 0, "skip": 0, "limit": 0, "unreadable": 0}
    diverging = []
    for c in cases_:
        if c.ref_want is not None:
            diverging.append(c.name)
            continue
        verdict, detail = I.check(c)
        tally[verdict] += 1
        print(f"  {verdict:4} {c.name:24} {detail}", flush=True)
    n = sum(tally.values())
    print(
        f"\n{tally['ok']}/{n} isomorphic   ({tally['FAIL']} differ, {tally['skip']} skipped,"
        f" {tally['limit']} not comparable, {tally['unreadable']} unreadable)"
        + (f"\n{len(diverging)} recorded divergence(s) not comparable: {', '.join(diverging)}" if diverging else "")
    )
    return 1 if tally["FAIL"] or tally["unreadable"] else 0


def main():
    global FLAT
    argv = sys.argv[1:]
    if argv and argv[0] == "nested":
        FLAT = False
        argv = argv[1:]
    if argv and argv[0] == "iso":
        return run_iso(argv[1:])

    if argv and argv[0] in ("known-encoding-limitations", "known-substitution-limitations"):
        return run_known_encoding_limitations()

    if argv and argv[0] == "reference-limitations":
        return run_reference_limitations()

    if argv and argv[0] == "list":
        for c in cases():
            print(f"{c.name:<24} {c.want}")
            print(f"    {c.rule.name:<16} {c.rule.lhs}  ->  {c.rule.rhs}")
        return 0
    if argv and argv[0] == "show":
        c = next(x for x in cases() if x.name == argv[1])
        print("---- spec")
        print(c.spec(), end="")
        print("---- egg")
        print(egg_program(c))
        print("---- reference     ", run_reference(c))
        print("---- encoding      ", run_encoding(c))
        print("---- ref  baseline ", run_reference(c, with_rule=False))
        print("---- enc  baseline ", run_encoding(c, with_rule=False))
        return 0

    cs = cases()
    bad = 0
    for c in cs:
        f = check_case(c)
        if f:
            bad += 1
        for x in f:
            print("FAIL " + x)
    print(f"\n{len(cs) - bad}/{len(cs)} cases agree")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
