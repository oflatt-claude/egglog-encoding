#!/usr/bin/env python3
"""Differential tester for the reference `sdql` language and its rewrite rules.

The 44-rule SDQL port had no external validation: every other differential check
in `slotted-experiments/` runs on the toy language or on the paper's array
language, and the SDQL rules were only ever self-checked against
`tests/slotted-sdql-rewrites.egg`. This compares them against the reference
`slotted-egraphs` implementation, the same way `xarray.py` does for the array
language.

The two sides:

  reference   the rule's own pattern text from `sdql_rules()` in
              `slotted-egraphs/benches/sdql.rs`, handed to `xmulti` as
              `nested` / `rhs` / `cond` lines -- i.e. literally `Rewrite::new_if`
              over the reference's single-pattern matcher, which is how the
              benchmark itself runs them. Every SDQL rule is a single-pattern
              rewrite, so no multipattern flattening happens on this side.
  encoding    the compiled rule LIFTED VERBATIM out of
              `tests/slotted-sdql-rules.egg` by its `:name`, so what runs is the
              generated artifact and not a re-derivation of it.

`beta` is not here. It rewrites to `?body[(var $x) := ?t]`, which the encoding
answers with `slotted-subst` and frame plumbing rather than with a compiled rule,
so `tests/slotted-sdql-rules.egg` has no `beta` to lift. (The reference side
could express it: `rhs` hands its text to `Pattern::parse`, which builds
`Pattern::Subst` for the `[_ := _]` form. There is simply nothing to compare it
against.)

Usage:
    ./xsdql.py                every case: each rule firing, and each guard blocking
    ./xsdql.py show <name>    one case's spec, its egg program, and both answers
    ./xsdql.py list           the cases and the rules they exercise
"""

import functools
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from xdiff import EGGLOG, ROOT, XMULTI, parse_same_class, slotenc  # noqa: E402

RUN_TIMEOUT = int(os.environ.get("XSDQL_TIMEOUT", "180"))

# The generated encoding rules. Lifted by `:name`, never rewritten.
RULES_EGG = ROOT / "tests" / "slotted-sdql-rules.egg"
# `tests/slotted-lang-sdql.egg` is the SDQL language plus the machinery it includes.
MACHINERY = "tests/slotted-lang-sdql.egg"


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
# `slotted-experiments/languages/sdql.egg` -- the same file `gen-sdql-rules.py`
# compiles the rules against. So a term cannot come to disagree with the rule that
# has to match it about a node's arity, its payload columns, or which of its
# children it binds: `sum`, `merge` and `let` bind their columns 1&2, 2&3&4 and 1
# because that file's `:binder` says they do, and nothing here restates it.
#
# Terms take their columns in the reference's surface order, which is where its
# `Bind<>` layers put the bound slots: `Sum(AppliedId, Bind<Bind<AppliedId>>)`
# prints as `(sum ?R $k $v ?body)`.
#
# What that file does not say in machine-readable form is the NAMING -- its tags
# are in comments, `; Add(A, A)  "+"` -- so the operator table below is written
# out, and asserted against the file so a renamed constructor is an error here.

# `let` is the one tag the oracle could not keep: `xmulti`'s language already has
# the array `Let(Bind<AppliedId>, AppliedId) = "let"`, a different node, and
# `define_language!` dispatches on the tag alone. See the comment in
# `xmulti/src/main.rs`.
LET_TAG = "sdql-let"

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
SYM_PREFIX = "sym:"

# operator -> (constructor, the reference's tag). A tag of `None` marks a payload
# leaf, which the reference writes as the payload itself.
OPS = {
    "lambda": ("Lambda", "lambda"),
    "sing": ("Sing", "sing"),
    "add": ("Add", "+"),
    "mult": ("Mult", "*"),
    "sub": ("Sub", "-"),
    "eq": ("Equality", "eq"),
    "get": ("Get", "get"),
    "range": ("Range", "range"),
    "apply": ("App", "apply"),
    "ifthen": ("IfThen", "ifthen"),
    "binop": ("Binop", "binop"),
    "subarray": ("SubArray", "subarray"),
    "unique": ("Unique", "unique"),
    "sum": ("Sum", "sum"),
    "merge": ("Merge", "merge"),
    "let": ("Let", LET_TAG),
    "num": ("Num", None),
    "sym": ("Symbol", None),
}

SIGS = slotenc.read_language(ROOT / "slotted-experiments" / "languages" / "sdql.egg")
# The table above is the one thing not read off that file, so it is checked against
# it: a constructor renamed, added or dropped there is an error here rather than a
# corpus that quietly stops covering the language the rules were compiled from.
assert {ctor for ctor, _ in OPS.values()} == set(SIGS), \
    "the operator table and languages/sdql.egg name different constructors"


class SdqlTerms(slotenc.TermLang):
    """The shared term language, plus the one thing the two sides spell differently.

    A payload leaf is written as its payload, which for a `Symbol` is the same
    spelling on both sides EXCEPT for `SYM_PREFIX`. That is the reference's parser
    working around itself, not part of the encoding, so it is overridden here rather
    than given a hook in the encoder.
    """

    def sexpr(self, t):
        if t[0] == "sym":
            return SYM_PREFIX + t[1]
        return super().sexpr(t)


LANG = SdqlTerms({op: slotenc.Op(op, ctor, SIGS[ctor], ref=ref)
                  for op, (ctor, ref) in OPS.items()})

enc, sexpr, shift = LANG.enc, LANG.sexpr, LANG.shift


def check_term(t):
    """Reject terms where the reference and the encoding disagree on a node's slots.

    `Bind<T>` hides the bound slot from that ONE column; the encoding's `:binder`
    drops it from the whole node. The two agree only when no uncovered column
    mentions a bound slot, so a term that does is out of scope for a comparison
    rather than a mismatch to report -- `tests/slotted-lang-sdql.egg` says the
    encoding renames such a collision away, which is a different node.
    """
    k = t[0]
    if k == "sum":
        assert not (LANG.slots(t[1]) & {t[2], t[3]}), \
            f"range mentions a bound slot: {t}"
    if k == "merge":
        assert not ((LANG.slots(t[1]) | LANG.slots(t[2])) & {t[3], t[4], t[5]}), \
            f"a range mentions a bound slot: {t}"
    if k == "let":
        assert not (LANG.slots(t[1]) & {t[2]}), f"value mentions the bound slot: {t}"
    for x in t[1:]:
        if isinstance(x, tuple):
            check_term(x)


# ---------------------------------------------------------------------- the rules
# LHS / RHS text copied from `sdql_rules()` in `slotted-egraphs/benches/sdql.rs`,
# byte for byte; `ref_text` applies the two spelling rewrites above and nothing
# else. A cond is (want, '$slot', [pvar...]) and reads "the slot is / is not among
# the slots of any listed variable", which is what the reference's guards test:
# every SDQL guard is `!subst[v].slots().contains(&Slot::named(s))`, so `notin`
# with one variable, and two of them conjoined for the two bound slots.

class Rule:
    def __init__(self, name, lhs, rhs, conds=()):
        self.name = name
        self.lhs = lhs
        self.rhs = rhs
        self.conds = list(conds)

    def spec_lines(self):
        # `rhs <root> <pattern>`: on the nested path the root is unused (the whole
        # pattern is the root), so it is written `_`.
        out = ["rule", f"nested {ref_text(self.lhs)}",
               f"rhs _ {ref_text(self.rhs)}"]
        for want, slot, pvars in self.conds:
            out.append(f"cond {'in' if want else 'notin'} {slot} {' '.join(pvars)}")
        return out


def ref_text(s):
    """The reference's own pattern text in `xmulti`'s spellings.

    Two mechanical rewrites, and nothing else: the operator `let` becomes
    `sdql-let`, and a payload symbol in a child position gets `SYM_PREFIX`. A
    token is an operator exactly when it follows `(`; a child token is a pattern
    variable (`?x`), a slot (`$x`), an integer, or a payload symbol. `list` prints
    the result for every rule, so the rewrite is auditable rather than trusted.
    """
    out, op_next = [], False
    for tok in re.findall(r"[()]|[^\s()]+", s):
        if tok in ("(", ")"):
            out.append(tok)
            op_next = tok == "("
        elif op_next:
            out.append(LET_TAG if tok == "let" else tok)
            op_next = False
        elif tok[0] in "?$" or re.fullmatch(r"-?\d+", tok):
            out.append(tok)
        else:
            out.append(SYM_PREFIX + tok)
    # the reference's tokenizer splits on parens, so spacing is free
    return " ".join(out)


RULES = {
    "eq-comm": Rule("eq-comm", "(eq ?a ?b)", "(eq ?b ?a)"),
    "mult-app1": Rule("mult-app1", "(* ?a ?b)", "(binop mult ?a ?b)"),
    "add-app1": Rule("add-app1", "(+ ?a ?b)", "(binop add ?a ?b)"),
    "mult-app2": Rule("mult-app2", "(binop mult ?a ?b)", "(* ?a ?b)"),
    "add-zero": Rule("add-zero", "(+ ?e 0)", "?e"),
    "unique-app1": Rule("unique-app1", "(unique ?a)", "(apply uniquef ?a)"),
    "get-range": Rule("get-range", "(get (range ?st ?en) ?idx)",
                      "(+ ?idx (- ?st 1))"),
    "let-binop3": Rule("let-binop3", "(let ?e1 $x (binop ?f ?e2 ?e3))",
                       "(binop ?f (let ?e1 $x ?e2) (let ?e1 $x ?e3))"),
    "sum-sing": Rule("sum-sing", "(sum ?e1 $k $v (sing (var $k) (var $v)))", "?e1"),
    "sum-fact-inv-1": Rule("sum-fact-inv-1", "(* ?e1 (sum ?R $k $v ?e2))",
                           "(sum ?R $k $v (* ?e1 ?e2))"),
    "sum-merge": Rule(
        "sum-merge",
        "(sum ?R $k1 $v1 (sum ?S $k2 $v2 (ifthen (eq (var $v1) (var $v2)) ?body)))",
        "(merge ?R ?S $k1 $k2 $v1 (let (var $v1) $v2 ?body))"),
    "sum-fact-1": Rule("sum-fact-1", "(sum ?R $x $y (* ?e1 ?e2))",
                       "(* ?e1 (sum ?R $x $y ?e2))",
                       conds=[(False, "$x", ["e1"]), (False, "$y", ["e1"])]),
}


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
        block = text[j:k + 1]
        if block.endswith(f':name "{name}")'):
            return block
        i = k + 1


# ---------------------------------------------------------------------- the cases
class Case:
    def __init__(self, name, rule, terms, probes, want, rounds=3):
        self.name = name
        self.rule = rule
        self.terms = list(terms)
        self.probes = list(probes)
        # the partition both sides must report, so a case that agrees on a
        # collapsed or empty answer still fails
        self.want = want
        self.rounds = rounds
        for t in self.terms + self.probes:
            check_term(t)

    def spec(self, with_rule=True):
        out = [f"rounds {self.rounds}"]
        out += [f"term {sexpr(t)}" for t in self.terms]
        if with_rule:
            out += self.rule.spec_lines()
        out += [f"probe {sexpr(t)}" for t in self.probes]
        return "\n".join(out) + "\n"

    def shifted(self, k):
        return Case(self.name + f"+{k}", self.rule,
                    [shift(t, k) for t in self.terms],
                    [shift(t, k) for t in self.probes], self.want, self.rounds)


def schedule(steps):
    return (f"(run-schedule (saturate (run slotted))\n"
            f"              (repeat {steps} (seq (run sdql) (saturate (run slotted)))))")


def egg_program(case, with_rule=True, mult=3):
    out = [f'(include "{MACHINERY}")', "(ruleset sdql)"]
    if with_rule:
        out.append(f";; {case.rule.name}")
        out.append(egg_rule(case.rule.name))
    # A slotted e-class is not one egglog e-class: two probes are in the same
    # slotted class when they reach a common leader.
    out += ["(ruleset probe)",
            "(relation ProbeId (U i64))",
            "(relation SameClass (i64 i64))",
            "(rule ((ProbeId a i) (ProbeId b j)\n"
            "       (RenamesToLeader a m1 l) (RenamesToLeader b m2 l))\n"
            "      ((SameClass i j)) :ruleset probe)"]
    for i, t in enumerate(case.terms):
        out.append(f"(let _t{i} {enc(t)})")
    for i, t in enumerate(case.probes):
        out.append(f"(let _p{i} {enc(t)})")
    out.append(schedule(case.rounds * mult))
    for i, _ in enumerate(case.probes):
        out.append(f"(ProbeId _p{i} {i})")
    out.append(schedule(case.rounds * mult))
    out.append("(run-schedule (saturate (run probe)))")
    out.append("(print-function SameClass 100000)")
    return "\n".join(out) + "\n"


def run_reference(case, with_rule=True):
    try:
        r = subprocess.run([str(XMULTI / "target" / "debug" / "xmulti")],
                           input=case.spec(with_rule), capture_output=True,
                           text=True, timeout=RUN_TIMEOUT)
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s")
    if r.returncode != 0:
        return ("ERROR", (r.stderr.strip().splitlines() or ["?"])[-1])
    part, sat = None, True
    for line in r.stdout.splitlines():
        if line.startswith("PARTITION "):
            part = line[len("PARTITION "):].strip()
        elif line.startswith("SATURATED "):
            sat = line.split()[1] == "yes"
    if part is None:
        return ("ERROR", "no PARTITION line")
    return ("OK" if sat else "UNSATURATED", part)


def run_encoding(case, with_rule=True, keep=None, mult=3):
    prog = egg_program(case, with_rule, mult)
    path = keep or (ROOT / f"xsdql-tmp-{os.getpid()}-{mult}.egg")
    path.write_text(prog)
    try:
        r = subprocess.run([str(EGGLOG), str(path)], capture_output=True,
                           text=True, timeout=RUN_TIMEOUT, cwd=ROOT)
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
        return [f"{case.name}: BASELINE differs (machinery, not the rule)\n"
                f"    ref {rv}\n    enc {ev}"]
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
    if rv != ev:
        fails.append(f"{case.name}: MISMATCH vs reference\n"
                     f"    ref {rv}\n    enc {ev}")
    if case.want is not None and rv != case.want and not fails:
        fails.append(f"{case.name}: both sides agree, but not on the expected "
                     f"partition\n    want {case.want}\n    got  {rv}")
    # A case whose rule never changed the partition compared the machinery, not the
    # rule -- and a "blocked" case that changed it never blocked anything.
    fired = rv != baseline
    if not fails and (case.want == FIRED) != fired:
        fails.append(f"{case.name}: the rule "
                     f"{'fired' if fired else 'did not fire'}, which is not what "
                     f"the case tests\n    baseline  {baseline}\n"
                     f"    with rule {rv}")

    # 2. the encoding at twice the steps: a moving answer means it had not settled,
    #    so the comparison was between two different amounts of work.
    if not fails:
        ds, dv = run_encoding(case, mult=6)
        if ds == "OK" and dv != ev:
            fails.append(f"{case.name}: encoding not settled or nondeterministic\n"
                         f"    {case.rounds * 3} steps {ev}\n"
                         f"    {case.rounds * 6} steps {dv}")

    # 3. slot-renaming invariance, per side.
    if shift_check and not fails:
        sh = case.shifted(40)
        xs, xv = run_reference(sh)
        ys, yv = run_encoding(sh)
        if xs in ("OK", "UNSATURATED") and xv != rv:
            fails.append(f"{case.name}: REFERENCE not slot-renaming invariant\n"
                         f"    {rv}\n    {xv}")
        if ys == "OK" and yv != ev:
            fails.append(f"{case.name}: ENCODING not slot-renaming invariant\n"
                         f"    {ev}\n    {yv}")
    if not fails:
        print(f"  ok  {case.name:<24} {'fired' if fired else 'NO-OP':<6} {rv}")
    return fails


# --------------------------------------------------------------------- shorthands
def V(n):
    return ("var", n)


FIRED = "[0,1][2] missing[[]]"
BLOCKED = "[0][1][2] missing[[]]"


def cases():
    out = []

    # --- a plain binary rule, and the symmetry it puts on the class.
    # The second child is a payload leaf, not a second variable: `(eq (var $1)
    # (var $2))` and `(eq (var $2) (var $1))` are ONE class before any rule runs,
    # since swapping two free slots is a renaming and the partition compares class
    # identity. That case tests nothing, so the children are made distinguishable.
    out.append(Case(
        "eq-comm", RULES["eq-comm"],
        [("eq", V(1), ("num", 5))],
        [("eq", V(1), ("num", 5)), ("eq", ("num", 5), V(1)),
         ("get", V(1), ("num", 5))],
        FIRED))

    # --- a payload literal the RIGHT-hand side builds: `(binop mult ?a ?b)`
    out.append(Case(
        "mult-app1", RULES["mult-app1"],
        [("mult", V(1), V(2))],
        [("mult", V(1), V(2)),
         ("binop", ("sym", "mult"), V(1), V(2)),
         ("binop", ("sym", "add"), V(1), V(2))],
        FIRED))

    # --- the payload symbol `add`, which is also an operator tag in `xmulti`'s
    # array language: without `SYM_PREFIX` the reference cannot parse this rule.
    out.append(Case(
        "add-app1", RULES["add-app1"],
        [("add", V(1), V(2))],
        [("add", V(1), V(2)),
         ("binop", ("sym", "add"), V(1), V(2)),
         ("binop", ("sym", "sub"), V(1), V(2))],
        FIRED))

    # --- a payload literal in a LEFT-hand child position, on a 3-child node
    out.append(Case(
        "mult-app2", RULES["mult-app2"],
        [("binop", ("sym", "mult"), V(1), V(2))],
        [("binop", ("sym", "mult"), V(1), V(2)),
         ("mult", V(1), V(2)),
         ("binop", ("sym", "add"), V(1), V(2))],
        FIRED))

    # --- and the same rule blocked by the payload: `add` is not `mult`.
    # The control cannot be the `mult` binop -- the rule fires on that one and it
    # would land in probe 1's class.
    out.append(Case(
        "mult-app2-blocked", RULES["mult-app2"],
        [("binop", ("sym", "add"), V(1), V(2))],
        [("binop", ("sym", "add"), V(1), V(2)),
         ("mult", V(1), V(2)),
         ("binop", ("sym", "sub"), V(1), V(2))],
        BLOCKED))

    # --- a `Num` literal in a left-hand child position, firing and blocked
    out.append(Case(
        "add-zero", RULES["add-zero"],
        [("add", V(1), ("num", 0))],
        [("add", V(1), ("num", 0)), V(1), ("add", V(1), ("num", 1))],
        FIRED))
    out.append(Case(
        "add-zero-blocked", RULES["add-zero"],
        [("add", V(1), ("num", 1))],
        [("add", V(1), ("num", 1)), V(1), ("add", V(1), ("num", 2))],
        BLOCKED))

    # --- arity 1, and a `Symbol` the right-hand side builds
    out.append(Case(
        "unique-app1", RULES["unique-app1"],
        [("unique", V(1))],
        [("unique", V(1)),
         ("apply", ("sym", "uniquef"), V(1)),
         ("apply", ("sym", "uniquefx"), V(1))],
        FIRED))

    # --- a nested left-hand side and a nested right-hand side over a `Num`
    out.append(Case(
        "get-range", RULES["get-range"],
        [("get", ("range", V(3), V(4)), V(7))],
        [("get", ("range", V(3), V(4)), V(7)),
         ("add", V(7), ("sub", V(3), ("num", 1))),
         ("add", V(7), ("sub", ("num", 1), V(3)))],
        FIRED))

    # --- a binder on the left AND two on the right, with `?f` over a payload class
    out.append(Case(
        "let-binop3", RULES["let-binop3"],
        [("let", V(1), 2, ("binop", ("sym", "mult"), V(2), V(3)))],
        [("let", V(1), 2, ("binop", ("sym", "mult"), V(2), V(3))),
         ("binop", ("sym", "mult"),
          ("let", V(1), 2, V(2)), ("let", V(1), 2, V(3))),
         ("binop", ("sym", "add"),
          ("let", V(1), 2, V(2)), ("let", V(1), 2, V(3)))],
        FIRED))

    # --- `Sum`: two binders on one node, and slot literals in child positions.
    # The control swaps the two `(var $)` children, which is a DIFFERENT term:
    # the bound slots are ordered, so no renaming turns one into the other.
    out.append(Case(
        "sum-sing", RULES["sum-sing"],
        [("sum", V(9), 5, 6, ("sing", V(5), V(6)))],
        [("sum", V(9), 5, 6, ("sing", V(5), V(6))),
         V(9),
         ("sum", V(9), 5, 6, ("sing", V(6), V(5)))],
        FIRED))

    # --- a right-hand side that builds a `Sum`, i.e. re-binds its two slots
    out.append(Case(
        "sum-fact-inv-1", RULES["sum-fact-inv-1"],
        [("mult", V(7), ("sum", V(1), 2, 3, ("get", V(2), V(3))))],
        [("mult", V(7), ("sum", V(1), 2, 3, ("get", V(2), V(3)))),
         ("sum", V(1), 2, 3, ("mult", V(7), ("get", V(2), V(3)))),
         ("sum", V(1), 2, 3, ("mult", ("get", V(2), V(3)), V(7)))],
        FIRED))

    # --- `Merge`: three binders on one node, six children, and a built `let`
    lhs = ("sum", V(1), 2, 3,
           ("sum", V(4), 5, 6,
            ("ifthen", ("eq", V(3), V(6)), ("get", V(2), V(5)))))
    rhs = ("merge", V(1), V(4), 2, 5, 3,
           ("let", V(3), 6, ("get", V(2), V(5))))
    # NOT the two ranges swapped: that is the free-slot renaming $1 <-> $4 of
    # probe 1, i.e. the same class. The two key binders swapped reorders the bound
    # slots against the body, which no renaming undoes.
    ctl = ("merge", V(1), V(4), 5, 2, 3,
           ("let", V(3), 6, ("get", V(2), V(5))))
    out.append(Case("sum-merge", RULES["sum-merge"], [lhs], [lhs, rhs, ctl], FIRED))

    # --- a slot-conditional rule, firing: `$x`,`$y` are not in `?e1`'s slots
    out.append(Case(
        "sum-fact-1-fires", RULES["sum-fact-1"],
        [("sum", V(1), 2, 3, ("mult", V(7), V(2)))],
        [("sum", V(1), 2, 3, ("mult", V(7), V(2))),
         ("mult", V(7), ("sum", V(1), 2, 3, V(2))),
         ("mult", V(2), ("sum", V(1), 2, 3, V(7)))],
        FIRED))

    # --- and blocked: `?e1` is the first bound slot's variable
    out.append(Case(
        "sum-fact-1-blocked", RULES["sum-fact-1"],
        [("sum", V(1), 2, 3, ("mult", V(2), V(7)))],
        [("sum", V(1), 2, 3, ("mult", V(2), V(7))),
         ("mult", V(2), ("sum", V(1), 2, 3, V(7))),
         ("mult", V(7), ("sum", V(1), 2, 3, V(2)))],
        BLOCKED))

    # --- blocked on the SECOND bound slot, which is the one an off-by-one misses
    out.append(Case(
        "sum-fact-1-blocked-y", RULES["sum-fact-1"],
        [("sum", V(1), 2, 3, ("mult", V(3), V(7)))],
        [("sum", V(1), 2, 3, ("mult", V(3), V(7))),
         ("mult", V(3), ("sum", V(1), 2, 3, V(7))),
         ("mult", V(7), ("sum", V(1), 2, 3, V(3)))],
        BLOCKED))

    return out


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "list":
        for c in cases():
            print(f"{c.name:<24} {c.want}")
            print(f"    {c.rule.name:<16} {ref_text(c.rule.lhs)}"
                  f"  ->  {ref_text(c.rule.rhs)}")
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
