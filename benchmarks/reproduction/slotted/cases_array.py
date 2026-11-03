"""Frozen regression case data and renderers, retained for explicit reproduction."""

from . import array as benchmark
from . import differential_source as driver
from . import reference as syntax

ARRAY_SRC = benchmark.SOURCE

ARRAY_SRC_RULES = benchmark.RULES

LANG = benchmark.LANG

sexpr, shift = LANG.sexpr, LANG.shift

MAP = ("Sym", "map")


class Case:
    lang = LANG

    def egg_program(self, *, mult):
        return egg_program(self, mult=mult)

    def __init__(self, name, terms, rules, probes, rounds=8, unions=()):
        self.name = name
        self.terms = list(terms)
        self.rules = list(rules)
        self.probes = list(probes)
        self.rounds = rounds
        self.unions = list(unions)

    def spec(self, include_probes=True):
        return driver.reference_spec(
            LANG,
            self.rounds,
            self.terms,
            self.unions,
            [line for r in self.rules for line in r.spec_lines()],
            self.probes if include_probes else [],
        )

    def shifted(self, k):
        return Case(
            self.name + f"+{k}",
            [shift(t, k) for t in self.terms],
            self.rules,
            [shift(t, k) for t in self.probes],
            self.rounds,
            [(shift(a, k), shift(b, k)) for a, b in self.unions],
        )


def egg_program(case, atom_order=None, mult=3, defer_probes=False):
    return driver.program(
        "array",
        LANG,
        [r.source(first_atom=atom_order) for r in case.rules],
        case.terms,
        case.unions,
        case.probes,
        case.rounds * mult,
        defer_probes=defer_probes,
    )


RULES = driver.load_rules(ARRAY_SRC_RULES, LANG)

ALL_RULES = list(RULES.values())


def V(n):
    return ("var", n)


def S(n):
    return ("Sym", n)


def A(*xs):
    """Left-nested application: A(f, a, b) = (app (app f a) b)."""
    out = xs[0]
    for x in xs[1:]:
        out = ("App", out, x)
    return out


def MAPPED(f, arg):
    return A(MAP, f, arg)


def per_rule_cases():
    """Each of the 8 rules firing on a small term, and each guarded rule blocked.

    The probes are always the pattern instance and the term the rule would produce,
    so a rule that fires merges them and a rule that is blocked does not. Symbol
    names avoid `f`, `g`, `h`, `k`, `sub`, `sub2`, `add`: those are operators of the
    oracle's existing toy language, and the reference's parser tries them as
    operators before it tries `Symbol`.
    """
    cs = []

    # -- eta ---------------------------------------------------------------
    #  (lam $0 (app f1 (var $0))) = f1
    cs.append(
        Case(
            "eta-fires",
            [("Lam", 0, ("App", S("f1"), V(0)))],
            [RULES["eta"]],
            [("Lam", 0, ("App", S("f1"), V(0))), S("f1"), S("f2")],
        )
    )
    # blocked: the bound slot is free in the function position, so eta would
    # capture it
    cs.append(
        Case(
            "eta-blocked",
            [("Lam", 0, ("App", ("App", S("f1"), V(0)), V(0)))],
            [RULES["eta"]],
            [("Lam", 0, ("App", ("App", S("f1"), V(0)), V(0))), ("App", S("f1"), V(0)), ("App", S("f1"), S("cc"))],
        )
    )

    # -- let-intro ---------------------------------------------------------
    cs.append(
        Case(
            "let-intro",
            [("App", ("Lam", 0, ("App", S("f1"), V(0))), S("aa"))],
            [RULES["let-intro"]],
            [
                ("App", ("Lam", 0, ("App", S("f1"), V(0))), S("aa")),
                ("Let", 0, ("App", S("f1"), V(0)), S("aa")),
                ("Let", 0, ("App", S("f1"), V(0)), S("bb")),
            ],
        )
    )

    # -- let-unused --------------------------------------------------------
    cs.append(
        Case(
            "let-unused-fires",
            [("Let", 0, ("App", S("f1"), S("cc")), S("aa"))],
            [RULES["let-unused"]],
            [("Let", 0, ("App", S("f1"), S("cc")), S("aa")), ("App", S("f1"), S("cc")), ("App", S("f1"), S("dd"))],
        )
    )
    cs.append(
        Case(
            "let-unused-blocked",
            [("Let", 0, ("App", S("f1"), V(0)), S("aa"))],
            [RULES["let-unused"]],
            [("Let", 0, ("App", S("f1"), V(0)), S("aa")), ("App", S("f1"), V(0)), ("App", S("f1"), S("cc"))],
        )
    )

    # -- let-var-same ------------------------------------------------------
    cs.append(
        Case(
            "let-var-same-fires",
            [("Let", 0, V(0), S("aa"))],
            [RULES["let-var-same"]],
            [("Let", 0, V(0), S("aa")), S("aa"), S("bb")],
        )
    )
    # blocked: `$x` is written twice, so the binder and the body's variable have
    # to be the same slot -- here they are not
    cs.append(
        Case(
            "let-var-same-blocked",
            [("Lam", 1, ("Let", 0, V(1), S("aa")))],
            [RULES["let-var-same"]],
            [("Lam", 1, ("Let", 0, V(1), S("aa"))), ("Lam", 1, S("aa")), ("Lam", 1, V(1))],
        )
    )

    # -- let-app -----------------------------------------------------------
    cs.append(
        Case(
            "let-app-fires",
            [("Let", 0, ("App", V(0), S("cc")), S("aa"))],
            [RULES["let-app"]],
            [
                ("Let", 0, ("App", V(0), S("cc")), S("aa")),
                ("App", ("Let", 0, V(0), S("aa")), ("Let", 0, S("cc"), S("aa"))),
                ("App", S("cc"), S("aa")),
            ],
        )
    )
    # blocked: the bound slot is free in NEITHER child of the application
    cs.append(
        Case(
            "let-app-blocked",
            [("Let", 0, ("App", S("dd"), S("cc")), S("aa"))],
            [RULES["let-app"]],
            [
                ("Let", 0, ("App", S("dd"), S("cc")), S("aa")),
                ("App", ("Let", 0, S("dd"), S("aa")), ("Let", 0, S("cc"), S("aa"))),
                ("App", S("dd"), S("cc")),
            ],
        )
    )

    # -- let-lam-diff ------------------------------------------------------
    cs.append(
        Case(
            "let-lam-diff-fires",
            [("Let", 0, ("Lam", 1, ("App", V(1), V(0))), S("aa"))],
            [RULES["let-lam-diff"]],
            [
                ("Let", 0, ("Lam", 1, ("App", V(1), V(0))), S("aa")),
                ("Lam", 1, ("Let", 0, ("App", V(1), V(0)), S("aa"))),
                ("Lam", 1, ("App", V(1), S("aa"))),
            ],
        )
    )
    # blocked: the outer bound slot is not free in the inner lambda's body
    cs.append(
        Case(
            "let-lam-diff-blocked",
            [("Let", 0, ("Lam", 1, ("App", V(1), S("cc"))), S("aa"))],
            [RULES["let-lam-diff"]],
            [
                ("Let", 0, ("Lam", 1, ("App", V(1), S("cc"))), S("aa")),
                ("Lam", 1, ("Let", 0, ("App", V(1), S("cc")), S("aa"))),
                ("Lam", 1, ("App", V(1), S("cc"))),
            ],
        )
    )

    # -- map-fusion --------------------------------------------------------
    cs.append(
        Case(
            "map-fusion",
            [MAPPED(S("f1"), MAPPED(S("f2"), S("arr")))],
            [RULES["map-fusion"]],
            [
                MAPPED(S("f1"), MAPPED(S("f2"), S("arr"))),
                MAPPED(("Lam", 0, ("App", S("f1"), ("App", S("f2"), V(0)))), S("arr")),
                MAPPED(("Lam", 0, ("App", S("f2"), ("App", S("f1"), V(0)))), S("arr")),
            ],
            rounds=4,
        )
    )

    # -- map-fission -------------------------------------------------------
    cs.append(
        Case(
            "map-fission-fires",
            [("App", MAP, ("Lam", 0, ("App", S("f1"), ("App", S("f2"), V(0)))))],
            [RULES["map-fission"]],
            [
                ("App", MAP, ("Lam", 0, ("App", S("f1"), ("App", S("f2"), V(0))))),
                ("Lam", 1, MAPPED(S("f1"), MAPPED(("Lam", 0, ("App", S("f2"), V(0))), V(1)))),
                ("Lam", 1, MAPPED(S("f2"), MAPPED(("Lam", 0, ("App", S("f1"), V(0))), V(1)))),
            ],
            rounds=3,
        )
    )
    # blocked: the lambda's bound slot is free in ?f, so fissioning there would
    # let it escape -- probe 1 is exactly the term with the escaped slot
    cs.append(
        Case(
            "map-fission-blocked",
            [("App", MAP, ("Lam", 0, ("App", ("App", S("f1"), V(0)), S("f2"))))],
            [RULES["map-fission"]],
            [
                ("App", MAP, ("Lam", 0, ("App", ("App", S("f1"), V(0)), S("f2")))),
                ("Lam", 1, MAPPED(("App", S("f1"), V(0)), MAPPED(("Lam", 0, S("f2")), V(1)))),
                ("App", MAP, ("Lam", 0, ("App", ("App", S("f1"), V(0)), S("f3")))),
            ],
            rounds=3,
        )
    )

    return cs


def goal_cases(n_params=(0, 1), rounds=8, wrap_lams=True, nfun=4, dims=2):
    """Test wrappers around the shared Figure 8 input and target generator."""
    cases = []
    for n in n_params:
        start, target = benchmark.goal(n, wrap_lams=wrap_lams, nfun=nfun, dims=dims)
        tag = "" if wrap_lams else "-free"
        name = f"goal{tag}-{dims}d-{nfun}f-N{n}"
        cases.append(Case(name, [start], list(ALL_RULES), [start, target], rounds=rounds))
    return cases


def _artifact_goal_text(o):
    """Literal transcription of artifact commit 83f2e5b's `gen.py` for N=2,M=2."""
    fresh = [0]

    def fresh_slot():
        fresh[0] += 1
        return f"${fresh[0]}"

    def fn_with_args(f):
        for i in range(1, o + 1):
            f = f"(app {f} (var $p{i}))"
        return f

    def chained(indices):
        fs = [fn_with_args(f"(var $fn{i})") for i in indices]
        if len(fs) == 1:
            return fs[0]
        x = fresh_slot()
        out = f"(var {x})"
        for fn in fs:
            out = f"(app {fn} {out})"
        return f"(lam {x} {out})"

    def maps(t):
        for _ in range(2):
            t = f"(app map {t})"
        return t

    def wrap(t):
        for i in reversed(range(1, o + 1)):
            t = f"(lam $p{i} {t})"
        for i in reversed(range(1, 5)):
            t = f"(lam $fn{i} {t})"
        return t

    lhs = wrap(maps(chained(range(1, 5))))
    left, right = maps(chained(range(3, 5))), maps(chained(range(1, 3)))
    x = fresh_slot()
    rhs = wrap(f"(lam {x} (app {left} (app {right} (var {x}))))")
    return lhs, rhs


def _alpha_shape(text):
    """A binder-name-free tree, sufficient to compare closed artifact terms."""
    tree = syntax.parse(text)[0]
    counter = [0]

    def go(term, env):
        if not isinstance(term, list):
            return term
        if term and term[0] == "lam":
            counter[0] += 1
            name = f"b{counter[0]}"
            nested = dict(env)
            nested[term[1]] = name
            return "lam", name, go(term[2], nested)
        if term and term[0] == "var":
            return "var", env.get(term[1], f"free:{term[1]}")
        return tuple(go(part, env) for part in term)

    return go(tree, {})


def unbound_cases():
    """Small shapes that are not one of the 8 rules but sit next to them, where
    the two sides might reasonably differ."""
    cs = []
    # A `let` whose bound slot is ALSO free in the value. `Bind` hides the slot
    # from the body only, so both implementations must keep it free and agree.
    #   let x = x in f1 x      -- the value's `x` is the AMBIENT one, the body's is
    # the bound one. `Bind` covers the body column only. Probing that needs a parent
    # that can see the difference: two applications that differ only in whether the
    # `let`'s slot and the argument's slot coincide.
    B = ("App", S("f1"), V(0))
    L = ("Let", 0, B, V(0))
    cs.append(
        Case(
            "let-slot-free-in-value",
            [("App", L, V(0)), ("App", L, V(1))],
            [RULES["let-unused"]],
            [("App", L, V(0)), ("App", L, V(1)), ("App", L, S("cc"))],
        )
    )
    return cs


SYMS = ["map", "f1", "f2", "aa", "cc"]
