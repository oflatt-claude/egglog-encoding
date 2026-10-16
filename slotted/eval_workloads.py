"""Prepare the paper workloads once, before timing or cache lookup.

Each workload has a source program with a goal check, an input-only program for
graph export, and reference specs for the two matchers. These are plain data so
serial and spawned-worker evaluation consume exactly the same inputs.
"""

import json
from dataclasses import dataclass
from pathlib import Path

import paper_fixtures as pf
import reference as syntax
import xarray as XA

ROOT = Path(__file__).resolve().parents[1]
BATAX_SUBSET = ROOT / "slotted" / "tests" / "sdql-paper-batax.egg"


@dataclass(frozen=True)
class Workload:
    study: str
    case: str
    rounds: int
    rules: int | None
    program: str
    graph_program: str
    multi: str
    nested: str
    paper: tuple[int, int, int, bool] | None = None

    @property
    def lang(self):
        # Language descriptors contain identity-based sentinels; reconstruct them
        # in each worker rather than pickling them with the generated programs.
        return XA.LANG if self.study == "array" else pf.reference_language()

    def reference(self, side):
        return self.multi if side == "ref-multi" else self.nested


def prepare(task, *, rounds=None, rules=44):
    study, case = task
    if study == "array":
        return array_workload(case, rounds=6 if rounds is None else rounds)
    return sdql_workload(*case, rules=rules, rounds=rounds)


def ctor_lines(lang):
    """`ctor <tag> <Name>` lines: what the encoding calls each of the oracle's constructors,
    so the oracle's substitution snapshot breaks ties by the same spelling."""
    out = []
    for op in {id(op): op for op in lang.ops.values()}.values():
        if op.ref:
            out.append(f"ctor {op.ref} {op.ctor}")
        else:
            out.append(f"ctor {'symbol' if 'String' in op.sig else 'number'} {op.ctor}")
    return sorted(out)


def rule_lines(lang, rules_path, selected, nested):
    """A rule file's rules as oracle spec lines, flattened or nested."""
    src = syntax.Source(rules_path)
    out = []
    for form in syntax.parse(rules_path.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        r = syntax.rewrite_parts(src, form)
        if selected is not None and r["name"] not in selected:
            continue
        lhs = src.term(r["lhs"], ground=False)
        rhs = syntax.pat_sexpr(lang, syntax.rhs_of(lang, src.term(r["rhs"], ground=False)))
        if nested:
            out += ["rule", f"nested {syntax.pat_sexpr(lang, syntax.rhs_of(lang, lhs))}", f"rhs root {rhs}"]
        else:
            root, atoms = syntax.flatten(lang, lhs)
            root, atom_text = syntax.atom_lines(lang, root, atoms)
            out += ["rule", *atom_text, f"rhs {root} {rhs}"]
        for want, slot, pvars in r["conds"]:
            out.append(f"cond {'in' if want else 'notin'} {slot} {' '.join(pvars)}")
    return out


def array_program(case, *, with_target):
    """Source terms and the shared eight-rule library; Rust performs the encoding."""

    def term(t):
        if t[0] == "var":
            return f"${t[1]}"
        op = XA.LANG.ops[t[0]]
        args = []
        for kind, arg in zip(op.arg_kinds(), t[1:], strict=True):
            if kind is syntax.CHILD:
                args.append(term(arg))
            elif kind is syntax.BINDER:
                args.append(f"${XA.LANG.slot(arg)}")
            else:
                args.append(json.dumps(arg))
        return "(" + " ".join([op.ctor, *args]) + ")"

    lines = ['(include "slotted/languages/array-rules.egg")']
    lines += [f"(let input{i} {term(t)})" for i, t in enumerate(case.terms)]
    lines += [f"(union {term(a)} {term(b)})" for a, b in case.unions]
    lines.append(f"(run {case.rounds})")
    if with_target:
        a, b = case.probes
        lines.append(f"(check (= {term(a)} {term(b)}))")
    return "\n".join(lines) + "\n"


def array_workload(n, *, rounds=6):
    case = XA.goal_cases([n], rounds=rounds)[0]
    start, target = case.probes
    head = [f"rounds {rounds}", *ctor_lines(XA.LANG), f"term {XA.sexpr(start)}"]
    goal = [f"goal {XA.sexpr(target)}"]
    multi = [line for rule in case.rules for line in rule.spec_lines()]
    nested = rule_lines(XA.LANG, XA.ARRAY_SRC_RULES, None, nested=True)
    return Workload(
        study="array",
        case=case.name,
        rounds=rounds,
        rules=None,
        program=array_program(case, with_target=True),
        graph_program=array_program(case, with_target=False),
        multi="\n".join(head + multi + goal) + "\n",
        nested="\n".join(head + nested + goal) + "\n",
    )


def sdql_program(kernel, phase, rules, rounds, with_target):
    """One workload as a slotted source: the full library by include, or BATAX's own 12."""
    if rules == 12:
        # the goal-directed test, its own rules and schedule; only its terms are reused
        forms = syntax.parse(BATAX_SUBSET.read_text())
        forms = [["run", str(rounds)] if f[:1] == ["run"] and f[1] != "0" else f for f in forms]
    else:
        forms = pf.test_forms(kernel, phase, rounds)
    if not with_target:
        # the saturated input alone, for counting: no target, no check
        forms = [f for f in forms if f[0] != "check" and f[:2] != ["let", "paper-target"]]
    return "\n".join(syntax.render(f) for f in forms) + "\n"


def sdql_workload(kernel, phase, *, rules=44, rounds=None):
    lang = pf.reference_language()
    start, target = pf.workload_text(kernel, phase, syntax.Source(pf.RULES), lang)
    budget = pf.iteration_limit(kernel, phase) if rounds is None else rounds
    selected = None
    if rules == 12:
        subset = syntax.Source(BATAX_SUBSET)
        selected = {syntax.rule_name(subset, f) for f in syntax.parse(BATAX_SUBSET.read_text()) if f[:1] == ["rewrite"]}
    head = [f"rounds {budget}", *ctor_lines(lang), f"term {start}"]
    goal = [f"goal {target}"]
    multi = rule_lines(lang, pf.RULES, selected, nested=False)
    nested = rule_lines(lang, pf.RULES, selected, nested=True)
    return Workload(
        study="sdql",
        case=f"{kernel}_{phase}-{rules}rules",
        rounds=budget,
        rules=rules,
        program=sdql_program(kernel, phase, rules, budget, True),
        graph_program=sdql_program(kernel, phase, rules, budget, False),
        multi="\n".join(head + multi + goal) + "\n",
        nested="\n".join(head + nested + goal) + "\n",
        paper=pf.TABLE1[(kernel, phase)],
    )
