"""Build differential-test programs through the production Rust CLI.

Most tests use the source language. Tests that inspect internal tables append
ordinary egglog observer rules to the CLI's desugared output.
"""

import json
import subprocess
import tempfile
from functools import cache, lru_cache
from pathlib import Path

import reference as ref

ROOT = Path(__file__).resolve().parents[1]
EGGLOG = ROOT / "target/debug/egglog-experimental"


@lru_cache(maxsize=32)
def compile_source(text):
    with tempfile.TemporaryDirectory(prefix="slotted-source-") as tmp:
        path = Path(tmp) / "source.egg"
        path.write_text(text)
        run = subprocess.run(
            [
                str(EGGLOG),
                "--slotted",
                "--mode",
                "desugar",
                str(path),
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if run.returncode:
            raise RuntimeError(f"Rust compilation failed:\n{run.stderr}\nSource:\n{text}")
        return run.stdout


def term(lang, t):
    """A generated ground term in the public source language."""
    if t[0] == "var":
        return f"${t[1]}"
    op = lang[t[0]]
    kids, pays = op.split(t[1:])
    return node(op, [f"${lang.slot(k)}" if i in op.binders else term(lang, k) for i, k in enumerate(kids)], pays)


def node(op, kids, pays):
    parts = [op.ctor]
    kids, pays = iter(kids), iter(pays)
    for col in op.sig:
        if col in ref.SLOTTED:
            parts.append(next(kids))
        else:
            value = next(pays)
            if isinstance(value, tuple):
                tag, value = value
                if tag == "plit" and col == "String":
                    value = json.dumps(value)
            parts.append(str(value))
    return "(" + " ".join(parts) + ")"


def pattern(lang, t):
    if t[0] in ("pv", "sl"):
        return t[1]
    if t[0] == "cls":
        return term(lang, t[1])
    if t[0] == ref.SUBST:
        return "(subst " + " ".join(pattern(lang, a) for a in t[1:]) + ")"
    op = lang[t[0]]
    kids, pays = op.split(t[1:])
    return node(op, [pattern(lang, k) for k in kids], pays)


def rewrite(lang, atoms, root, rhs, *, conds=(), fresh=(), name=None, lead=0):
    """Spell a generated conjunctive rule as a source rewrite with side patterns."""
    facts = []
    for r, op, kids, *payloads in atoms:
        pays = payloads[0] if payloads else lang[op].pays
        facts.append(f"(= {r} {node(lang[op], [pattern(lang, k) for k in kids], pays)})")
    facts.extend(f"({'free' if want else 'not-free'} {slot} {' '.join(pvars)})" for want, slot, pvars in conds)
    options = f" :when ({' '.join(facts)}) :lead {lead}"
    if fresh:
        options += " :fresh " + " ".join(fresh)
    if name:
        options += " :name " + json.dumps(name)
    return f"(rewrite {root} {pattern(lang, rhs)}{options})"


@cache
def machinery(language):
    return compile_source(f'(include "slotted/languages/{language}.egg")')


@lru_cache(maxsize=1)
def maintenance():
    """Use the compiler's actual maintenance schedule in internal-table tests."""
    text = compile_source('(include "slotted/languages/toy.egg")\n(run 0)')
    return ref.render(next(f for f in ref.parse(text) if f[0] == "run-schedule"))


def program(language, lang, rules, terms, unions, probes, rounds, *, defer_probes=False):
    source = [f'(include "slotted/languages/{language}.egg")', *dict.fromkeys(rules)]
    source.extend(f"(let _t{i} {term(lang, t)})" for i, t in enumerate(terms))
    source.extend(f"(union {term(lang, a)} {term(lang, b)})" for a, b in unions)
    # A bare slot has no source-level global representation. The partition
    # observer needs only its class, which is the canonical variable node.
    var = f"({lang.symbols_for(lang.default_sort).var} 0)"
    probe_terms = [var if t[0] == "var" else f"(let _p{i} {term(lang, t)})" for i, t in enumerate(probes)]
    if not defer_probes:
        source.extend(probe_terms)
    source.append(f"(run {rounds})")
    if defer_probes:
        source.extend(probe_terms)
    source.append("(run 0)")
    encoded = compile_source("\n".join(source))
    # Observations run after the budget, without another rewrite or maintenance round.
    observer = [
        """
(ruleset probes)
(relation ProbeId (U i64))
(relation SameClass (i64 i64))
(rule ((ProbeId a i) (ProbeId b j)
       (RenamesToLeader_0 a m1 l) (RenamesToLeader_0 b m2 l))
      ((SameClass i j)) :ruleset probes)
"""
    ]
    observer.extend(f"(ProbeId {var if t[0] == 'var' else f'$_p{i}'} {i})" for i, t in enumerate(probes))
    observer += ["(run-schedule (saturate (run probes)))", "(print-function SameClass 100000)"]
    return encoded + "\n".join(observer) + "\n"
