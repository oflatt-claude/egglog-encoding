#!/usr/bin/env python3
"""Does the encoding partition the reference's terms the way the reference does?

`isomorphism.py` asks for the whole graph -- every class's slots, group and nodes, with
a witness -- and that fails as soon as the two sides keep different NODES for the same
classes, which the encoding does in two known ways: a slot a node carries that its class
does not unifies with another occurrence, where the reference gives it a fresh name and
finds no match; and a node row is kept once per reading of a symmetric child through a
bound slot, where the reference keeps one. Neither changes which terms are equal.

This asks the weaker question that still matters. For every node of every reference
class, the term through that node -- its children spelled by their smallest terms -- is
added to the encoding's FINISHED graph with the machinery alone, and the encoding's
equivalence over those terms is compared with the reference's:

- a reference class whose probes land in several encoding classes is SPLIT: the
  encoding did not identify terms the reference did;
- an encoding class hit by probes of several reference classes MERGED them: the
  encoding identified terms the reference did not.

Neither says which side is right -- a split is a derivation the reference found and
the encoding did not, or one the reference cannot make, and a merge the converse -- so
both are reported, and a change on either side shows.
"""

import re
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
slotenc = __import__("slotted-encoder")

INF = 10**9


def reference_terms(g, lang):
    """One tuple term per reference node: the node over its children's smallest terms.

    Terms use the language's Python spelling: `(op, arg...)`, a binder argument as its
    slot number, `(lang.VAR, n)` for a variable, a payload leaf as `(op, value)`. The
    variable class gets no probe, since a bare slot is not a term of its own; a class
    with no finite term (only nodes through itself) gets none either.
    """
    by_tag = {op.ref: op for op in lang.ops.values() if op.ref}
    # a payload leaf is printed as its payload, behind the prefix its `.ref` line gives
    by_prefix = sorted(
        ((op.ref_prefix or "", op) for op in lang.ops.values() if op.ref is None), key=lambda x: -len(x[0])
    )

    def leaf(tag):
        return tag == "var" or tag not in by_tag

    def node_size(elems, size):
        return 1 + sum(size[e[1]] for e in elems if e[0] == "child")

    size = {c: INF for c in g.ids()}
    changed = True
    while changed:
        changed = False
        for c in g.ids():
            for tag, elems in g.nodes[c]:
                s = 1 if leaf(tag) else node_size(elems, size)
                if s < size[c]:
                    size[c], changed = s, True

    def best(c):
        return min(g.nodes[c], key=lambda n: (1 if leaf(n[0]) else node_size(n[1], size), str(n)))

    counter = [10000]

    def fresh():
        counter[0] += 1
        return counter[0]

    def payload(tag):
        prefix, op = next((prefix, op) for prefix, op in by_prefix if tag.startswith(prefix))
        text = tag[len(prefix) :]
        return (op.name, int(text) if "i64" in op.sig else text)

    def node_term(node, ren):
        tag, elems = node
        if tag == "var":
            return (lang.VAR, ren[elems[0][1]])
        if tag not in by_tag:
            return payload(tag)
        op = by_tag[tag]
        local, extra, args = {}, {}, []
        for e, _kind in zip(elems, op.arg_kinds(), strict=True):
            if e[0] == "slot":
                # a binder: the node's own slot, fresh here
                b = fresh()
                local[e[1]] = b
                args.append(b)
            else:
                _, kid, edge = e
                ren2 = {}
                for cs, ps in edge:
                    # a slot the node carries that its class does not: fresh, once per node
                    ren2[cs] = ren[ps] if ps in ren else local[ps] if ps in local else extra.setdefault(ps, fresh())
                for cs in g.slots[kid]:
                    ren2.setdefault(cs, fresh())
                args.append(class_term(kid, ren2))
        return (op.name, *args)

    def class_term(c, ren):
        if size[c] >= INF:
            raise ValueError(f"{c}: no finite term")
        return node_term(best(c), ren)

    out = []
    for c in g.ids():
        base = {s: fresh() for s in g.slots[c]}
        for k, node in enumerate(g.nodes[c]):
            if node[0] == "var":
                continue
            try:
                out.append((c, k, node_term(node, dict(base))))
            except ValueError:
                continue
    return out


def probe_lines(terms, lang, renames, sort="U", declared=False):
    """The egglog that installs the probes after the run and prints the equivalence.

    `renames` is the carrier's `RenamesToLeader` relation; `declared` says the program
    already has the `probe` ruleset and its two relations. Only the machinery and the
    probe rule run: the user rules get no further budget.
    """
    out = []
    if not declared:
        out += [
            "(ruleset probe)",
            f"(relation ProbeId ({sort} i64))",
            "(relation SameClass (i64 i64))",
            f"(rule ((ProbeId a i) (ProbeId b j) ({renames} a m1 l) ({renames} b m2 l))"
            " ((SameClass i j)) :ruleset probe)",
        ]
    # the constructor tables' sizes before and after: a probe whose node the graph
    # already holds, in any reading, adds no row once the machinery has folded it
    out.append("(print-size)")
    for i, (_, _, t) in enumerate(terms):
        out.append(f"(let _probe{i} {lang.enc(t)})")
    for i in range(len(terms)):
        out.append(f"(ProbeId _probe{i} {i})")
    out += [
        f"(run-schedule {slotenc.MACHINERY_SCHEDULE} (saturate (run probe)))",
        "(print-size)",
        "(print-function SameClass 1000000)",
    ]
    return out


def rows_added(stdout, lang):
    """How many constructor rows the probes left behind, from the two `print-size`
    listings around them: none when every probed node was already there."""
    ctors = {op.ctor for op in lang.ops.values()}
    sizes = [
        (name, int(n))
        for name, n in re.findall(r"\((\S+) (\d+)\)", stdout)
        if name in ctors or re.fullmatch(r"SlottedVar_\d+", name)
    ]
    if not sizes or len(sizes) % 2:
        return None
    half = len(sizes) // 2
    before, after = dict(sizes[:half]), dict(sizes[half:])
    return sum(after[k] - before.get(k, 0) for k in after)


def partition(terms, stdout):
    """The two partitions of the probes, from the printed `SameClass` relation."""
    parent = list(range(len(terms)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for m in re.finditer(r"\(SameClass (\d+) (\d+)\)", stdout):
        a, b = find(int(m.group(1))), find(int(m.group(2)))
        if a != b:
            parent[max(a, b)] = min(a, b)
    by_ref, by_enc = defaultdict(set), defaultdict(set)
    for i, (c, _, _) in enumerate(terms):
        by_ref[c].add(find(i))
        by_enc[find(i)].add(c)
    return {
        "classes": len(by_ref),
        "hit": len(by_enc),
        "split": {c: e for c, e in by_ref.items() if len(e) > 1},
        "merged": {e: cs for e, cs in by_enc.items() if len(cs) > 1},
    }


def verdict(p, added=None, same_size=False):
    """One phrase for a report cell.

    `same rows`: the partitions agree, every reference node is already a row of the
    encoding's graph in some reading, and the two graphs have the same number of rows
    -- so each class holds the reference's rows and no others: the same e-graph, found
    without a witness search.
    """
    if not p["split"] and not p["merged"]:
        return "same rows" if added == 0 and same_size else "same partition"
    return f"split {len(p['split'])}, merged {len(p['merged'])}"
