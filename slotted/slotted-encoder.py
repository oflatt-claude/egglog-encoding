#!/usr/bin/env python3
"""Generate the slotted e-graph encoding from typed constructors and rules.

The implementation has four layers: constructor signatures, invariant-maintenance
rules, term encoding, and MultiPattern rule encoding. Each equality-sort carrier has
its own `CarrierSymbols`; renaming maps and layout metadata are shared.

The executable derivation and worked examples live in
`slotted/ENCODING.md`. This module keeps only the invariants needed beside
their implementation.
"""

import hashlib
import re
from dataclasses import dataclass

CHILD = object()  # a slotted child: `Renaming U`
BINDER = object()  # a slotted child that also binds its slot

SLOTTED = (CHILD, BINDER)


@dataclass(frozen=True)
class CarrierSymbols:
    """Generated constructor and relation names for one equality sort."""

    sort: str
    var: str
    renames: str
    equated: str
    class_slots: str
    subst_pending: str

    @classmethod
    def create(cls, sort, index):
        return cls(
            sort,
            f"SlottedVar_{index}",
            f"RenamesToLeader_{index}",
            f"Equated_{index}",
            f"ClassSlots_{index}",
            f"SubstPending_{index}",
        )


def carrier_symbols(sorts):
    """The table names for one declared equality sort, in declaration order.

    Indexed whether a program declares one sort or ten, so adding a second sort to a
    working program does not rename the tables its first one compiled to.
    """
    return {sort: CarrierSymbols.create(sort, i) for i, sort in enumerate(tuple(sorts))}


###############################################################################
# language specs
###############################################################################


def read_language(path, sorts=("U",)):
    """Parse annotated constructor declarations.

        (constructor Lam (U U) U :binder 0)
        (constructor Sum (U U U U) U :binder 1 2)
        (constructor Num (i64) U)

    A `U` column is a slotted child and expands to `Renaming U`; anything else is a
    payload and passes through. `:binder` names the child positions -- counted over
    children, not over columns -- whose slot the node binds. This is the syntax the
    encoder recognises today; the intent is for egglog-experimental to accept it and
    strip it on the way down to core egglog, where nothing about a binder is
    primitive.
    """
    language = {}
    for raw in path.read_text().splitlines():
        line = raw.split(";")[0].strip()
        if not line.startswith("(constructor "):
            continue
        head, _, rest = line[len("(constructor ") :].partition("(")
        cols_text, _, tail = rest.partition(")")
        name = head.strip()
        # `tail` is the output sort, then the options, then the closing paren
        tokens = tail.rstrip(")").split()
        opts = next((i for i, t in enumerate(tokens) if t.startswith(":")), len(tokens))
        language[name] = signature(cols_text.split(), constructor_options(name, tokens[opts:]), sorts, name)
    return language


#: egglog's own `(constructor ...)` options. Recognised so they can be refused by name
#: rather than ignored: extraction here does not honour them, and a silently dropped
#: `:cost` leaves a program doing something other than what it says.
EGGLOG_CTOR_OPTIONS = (":cost", ":unextractable", ":internal-term-constructor")


def constructor_options(name, tokens):
    """The binder positions a constructor's options declare.

    `:binder <pos>...` is this language's one addition to egglog's constructor options,
    and may stand anywhere among them. egglog's own are refused by name.
    """
    binders, seen = [], None
    for tok in tokens:
        if isinstance(tok, str) and tok.startswith(":"):
            if tok in EGGLOG_CTOR_OPTIONS:
                raise SystemExit(
                    f"constructor {name}: `{tok}` is egglog's and is not implemented here. "
                    "Extraction over the encoding would not honour it, so it is refused "
                    "rather than dropped in silence."
                )
            if tok != ":binder":
                raise SystemExit(f"constructor {name}: unknown option `{tok}`")
            seen = tok
            continue
        if seen == ":binder":
            binders.append(int(tok))
    return binders


def signature(cols, binders, sorts=("U",), name="constructor"):
    """Columns and the binding child positions as the encoder's signature.

    A column whose sort is one the program DECLARED is a slotted child and expands to
    `Renaming <sort>`; anything else -- `i64`, `String`, a primitive -- is a payload and
    passes through. `sorts` defaults to the carrier the hand-written core declares.
    """
    child_count = sum(col in sorts for col in cols)
    if len(set(binders)) != len(binders):
        raise SystemExit(f"constructor {name}: duplicate `:binder` position")
    if any(pos < 0 or pos >= child_count for pos in binders):
        raise SystemExit(f"constructor {name}: `:binder` position is outside its {child_count} child columns")
    if binders:
        lo, hi = min(binders), max(binders)
        if sorted(binders) != list(range(lo, hi + 1)):
            raise SystemExit(f"constructor {name}: `:binder` positions must be contiguous")
        if hi + 1 >= child_count:
            raise SystemExit(f"constructor {name}: `:binder` columns must be followed by the child they cover")

    sig, seen_kids = [], 0
    for col in cols:
        if col in sorts:
            sig.append(BINDER if seen_kids in binders else CHILD)
            seen_kids += 1
        else:
            sig.append(col)
    return sig


def read_typed_language_form(form, sorts=("U",)):
    """One constructor declaration with the sort information the generic recipe erases.

    Returns ``(name, signature, output_sort, child_sorts)``.  ``signature`` remains
    the historical CHILD/BINDER/payload walk, while ``child_sorts`` records the
    equality sort of each slotted column.  Keeping both lets the existing term and
    rule algorithms stay structural while multi-sort emission selects the right
    per-sort tables at every edge.
    """
    assert form[0] == "constructor" and isinstance(form[2], list), form
    name, cols, output = form[1], form[2], form[3]
    if output not in sorts:
        raise SystemExit(
            f"constructor {name}: output sort {output!r} is not one of the declared equality sorts ({', '.join(sorts)})"
        )
    sig = signature(cols, constructor_options(name, form[4:]), sorts, name)
    return name, sig, output, tuple(col for col in cols if col in sorts)


def read_correspondence(path):
    """Parse a `.ref` file: how a language's operators are spelled by the reference.

        app     App     app
        sym     Sym     =payload sym:

    Returns `{operator: (constructor, ref, prefix)}`, where `ref` is `None` for
    `=payload` -- an operator the reference writes as its payload rather than under a
    tag -- and `prefix` is what that payload needs in front of it, or `""`.

    This is deliberately not in the `.egg` language file: what the reference calls a
    constructor is a fact about the harness, not about the encoding.
    """
    out = {}
    for raw in path.read_text().splitlines():
        line = raw.split(";")[0].strip()
        if not line:
            continue
        op, ctor, ref, *rest = line.split()
        if ref == "=payload":
            assert len(rest) <= 1, f"{op}: one prefix at most, got {rest}"
            out[op] = (ctor, None, rest[0] if rest else "")
        else:
            assert not rest, f"{op}: a tag takes no further field, got {rest}"
            out[op] = (ctor, ref, "")
    return out


def language(spec, ref):
    """A `TermLang` from a language file and its correspondence file.

    The two must name the same constructors, so an operator added to one and not the
    other is an error here rather than a harness that quietly stops covering it.
    """
    sigs = read_language(spec)
    corr = read_correspondence(ref)
    named = {ctor for ctor, _, _ in corr.values()}
    assert named == set(sigs), (
        f"{spec.name} declares {sorted(set(sigs) - named)} that {ref.name} does not name, "
        f"and {ref.name} names {sorted(named - set(sigs))} that it does not declare"
    )
    ops = {op: Op(op, ctor, sigs[ctor], ref=tag, ref_prefix=prefix) for op, (ctor, tag, prefix) in corr.items()}
    # Also reachable by CONSTRUCTOR name. A slotted `.egg` writes the constructor it
    # declared, `(App ?a ?b)`, while a corpus written in Python names the operator,
    # `("app", a, b)`; both denote the same node, and the `.ref` already gives one
    # operator two names where a language wants them.
    for op in list(ops.values()):
        ops.setdefault(op.ctor, op)
    return TermLang(ops)


def cols_of(sig):
    """Column names for a signature: payload vars, and (edge, child) per child."""
    payloads, edges, kids, order = [], [], [], []
    for _i, col in enumerate(sig):
        if col in SLOTTED:
            e, k = f"m{len(kids) + 1}", f"c{len(kids) + 1}"
            edges.append(e)
            kids.append(k)
            order.append((e, k))
        else:
            p = f"p{len(payloads) + 1}"
            payloads.append(p)
            order.append((p,))
    return payloads, edges, kids, order


def pattern(name, sig, edges=None, kids=None, payloads=None):
    """`(Name p1 m1 c1 ...)`, with any column list overridden."""
    dp, de, dk, order = cols_of(sig)
    payloads, edges, kids = payloads or dp, edges or de, kids or dk
    out, pi, ci = [], 0, 0
    for slot in order:
        if len(slot) == 2:
            out += [edges[ci], kids[ci]]
            ci += 1
        else:
            out.append(payloads[pi])
            pi += 1
    return f"({name} {' '.join(out)})"


def declare(name, sig, sort="U"):
    """The `(constructor ...)` line for one signature: a slotted column becomes the two
    egglog columns `Renaming <sort>`, a payload column stays as it is.

    `sort` is the carrier -- the sort a node has and a slotted child is reached through.
    It defaults to the one the hand-written core declares, and is the program's own when
    it declared one."""
    cols = " ".join(f"Renaming {sort}" if c in SLOTTED else c for c in sig)
    return f"(constructor {name} ({cols}) {sort})\n"


def layout(name, sig):
    """Runtime layout metadata for ``slotted-subst``.

    The primitive cannot distinguish an equality-sort column from a container by
    looking at egglog's erased ``Id`` column type.  The compiler therefore records
    every physical edge column explicitly. Binder rows say which edge is the marker
    and which later edge it covers.

    Column indices are zero-based indices into the encoded constructor inputs, after
    every slotted source column has expanded to ``Renaming <carrier>``.
    """
    physical, edges, payloads, sorts = 0, [], [], []
    child_positions = []
    for col in sig:
        if col in SLOTTED:
            edges.append(physical)
            child_positions.append(col)
            physical += 2
        else:
            payloads.append(physical)
            sorts.append(col)
            physical += 1

    out = [f'(set (SlottedNodeLayout "{name}" {physical}) ())']
    out += [f'(set (SlottedEdgeLayout "{name}" {edge}) ())' for edge in edges]
    # a payload's sort, so the substitution spells it as its value when it ranks terms
    out += [
        f'(set (SlottedPayloadLayout "{name}" {col} "{sort}") ())' for col, sort in zip(payloads, sorts, strict=True)
    ]

    bound = [i for i, col in enumerate(child_positions) if col is BINDER]
    if bound:
        covered = max(bound) + 1
        out += [f'(set (SlottedBinderLayout "{name}" {edges[pos]} {edges[covered]} -1 "") ())' for pos in bound]

    return out


def shape_of(col):
    """A column's kind as it is written in a generated file's comments."""
    return {CHILD: "child", BINDER: "binder"}.get(col, str(col))


# The hand-written half, and the generated file that includes it. A language file
# includes the generated one, so it gets both.


###############################################################################
# machinery: the per-constructor maintenance rules
###############################################################################


def _symbols(symbols):
    """The single-sort names when a caller needs no namespace."""
    return symbols or CarrierSymbols.create("U", 0)


def fold(op, xs, empty):
    """`xs` combined right-to-left with a binary egglog operator; `empty` for none."""
    if not xs:
        return empty
    out = xs[-1]
    for x in reversed(xs[:-1]):
        out = f"({op} {x} {out})"
    return out


#: WHAT A BINDER COLUMN IS, and why three rules have to know.
#:
#: `Lam([0 -> x] * Var, m2*c2)` is `lam $x. m2*c2`. The `[0 -> x]` is the name the node
#: BINDS, and the `Var` under it is only how the encoding spells a slot -- not a child the
#: node uses. That distinction is invisible in the columns, which is why it has to be
#: written into the rules that rewrite them, and it matters because the variable class
#: goes SLOTLESS as soon as two of its invocations are equated. From then on every
#: renaming it offers is the empty map, and composing a binder edge with one erases the
#: bound name. Once erased, every later match of a binder pattern -- which reads that slot
#: out of the edge -- silently fails, and the reference, whose `Bind` holds a `Slot`
#: outright, keeps making unions we no longer make.
#:
#: The two rules that compose an edge do it for different reasons, so they need different
#: answers:
#:
#:   `child_update` follows the child's renaming toward its LEADER, which a binder column
#:      does need -- reaching `[0 -> x] * Var(0)` from `[x -> x] * Var(x)` is how two
#:      spellings of one binder are seen to be alpha-equivalent. So the rule stays and
#:      asks for the bound name in the result: renaming it passes, losing it does not.
#:
#:   `congruence` composes with the child's own SYMMETRY, to try the other spellings of
#:      the same invocation. A binder column has no other spelling, so it skips it.
#:      Asking for the name to survive would not do here: the shrinking rule deletes a
#:      slotless class's identity self-loop, leaving the empty map as the only symmetry
#:      on offer, and the rule would simply stop firing.
BOUND_NAME_KEPT = "\n       ; a bound name may be renamed but not lost\n       (= bound{i} (map-get {edge} 0))"


def class_slots(name, sig, symbols=None):
    """A node's own slots, offered as an upper bound on its class's.

    `ClassSlots` intersects on merge, so a class ends up with the slots *every* one of
    its nodes has -- anything only some of them carry is redundant. That is the
    reference's `c.slots`, which starts as the creating node's slots and afterwards
    only shrinks. Discovering another node can narrow this set but never widen it;
    the identity self-edge is derived from the resulting class support.
    """
    symbols = _symbols(symbols)
    _, edges, _, _ = cols_of(sig)
    slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    return f"""\
(rule ((= e1 {pattern(name, sig)}))
      ((set ({symbols.class_slots} e1) {slots})))
"""


def congruence(name, sig, symbols):
    """Pairwise congruence, including the self-pair that discovers symmetries.

    For equal children, solve r . n_i = m_i . g_i over each child's symmetry
    rows. Binder markers are names, so they are compared without a child symmetry.
    The equation is recorded before any duplicate row is removed.
    """
    _, edges, kids, _ = cols_of(sig)
    other = [f"n{i + 1}" for i in range(len(edges))]
    columns = [c for c in sig if c in SLOTTED]
    readings, facts = [], []
    for i, (edge, child, col) in enumerate(zip(edges, kids, columns, strict=True)):
        if col is BINDER:
            readings.append(edge)
        else:
            facts += [f"({symbols.renames} {child} g{i} {child})"]
            readings.append(f"(compose {edge} g{i})")
    facts += [f"(= r (find-mapping {' '.join(readings + other)}))"]
    a, b = pattern(name, sig), pattern(name, sig, edges=other)
    body = [f"(= a {a})", f"(= b {b})", *facts]
    equation = f"({symbols.equated} a r b)"
    derive = "(rule (" + "\n       ".join(body) + f")\n      ({equation}) :ruleset slotted)"
    # Only duplicates within one class are removed here. Migration moves rows
    # between different classes and must preserve their node-local slots.
    duplicate = body + [
        "(= a b)",
        f"(= left (vec-of {' '.join(edges)}))",
        f"(= right (vec-of {' '.join(other)}))",
        "(!= left right)",
        "(= left (ordering-max left right))",
    ]
    remove = "(rule (" + "\n       ".join(duplicate) + f")\n      ({equation} (delete {a})) :ruleset slotted)"
    return derive + "\n" + remove


def migration(name, sig, symbols=None):
    """Rewrite a follower's node into its leader's frame.

    For `e2 = f(m1*c1, m2*c2)` and `e2 = m*e1`, rewriting into e1's frame gives

        e1 = m^-1*e2 = f(m^-1*m1*c1, m^-1*m2*c2)

    so each edge composes with `m^-1` and the original row goes.

    A node can use a slot its leader's frame cannot name -- a slot the class does not
    depend on. A name is invented for it, as the reference's `compose_fresh` does, which is
    what lets the node move at all: leaving it behind instead would mean follower classes
    are never emptied.

    Only ever toward the leader. A native union can temporarily invalidate an
    edge's orientation, so the same ordering guard used by the leader rules also
    guards migration. Otherwise a row could move away from its eventual leader.
    """
    symbols = _symbols(symbols)
    _, edges, _, _ = cols_of(sig)
    ns = [f"n{i + 1}" for i in range(len(edges))]
    node_slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    pulled = "\n       ".join(
        [
            f"(= nodeslots {node_slots})",
            "; R takes the node's slots to the leader's, agreeing with m inverse where",
            "; that is defined and minting a name where it is not",
            "(= R (find-mapping-total (map-domain m) nodeslots (map-domain m) m))",
        ]
        + [f"(= {ns[i]} (compose R {edges[i]}))" for i in range(len(edges))]
    )
    return f"""\
(rule (({symbols.renames} e2 m e1)
       (= e2 {pattern(name, sig)})
       (!= e1 e2)
       (= e2 (ordering-max e1 e2))       ; toward the leader only
       {pulled})
      ((union e1 {pattern(name, sig, edges=ns)})
       (delete {pattern(name, sig)})) :ruleset slotted)
"""


def child_update(name, sig, pos, bound_name=False, symbols=None):
    """Replace child `pos` with its more canonical `m*c'`.

    One rule per child position, canonicalising that child to the class's representative:
    the stored edge composes with the child's renaming, `m1` becoming `m1 . m`.

    `bound_name` says this column holds a name the node binds rather than a child it uses,
    and adds the one condition that makes the rewrite safe there: the bound slot must
    survive the composition. See `BOUND_NAME_KEPT`.

    Only ever toward the leader, for the same reason migration needs it: native
    unions can temporarily invalidate the ordering of a stored edge.

    The child's own identity row is in the relation too, and the rule wants it: composing
    with it narrows an edge that still names a slot the child has since dropped. Any
    OTHER row from the child to itself is refused: rewriting a node through a
    symmetry of its child yields a row per group element and no fixpoint.
    """
    symbols = _symbols(symbols)
    _, edges, kids, _ = cols_of(sig)
    new_e, new_k = list(edges), list(kids)
    new_e[pos] = f"(compose {edges[pos]} m)"
    new_k[pos] = "c'"
    conds = BOUND_NAME_KEPT.format(i=pos, edge=new_e[pos]) if bound_name else ""
    return f"""\
(rule (({symbols.renames} {kids[pos]} m c')
       (= node {pattern(name, sig)}){conds}
       (= {kids[pos]} (ordering-max {kids[pos]} c'))    ; toward the leader only
       ; a row from the child to itself must be idempotent: a native union can turn an
       ; edge into one, and composing a node's edge with a symmetry of its child would
       ; rewrite the node once per group element and never settle
       (guard (or (bool-!= {kids[pos]} c') (bool= (compose m m) m)))
       ; and the new node must differ from the old one
       (guard (or (bool-!= {kids[pos]} c')
                  (bool-!= (compose {edges[pos]} m) {edges[pos]}))))
      ((union node {pattern(name, sig, edges=new_e, kids=new_k)})
       (delete {pattern(name, sig)})) :ruleset slotted)
"""


def binder(name, sig, positions, symbols=None):
    """Take a bound slot out of the node's class's slot set, where it is bound.

    A bound slot rides in its child's edge, so it is a slot of the *node* but must
    not be one of the class: removing it from the edge to the leader is what makes
    two spellings of the same binder alpha-equivalent.

    A binder covers ONE column -- the one right after the binder slots, which is
    what `Bind<T>` wrapping a single child means -- so the slot is removed only
    when no other child column names it. `Let(Bind<body>, value)` binds the slot
    in the body and leaves a `value` occurrence free, and stripping it from the
    whole node instead merges terms the reference keeps apart. Each bound slot
    gets its own rule, since one may be free in an uncovered column while another
    is not: `sdql`'s `Sum` binds two over one body, beside an uncovered range.
    """
    symbols = _symbols(symbols)
    _, edges, kids, _ = cols_of(sig)
    e, k = list(edges), list(kids)
    for n, pos in enumerate(positions):
        e[pos], k[pos] = f"mvar{n}", f"({symbols.var} 0)"
    node = pattern(name, sig, edges=e, kids=k)

    covered = max(positions) + 1
    assert covered < len(kids), f"{name}: a binder must cover a following column"
    uncovered = [i for i in range(len(kids)) if i not in positions and i != covered]

    rules = []
    for n, pos in enumerate(positions):
        free_elsewhere = "".join(f"\n       (map-not-contains (map-image {edges[u]}) v{n})" for u in uncovered)
        rules.append(f"""\
(rule (({symbols.renames} {node} ml l)
       (= v{n} (map-get mvar{n} 0)){free_elsewhere})
      (({symbols.equated} {node} (inverse (map-remove (inverse ml) v{n})) l)))
""")

        # A collision with an uncovered column blocks the strip above, which would
        # leave the bound slot in the class's slot set and stop it being renameable.
        # Move it to a slot the node does not use; the strip then applies. One rule
        # per uncovered column, so the guard stays a single fact.
        # built from the PATTERN's edge names: the binder columns are bound as
        # `mvarN` there, not by their positional name.
        union_of = f"(map-image {e[0]})"
        for x in e[1:]:
            union_of = f"(map-union {union_of} (map-image {x}))"
        for u in uncovered:
            fresh_e = list(e)
            fresh_e[pos] = f"(map-of 0 w{n})"
            fresh_e[covered] = f"(compose (map-insert (map-image {edges[covered]}) v{n} w{n}) {edges[covered]})"
            renamed = pattern(name, sig, edges=fresh_e, kids=k)
            rules.append(f"""\
(rule ((= node {node})
       (= v{n} (map-get mvar{n} 0))
       (map-contains (map-image {edges[u]}) v{n})   ; bound slot is free here too
       (= used {union_of})
       ; the smallest slot the node does not use
       (= fresh{n} (find-mapping-total used (map-of 0 0) (map-empty) (map-empty)))
       (= w{n} (map-get fresh{n} 0)))
      ((union node {renamed})
       (delete {node})))
""")
    return "\n".join(rules)


def banner(text):
    """A section header for a generated file."""
    bar = ";" * 78
    return [bar, f";;; {text}", bar, ""]


def emit(language, sort="U", symbols=None):
    """Node slots, pairwise congruence, migration, child updates, and binder scope."""
    symbols = _symbols(symbols)
    out = []
    for name, sig in language.items():
        _, _, kids, _ = cols_of(sig)
        out += banner(f"{name} :: {' '.join(shape_of(c) for c in sig)}")
        out += [declare(name, sig, sort), *layout(name, sig), class_slots(name, sig, symbols)]
        if not kids:
            continue
        columns = [c for c in sig if c in SLOTTED]
        out += [congruence(name, sig, symbols), migration(name, sig, symbols)]
        out += [child_update(name, sig, i, bound_name=col is BINDER, symbols=symbols) for i, col in enumerate(columns)]
        bound = [i for i, col in enumerate(columns) if col is BINDER]
        if bound:
            out.append(binder(name, sig, bound, symbols=symbols))
    return out


#: The right-hand side head that is a call rather than a node.
SUBST = "subst"


# The constructor-independent half of the node machinery. Hand-written in
# the machinery along with a constructor or two, and kept
# here so a generator can state what that text has to say.


def carrier_core(s):
    """A relational slotted union-find; self-edges are the symmetry group.

    ClassSlots is maintained explicitly. Every stored renaming is restricted to
    its endpoints' public slots, while constructor rows retain node-local slots.
    """
    return f"""(sort {s.sort})
(constructor {s.var} (i64) {s.sort})
(relation {s.renames} ({s.sort} Renaming {s.sort}))
(relation {s.equated} ({s.sort} Renaming {s.sort}))
(function {s.class_slots} ({s.sort}) Renaming :merge (map-intersect old new))
(relation {s.subst_pending} ({s.sort} Renaming Renaming {s.sort}))
(set (SlottedNodeLayout "{s.var}" 1) ())
(set ({s.class_slots} ({s.var} 0)) (map-of 0 0))

;; Orient equations toward the smaller value; self-equations are symmetries.
(rule (({s.equated} a m b) (= a (ordering-max a b))
       (= sa ({s.class_slots} a)) (= sb ({s.class_slots} b)))
      (({s.renames} a (compose sa (compose m sb)) b)) :ruleset slotted)
(rule (({s.equated} a m b) (!= a b) (= b (ordering-max a b))
       (= sa ({s.class_slots} a)) (= sb ({s.class_slots} b)))
      (({s.renames} b (compose sb (compose (inverse m) sa)) a)) :ruleset slotted)

;; Identity, and removal of edges whose orientation a native union invalidated.
(rule ((= slots ({s.class_slots} a)))
      (({s.renames} a slots a)) :ruleset slotted)
(rule (({s.renames} a m b) (!= a b) (= b (ordering-max a b)))
      ((delete ({s.renames} a m b))) :ruleset slotted)

;; Transport support in both directions. Self-edges also remove slots whose
;; symmetry orbit leaves the support, so redundancy propagates through the group.
(rule (({s.renames} a m b) (= slots ({s.class_slots} a)))
      ((set ({s.class_slots} b) (map-image (compose (inverse m) slots)))) :ruleset slotted)
(rule (({s.renames} a m b) (= slots ({s.class_slots} b)))
      ((set ({s.class_slots} a) (map-image (compose m slots)))) :ruleset slotted)

;; Compose paths. Symmetries compose with each other; they do not multiply a
;; follower's edges by every reading of its leader.
(rule (({s.renames} a m b) ({s.renames} b n c)
       (guard (or (bool-!= b c) (bool= a c))))
      (({s.equated} a (compose m n) c)) :ruleset slotted)

;; Two leaders of one follower become related. The guard keeps this deletion
;; separate from the rule that restates renamings after support has shrunk.
(rule (({s.renames} a m b) ({s.renames} a n c)
       (!= a b) (!= a c)
       (= sa ({s.class_slots} a)) (= sb ({s.class_slots} b)) (= sc ({s.class_slots} c))
       (= m (compose sa (compose m sb))) (= n (compose sa (compose n sc)))
       (= b (ordering-max b c))
       (guard (or (bool-!= b c)
                  (and (bool-!= m n) (bool= (ordering-max m n) m)))))
      (({s.equated} b (compose (inverse m) n) c)
       (delete ({s.renames} a m b))) :ruleset slotted)

;; Move a follower's symmetries to its leader before removing its self-edges.
(rule (({s.renames} f g f) ({s.renames} f m l) (!= f l))
      (({s.equated} l (compose (inverse m) (compose g m)) l)
       (delete ({s.renames} f g f))) :ruleset slotted)

;; Normalize old edges and symmetries after either endpoint loses slots.
(rule (({s.renames} a m b)
       (= sa ({s.class_slots} a)) (= sb ({s.class_slots} b))
       (= restricted (compose sa (compose m sb))) (!= m restricted))
      (({s.renames} a restricted b) (delete ({s.renames} a m b))) :ruleset slotted)

;; Equal invocations become one native value. A common leader is not enough:
;; their slot mappings must agree modulo a symmetry of that leader.
(rule (({s.renames} a m c) ({s.renames} b n c) ({s.renames} c g c)
       (= m (compose n g)))
      ((union a b)) :ruleset slotted)

;; Keep a variable's name on the edge into the canonical variable constructor.
(rule ((= a ({s.var} v)) (!= v 0))
      (({s.equated} a (map-of 0 v) ({s.var} 0))
       (delete ({s.var} v))) :ruleset slotted)

;; Substitution returns a class and its frame; record their equation together.
(rule (({s.subst_pending} root q mr r) (= slots ({s.class_slots} r)))
      (({s.equated} root (compose q (compose mr slots)) r)) :ruleset slotted)
"""


#: The sort name the generated single-carrier files encode over.
CARRIER_SORT = "U"

# Maintenance is one fixed point; user matches are applied between fixed points.
MACHINERY_SCHEDULE = "(saturate (run slotted))"


def machinery_schedule():
    """The machinery alone, saturated: what a program with no user rules runs."""
    return f"(run-schedule {MACHINERY_SCHEDULE})"


def round_schedule(steps, user="(run)"):
    """`steps` rounds of the user rules -- `user` is how one step of them is run --
    each followed by the stored matches' actions and the machinery."""
    step = f"(seq {user} (saturate (run slotted-refine)) (run slotted-apply) {MACHINERY_SCHEDULE})"
    return f"(run-schedule {MACHINERY_SCHEDULE}\n              (repeat {steps} {step}))"


def prelude():
    """The declarations no sort owns: renamings, refinement lists, and their indices.

    Nothing here names a carrier, so one copy serves a program however many equality
    sorts it declares.
    """
    return "\n".join(
        [
            ";; A renaming is a partial injection on slots.",
            "(sort Renaming (Map i64 i64))",
            "",
            ";; Every way a match's slots may be merged, and the indices to read one at.",
            "(sort Frames (Vec Frame))",
            "(sort Renamings (Vec Renaming))",
            ";; Grow indices to cover every stored match before the apply phase.",
            "(ruleset slotted-refine)",
            "(function RefinementCount () i64 :merge (max old new))",
            "(set (RefinementCount) 0)",
            "(relation Idx (i64))",
            "(Idx 0)",
            # Binary-tree expansion covers [0, count) in logarithmically many rounds.
            *(
                f"(rule ((Idx _i) (= _next (+ (* _i 2) {offset})) (< _next (RefinementCount)))"
                " ((Idx _next)) :ruleset slotted-refine)"
                for offset in (1, 2)
            ),
        ]
    )


def multi_sort_core(carriers):
    """Shared declarations followed by one isolated core per carrier."""
    header = "\n".join(
        [
            ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
            ";;; multi-sort slotted machinery",
            ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
            "",
            "(ruleset slotted)",
            "(ruleset slotted-apply)",
            "",
            "(function SlottedNodeLayout (String i64) Unit :no-merge :internal-hidden)",
            "(function SlottedEdgeLayout (String i64) Unit :no-merge :internal-hidden)",
            "(function SlottedBinderLayout (String i64 i64 i64 String) Unit :no-merge :internal-hidden)",
            "(function SlottedPayloadLayout (String i64 String) Unit :no-merge :internal-hidden)",
            "",
        ]
    )
    body = "\n".join([header, *(carrier_core(symbols) for symbols in carriers.values())])
    return prefix_variables_in_rules(body)


#: Keywords that introduce a name the rule does not bind, so the token after one is
#: left alone.
_RULE_KEYWORDS = (":ruleset", ":name", ":when", ":subsume")


def prefix_rule_variables(text, prefix="_"):
    """Every variable a generated rule binds, renamed out of the program's namespace.

    egglog refuses a rule variable that shadows a sort, so a machinery rule writing
    `m` or `a` would make `(sort m)` illegal -- a restriction on the program coming
    from a name the machinery happened to pick. Prefixing puts them where the compiler
    already keeps its own names.

    A token is an OPERATOR when it follows `(`, and a variable otherwise; numbers,
    strings and the token after a keyword are neither. That is enough to tell them
    apart without knowing which relations and primitives exist.
    """
    out, after_open, after_kw = [], False, False
    for tok in re.findall(r'\(|\)|"[^"]*"|;[^\n]*|[^\s()]+|\s+', text):
        if tok.startswith(";") or tok.isspace():
            out.append(tok)
            continue
        if tok == "(":
            out.append(tok)
            after_open, after_kw = True, False
            continue
        if tok == ")":
            out.append(tok)
            after_open, after_kw = False, False
            continue
        bare = not (after_open or after_kw or tok.startswith(('"', ":")) or re.fullmatch(r"-?\d+", tok))
        out.append(prefix + tok if bare else tok)
        after_kw = tok in _RULE_KEYWORDS
        after_open = False
    return "".join(out)


def prefix_variables_in_rules(text, prefix="_"):
    """`prefix_rule_variables` over every `(rule ...)` in a block, and nothing else.

    A declaration binds names the program must be able to write -- `(constructor Add
    ...)` -- so only rule bodies are rewritten.
    """
    out, i = [], 0
    while True:
        at = text.find("(rule ", i)
        if at < 0:
            out.append(text[i:])
            return "".join(out)
        out.append(text[i:at])
        depth, j = 0, at
        while j < len(text):
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            elif text[j] == '"':
                j = text.index('"', j + 1)
            elif text[j] == ";":
                j = text.find("\n", j)
            j += 1
        out.append(prefix_rule_variables(text[at:j], prefix))
        i = j


def in_slotted_ruleset(text):
    """Put every emitted rule in the `slotted` ruleset.

    These rules maintain the encoding's invariants, and they have to be *saturated*
    between the user's rule steps: a user rule that matches a node before the alpha- and
    slot-canonicalisation of that node has finished sees a spelling that is about to
    change, and then matches again when it does. `slotted/ENCODING.md` says
    what schedule to write; this only puts the rules where a schedule can name them.
    """
    out, depth, form, buf = [], 0, [], []
    for line in text.splitlines(keepends=True):
        if depth == 0 and not line.lstrip().startswith("("):
            buf.append(line)
            continue
        depth += line.count("(") - line.count(")")
        form.append(line)
        if depth <= 0:
            body = "".join(form)
            head = body.lstrip()[:6]
            if head in ("(rule ", "(rule\n") and ":ruleset" not in body:
                i = body.rindex(")")
                body = body[:i] + " :ruleset slotted)" + body[i + 1 :]
            out.append("".join(buf) + body)
            buf, form, depth = [], [], 0
    return prefix_variables_in_rules("".join(out) + "".join(buf))


###############################################################################
# terms
###############################################################################


def map_of(d):
    """A renaming literal, from a dict."""
    if not d:
        return "(map-empty)"
    return "(map-of " + " ".join(f"{k} {v}" for k, v in sorted(d.items())) + ")"


def pay_text(op, pay):
    """A payload as the ORACLE spells it.

    A pattern tags its payloads, and the oracle's syntax has a place for a literal but
    not for a variable: its patterns bind slots and applied ids, not payload values. So
    a variable there is refused rather than mis-spelled.
    """
    if isinstance(pay, tuple):
        if pay[0] == "ppv":
            raise SystemExit(
                f"{op.name}: the oracle cannot be asked about a payload VARIABLE "
                f"({pay[1]!r}); its patterns have no place for one."
            )
        pay = pay[1]
    return pay.strip('"')


def node_expr(op, edges, kids, pays=(), pay_var=None):
    """`(Ctor pay... m c ...)`: one node, payloads interleaved into their columns.

    A payload arrives either already spelled -- a literal the operator pins, or a ground
    term's value -- or TAGGED by a pattern: `("plit", value)` to spell here against the
    column's sort, or `("ppv", name)` for a variable, which `pay_var` turns into the
    egglog name that binds it. Spelling in one place is what keeps a string from being
    quoted twice.
    """
    cols, ci, pi = [], 0, 0
    for col in op.sig:
        if col in SLOTTED:
            cols += [edges[ci], kids[ci]]
            ci += 1
        else:
            p = pays[pi]
            if isinstance(p, tuple):
                if p[0] == "ppv":
                    if pay_var is None:
                        raise SystemExit(f"{op.name}: a payload variable ({p[1]!r}) where no pattern binds one")
                    p = pay_var(p[1])
                else:
                    p = f'"{p[1]}"' if col == "String" else str(p[1])
            cols.append(p)
            pi += 1
    return f"({op.ctor} {' '.join(cols)})" if cols else f"({op.ctor})"


class Op:
    """One high-level operator, and the constructor column-walk it compiles to.

    `ctor`  the egglog constructor.
    `sig`   its columns in order: `CHILD`, `BINDER`, or a payload sort.
    `pays`  one entry per payload column: a literal already spelled for egglog,
            where the operator pins it -- the generic encoding's head string is one --
            or `None` to take the value from the term's argument in that column.
    `ref`   the operator's name in the oracle's syntax. `None` marks a payload leaf,
            which the oracle writes as the payload itself.
    `ref_prefix`
            what that payload needs in front of it for the oracle to read it as a
            payload rather than a tag.

    A term's arguments line up with the columns that consume one: a sub-term for a
    `CHILD`, a slot for a `BINDER`, a value for a payload the operator does not pin.
    """

    def __init__(
        self,
        name,
        ctor,
        sig=(),
        pays=None,
        ref=None,
        ref_prefix="",
        sort="U",
        kid_sorts=None,
    ):
        self.name = name
        self.ctor = ctor
        self.sig = list(sig)
        self.sort = sort
        self.kid_sorts = list(kid_sorts) if kid_sorts is not None else [sort] * sum(c in SLOTTED for c in self.sig)
        assert len(self.kid_sorts) == sum(c in SLOTTED for c in self.sig), (
            f"{name}: {len(self.kid_sorts)} child sort(s) for {sum(c in SLOTTED for c in self.sig)} slotted column(s)"
        )
        npay = sum(1 for c in self.sig if c not in SLOTTED)
        self.pays = list(pays) if pays is not None else [None] * npay
        assert len(self.pays) == npay, f"{name}: {npay} payload column(s)"
        self.ref = ref
        self.ref_prefix = ref_prefix

    @property
    def kid_cols(self):
        """The slotted columns, in order."""
        return [c for c in self.sig if c in SLOTTED]

    @property
    def binders(self):
        """The child positions -- counted over children -- whose slot the node binds."""
        return [i for i, c in enumerate(self.kid_cols) if c is BINDER]

    @property
    def covered(self):
        """The one child column a binder scopes over: the next one along."""
        return max(self.binders) + 1 if self.binders else None

    def arg_kinds(self):
        """One entry per term argument: `CHILD`, `BINDER`, or the payload's sort."""
        out, pi = [], 0
        for col in self.sig:
            if col in SLOTTED:
                out.append(col)
            else:
                if self.pays[pi] is None:
                    out.append(col)
                pi += 1
        return out

    def split(self, args):
        """`(kids, pays)`: the arguments in slotted columns, and a literal per
        payload column -- the operator's own where it pins one, else the argument
        spelled for its sort."""
        kids, pays, ai, pi = [], [], 0, 0
        for col in self.sig:
            if col in SLOTTED:
                kids.append(args[ai])
                ai += 1
            else:
                lit = self.pays[pi]
                if lit is None:
                    a = args[ai]
                    # a pattern's payload arrives tagged and is spelled by `compile_rule`
                    lit = a if isinstance(a, tuple) else (f'"{a}"' if col == "String" else str(a))
                    ai += 1
                pays.append(lit)
                pi += 1
        assert ai == len(args), f"{self.name}: {len(args)} argument(s) for {ai} column(s)"
        return kids, pays


class TermLang:
    """A high-level term language over the encoding: `{operator: Op}`.

    A term is `(op, arg...)`. `("var", s)` is the one built-in: the encoding has a
    single variable class `(Var 0)`, and a variable is that class reached by an edge
    `0 -> s`, so a bare variable at top level would lose its slot.

    A binder column's argument is the slot it binds, written either bare or as the
    `("var", s)` term some corpora spell it with.
    """

    VAR = "var"

    def __init__(self, ops, carriers=None):
        self.ops = dict(ops)
        declared = []
        for op in self.ops.values():
            for sort in (op.sort, *op.kid_sorts):
                if sort not in declared:
                    declared.append(sort)
        self.carriers = carriers or carrier_symbols(declared or ("U",))
        self.default_sort = next(iter(self.carriers))

    def __getitem__(self, name):
        return self.ops[name]

    def __contains__(self, name):
        return name in self.ops

    def symbols_for(self, sort):
        return self.carriers[sort]

    def sort_of(self, t, expected=None):
        """The equality sort of a term; a bare variable inherits its context."""
        if t[0] == self.VAR:
            return expected
        return self.ops[t[0]].sort

    @staticmethod
    def slot(arg):
        """A binder column's argument as a bare slot."""
        return arg[1] if isinstance(arg, tuple) else arg

    def slots(self, t):
        """The term's FREE slots.

        A binder's slot is free in every column but the one it covers, which is what
        `Bind<T>` wrapping a single child means: `let x = x in b` keeps the value's
        occurrence free.
        """
        if t[0] == self.VAR:
            return {t[1]}
        op = self.ops[t[0]]
        kids, _ = op.split(t[1:])
        bound = {self.slot(kids[i]) for i in op.binders}
        free = set()
        for i, k in enumerate(kids):
            if i in op.binders:
                continue
            s = self.slots(k)
            free |= (s - bound) if i == op.covered else s
        return free

    def edge(self, t):
        """The stored renaming from a child's slots into its parent's slot space.

        A variable is stored as the canonical `(Var 0)`, so its edge names slot 0;
        anything else is built at its own slot names, so its edge is the identity on
        its free slots -- for a binder that is the node's slots minus the bound one,
        which is what the class has.
        """
        if t[0] == self.VAR:
            return {0: t[1]}
        return {s: s for s in self.slots(t)}

    def refresh_shadowed_binders(self, t):
        """Give repeated binder columns the reference language's `Bind` meaning.

        `Sum(A, Bind<Bind<A>>)` and `Merge(A, A, Bind<Bind<Bind<A>>>)` are
        lexically nested binders even though the encoding flattens their names into
        sibling columns.  If two layers use the same source name, the innermost one
        shadows the outer one.  Leaving both columns equal instead identifies two
        private slots and produces a different e-node.  Alpha-refresh only the
        shadowed OUTER column; occurrences in the covered body continue to name the
        innermost binder.

        Fresh names avoid every slot written anywhere in this term, including
        uncovered columns.  Running this over the whole tree before recursive
        encoding also avoids colliding with an enclosing binder.
        """

        def all_slots(x):
            if isinstance(x, str):
                return {x} if x.startswith("$") else set()
            if x[0] == self.VAR:
                return {x[1]}
            if x[0] not in self.ops:  # a front-end's opaque, already-bound name
                return set()
            op = self.ops[x[0]]
            out = set()
            for kind, arg in zip(op.arg_kinds(), x[1:], strict=True):
                if kind is BINDER:
                    out.add(self.slot(arg))
                elif kind is CHILD:
                    out |= all_slots(arg)
            return out

        used = all_slots(t)
        pattern_slots = any(isinstance(s, str) and s.startswith("$") for s in used)
        fresh_index = [0]

        def fresh():
            if pattern_slots:
                while True:
                    s = f"$__shadow{fresh_index[0]}"
                    fresh_index[0] += 1
                    if s not in used:
                        used.add(s)
                        return s
            s = 0
            while s in used:
                s += 1
            used.add(s)
            return s

        def go(x):
            if isinstance(x, str):
                return x
            if x[0] == self.VAR or x[0] not in self.ops:
                return x
            op = self.ops[x[0]]
            args = [
                go(a) if kind is CHILD and isinstance(a, tuple) else a
                for kind, a in zip(op.arg_kinds(), x[1:], strict=True)
            ]
            kids, _pays = op.split(args)
            seen = set()
            for i in reversed(op.binders):
                name = self.slot(kids[i])
                if name in seen:
                    # `args` and child positions differ when fixed payload columns are
                    # present; find this child column in the argument walk.
                    child_index = -1
                    for ai, kind in enumerate(op.arg_kinds()):
                        if kind in SLOTTED:
                            child_index += 1
                            if child_index == i:
                                args[ai] = fresh()
                                break
                else:
                    seen.add(name)
            return (x[0], *args)

        return go(t)

    def enc(self, t, expected_sort=None):
        """Encoding syntax.

        A binder column holds the bound slot as an edge `0 -> s` to `(Var 0)`. The
        covered child's own edge still names that slot: the node carries it, and only
        the class drops it.
        """
        t = self.refresh_shadowed_binders(t)
        if t[0] == self.VAR:
            sort = expected_sort or self.default_sort
            return f"({self.symbols_for(sort).var} 0)"
        op = self.ops[t[0]]
        if expected_sort is not None and op.sort != expected_sort:
            raise SystemExit(f"{op.name} produces {op.sort}, but this position requires {expected_sort}")
        kids, pays = op.split(t[1:])
        edges, cs = [], []
        for i, k in enumerate(kids):
            if i in op.binders:
                edges.append(map_of({0: self.slot(k)}))
                cs.append(f"({self.symbols_for(op.kid_sorts[i]).var} 0)")
            else:
                edges.append(map_of(self.edge(k)))
                cs.append(self.enc(k, op.kid_sorts[i]))
        return node_expr(op, edges, cs, pays)

    def sexpr(self, t):
        """Reference / oracle syntax."""
        if t[0] == self.VAR:
            return f"(var ${t[1]})"
        op = self.ops[t[0]]
        kids, pays = op.split(t[1:])
        if op.ref is None:
            # a payload leaf, written as its payload
            return op.ref_prefix + pay_text(op, pays[0])
        assert not (kids and None in op.pays), f"{op.name}: no oracle syntax for a payload argument beside a child"
        parts = [f"${self.slot(k)}" if i in op.binders else self.sexpr(k) for i, k in enumerate(kids)]
        return f"({op.ref} {' '.join(parts)})" if parts else op.ref

    def shift(self, t, k):
        """Add `k` to every slot in a term. Slot names carry no meaning, so no answer
        may change."""
        if t[0] == self.VAR:
            return (t[0], t[1] + k)
        out = []
        for kind, a in zip(self.ops[t[0]].arg_kinds(), t[1:], strict=True):
            if kind is CHILD:
                out.append(self.shift(a, k))
            elif kind is BINDER:
                out.append(self.shift(a, k) if isinstance(a, tuple) else a + k)
            else:
                out.append(a)
        return (t[0], *out)


###############################################################################
# rules
###############################################################################
#
# An ATOM is `(root, op, [child...])`, one per e-node of the flattened left-hand
# side, with each child one of
#
#   ("pv",  name)   a pattern variable
#   ("sl",  "$x")   a slot literal -- a binder column, or the reference's `(var $x)`
#                   in an ordinary column. Both are the class `(Var 0)` reached by an
#                   edge `0 -> $x`
#   ("cls", term)   a ground leaf node, matched through `RenamesToLeader` so the
#                   column is compared against the leaf's CLASS. Writing the leaf
#                   into the column instead matches the same rows -- a slotless class
#                   is unioned with its leader -- but this is the one spelling
#                   `flatten` emits, so a rule reads the same however it was written
#
# A RIGHT-HAND SIDE is a `("pv", name)`, a `("sl", "$x")`, or `(op, arg...)` to build
# a node -- its arguments right-hand sides for the slotted columns and plain values
# for any payload column the operator does not pin, so a ground leaf is the case with
# no slotted columns.
#
# `rhs_of` converts a plain nested term into that grammar for a caller that writes
# its variables as bare strings.
#
# The markers are read as markers, so no operator may be named `pv`, `sl` or `cls`.


def pvars_of(atom):
    """An atom's pattern variables -- its root and every `pv` child.

    This ordering helper counts shared class variables. Slot-literal constraints
    are joined by the frame independently of that ordering.
    """
    return {atom[0]} | {c[1] for c in atom[2] if c[0] == "pv"}


def connected_order(lang, atoms, first=None):
    """Prefer connected atoms and parent/child links for stable, readable output.

    Frame joins do not depend on atom order. Keep this ordering convention because
    it also affects query planning and the generated variable names. `first` pins
    the leading atom; the default prefers a non-binder.
    """
    atoms = list(atoms)
    if first is None:
        first = next((j for j, a in enumerate(atoms) if not lang[a[1]].binders), 0)

    def kids_of(a):
        return {c[1] for c in a[2] if c[0] == "pv"}

    out = [atoms[first]]
    rest = [a for j, a in enumerate(atoms) if j != first]
    seen = pvars_of(atoms[first])
    roots = {atoms[first][0]}
    kids = kids_of(atoms[first])
    while rest:
        # Prefer a parent/child link, then any shared variable, then a disconnected atom.
        i = next(
            (j for j, a in enumerate(rest) if a[0] in kids or kids_of(a) & roots),
            None,
        )
        if i is None:
            i = next((j for j, a in enumerate(rest) if pvars_of(a) & seen), 0)
        a = rest.pop(i)
        out.append(a)
        seen |= pvars_of(a)
        roots.add(a[0])
        kids |= kids_of(a)
    return out


def slot_literals(t, out=None):
    """Every slot literal a term mentions, as the `$x` strings a pattern writes."""
    out = set() if out is None else out
    if isinstance(t, tuple):
        if len(t) == 2 and t[0] == "sl":
            out.add(t[1])
        else:
            for a in t:
                slot_literals(a, out)
    return out


def _binder_scopes(lang, t, under=frozenset(), out=None):
    """For each pattern variable, the binder slots each of its occurrences sits under."""
    out = {} if out is None else out
    if not isinstance(t, tuple) or len(t) < 2 or t[0] == "sl":
        return out
    if t[0] == "pv":
        out.setdefault(t[1], []).append(frozenset(under))
        return out
    if t[0] == SUBST:
        for a in t[1:]:
            _binder_scopes(lang, a, under, out)
        return out
    op = lang[t[0]]
    kids, _pays = op.split(t[1:])
    bound = frozenset(kids[i][1] for i in op.binders if isinstance(kids[i], tuple) and kids[i][0] == "sl")
    for i, k in enumerate(kids):
        _binder_scopes(lang, k, under | bound if i == op.covered else under, out)
    return out


def capture_guards(lang, lhs, rhs):
    """The `(not-free $b v)` guards a rule owes, as `($b, v)` pairs.

    A matched binder's bound slot may be read as any name -- the name of one of the
    term's free variables included, which is a fine alpha-variant of the term. That is
    the matcher's semantics here and in the reference's `MultiPattern`, and a language
    may want it (a bound variable identified with a free one, as `bound-aliasing`
    does). It puts one duty on a rule: where its right-hand side rebinds a slot `$b`
    over a variable `v` that the left-hand side did NOT match under `$b`, the reading
    with `$b` as `v`'s free variable builds a node that captures `v`. `let-lam-diff`
    reading `let x = y in (λw. x w)` with `w` as `y` builds `λy. let x = y in x y`. So
    such a rule has to say `(not-free $b v)`, and this is the list of those it owes.
    Under the reference's nested matcher the guards are vacuous, its bound slots
    staying injective, so a reference rule set can lack them and still be faithful.

    A slot the right-hand side alone binds is minted fresh and owes nothing.
    """
    if not isinstance(rhs, tuple) or rhs[0] in ("pv", "sl", SUBST):
        return set()
    seen_in_lhs = slot_literals(lhs)
    on_left, on_right = _binder_scopes(lang, lhs), _binder_scopes(lang, rhs)
    owed = set()
    for v, occurrences in on_right.items():
        left = on_left.get(v)
        if not left:
            continue
        for under in occurrences:
            for b in under:
                if b in seen_in_lhs and all(b not in o for o in left):
                    owed.add((b, v))
    return owed


def missing_capture_guards(lang, lhs, rhs, conds):
    """The owed guards a rule does not state."""
    stated = {(slot, v) for want, slot, pvars in conds if not want for v in pvars}
    return capture_guards(lang, lhs, rhs) - stated


def has_pay_var(t):
    """Does this sub-term bind a payload VARIABLE anywhere?

    Such a term is not ground, so it cannot be reached through its class -- it has to be
    matched like any other atom.
    """
    if not isinstance(t, tuple):
        return False
    if len(t) == 2 and t[0] == "ppv":
        return True
    return any(has_pay_var(a) for a in t)


def plain_pays(t):
    """This sub-term with its payload literals untagged, for the ground spellers.

    A pattern tags its payloads; a term named by its class is ground, so every payload
    in it is a literal and the tag has no more work to do.
    """
    if not isinstance(t, tuple):
        return t
    if len(t) == 2 and t[0] == "plit":
        return t[1]
    if len(t) == 2 and t[0] in ("pv", "sl", "cls", "var", "name"):
        return t
    return tuple(plain_pays(a) for a in t)


def flatten(lang, term, root="?_p", tmp="?_t"):
    """A nested pattern as depth-1 atoms, pre-order, so every atom's root is a child
    of an earlier one -- which is the connectivity the recipe requires.

    Returns `(root, atoms)`. A child written `$x` is a slot literal, a ground leaf
    node is reached through its class, and any other sub-term gets a name of its own.

    An atom is `(root, op, kids, pays)`. The payloads ride along because a pattern may
    match on one or bind it, and dropping them here is what made an operator with a
    payload column unusable in any rule.
    """
    term = lang.refresh_shadowed_binders(term)
    atoms, ctr = [], [0]

    def go(t, name):
        kids, nested = [], []
        cs, pays = lang[t[0]].split(t[1:])
        for c in cs:
            if isinstance(c, str):
                kids.append(("sl", c) if c.startswith("$") else ("pv", c))
            elif not lang[c[0]].kid_cols and not has_pay_var(c):
                kids.append(("cls", plain_pays(c)))
            else:
                ctr[0] += 1
                nm = f"{tmp}{ctr[0]}"
                kids.append(("pv", nm))
                nested.append((c, nm))
        atoms.append((name, t[0], kids, pays))
        for c, nm in nested:
            go(c, nm)

    go(term, root)
    return root, atoms


def rhs_of(lang, t):
    """A plain nested term as a right-hand side in the grammar above: a bare string
    is a pattern variable unless it starts with `$`, and a payload argument is left
    alone.

    `(subst body $x t)` is the one head that is not a constructor. It is a call, not a
    node, so it cannot be built -- see `compile_rule`.
    """
    t = lang.refresh_shadowed_binders(t)
    if isinstance(t, str):
        return ("sl", t) if t.startswith("$") else ("pv", t)
    if t[0] == SUBST:
        assert len(t) == 4, f"{SUBST} takes a body, a slot and a term: {t}"
        return (SUBST, *(rhs_of(lang, a) for a in t[1:]))
    out = [rhs_of(lang, a) if kind in SLOTTED else a for kind, a in zip(lang[t[0]].arg_kinds(), t[1:], strict=True)]
    return (t[0], *out)


def atom_lines(lang, root, atoms, var="var"):
    """A flattened pattern as the oracle's `MultiPattern` atom lines.

    `(root_name, lines)`, with the leading `?` stripped as those lines want. An atom's
    children are pattern variables and slot literals, so:

      * a slot literal in a BINDER column is the bare `$x` that `Bind` holds; a pattern
        variable there is refused by the compiler, and is an error here;
      * anywhere else it is the TERM `(var $x)`, which needs an atom of its own, since
        an atom's child has to be a pattern variable;
      * a child reached through its own class -- a payload leaf written literally --
        gets an ATOM OF ITS OWN, since it cannot sit in a child position either, and the
        child refers to that; its payload is marked `#` so it stays a payload.

    Asking the reference the flattened question makes the comparison like-for-like:
    the encoding implements `MultiPattern`, not the reference's distinct nested
    pattern language.
    """
    out, extra = [], [0]
    for name, op, kids, *_pays in atoms:
        binders = set(lang[op].binders)
        spelled = []
        for i, (kind, c) in enumerate(kids):
            if kind == "pv" and i in binders:
                raise SystemExit(f"a pattern variable ({c}) cannot stand in {op}'s binder column")
            if kind == "pv":
                spelled.append(c.lstrip("?"))
            elif kind == "sl" and i in binders:
                spelled.append(c)
            elif kind == "sl":
                extra[0] += 1
                v = f"_sl{extra[0]}"
                out.append(f"atom {v} {var} {c}")
                spelled.append(v)
            else:
                # a leaf reached through its own class. It cannot sit in a child position
                # either -- an atom's child has to be a pattern variable -- so it gets an
                # atom of its own and the child refers to that. Its payload is marked `#`
                # so it stays a payload rather than becoming a variable.
                extra[0] += 1
                v = f"_cl{extra[0]}"
                leaf = lang.sexpr(c)
                if leaf.startswith("("):
                    head, *pays = leaf[1:-1].split()
                    out.append(f"atom {v} {head} " + " ".join(f"#{x}" for x in pays))
                else:
                    out.append(f"atom {v} {leaf}")
                spelled.append(v)
        out.append(f"atom {name.lstrip('?')} {lang[op].ref or op} {' '.join(spelled)}")
    return root.lstrip("?"), out


def pat_sexpr(lang, t, binder=False):
    """A pattern term -- an atom's child, or a right-hand side -- in the oracle's
    syntax.

    A slot literal renders two ways: in a binder column it is the bare `$x` that
    `Bind` holds, and anywhere else it is the term `(var $x)`. The encoding stores
    both as an edge to `(Var 0)`, which is why one child kind covers both.
    """
    if t[0] == "pv":
        return f"?{t[1]}"
    if t[0] == "sl":
        return t[1] if binder else f"(var {t[1]})"
    if t[0] == "cls":
        return lang.sexpr(t[1])
    if t[0] == SUBST:
        # The reference's own spelling of a substitution, `b[x := t]`, which its
        # `Pattern::parse` accepts on a right-hand side (`src/rewrite/pattern.rs`).
        # Not a constructor, so `lang[...]` below would not find it.
        b, sl, tt = t[1:]
        return f"{pat_sexpr(lang, b)}[(var {sl[1]}) := {pat_sexpr(lang, tt)}]"
    op = lang[t[0]]
    kids, pays = op.split(t[1:])
    if op.ref is None:
        # a payload leaf, written as its payload -- with the prefix the oracle needs to
        # read it as a payload rather than a tag, exactly as `TermLang.sexpr` does for
        # a ground term. The two renderers have to agree: one writes a rule's pattern
        # and the other the terms that rule has to match.
        return op.ref_prefix + pay_text(op, pays[0])
    assert not (kids and None in op.pays), f"{op.name}: no oracle syntax for a payload argument beside a child"
    parts = [pat_sexpr(lang, k, binder=(i in op.binders)) for i, k in enumerate(kids)]
    return f"({op.ref} {' '.join(parts)})" if parts else op.ref


def infer_pattern_sorts(lang, atoms):
    """Infer each MultiPattern variable's carrier from its atom positions."""
    sorts = {}

    def bind(pvar, sort):
        previous = sorts.setdefault(pvar, sort)
        if previous != sort:
            raise SystemExit(f"pattern variable {pvar!r} is used at both equality sorts {previous} and {sort}")

    for root, opname, kids, *_payloads in atoms:
        op = lang[opname]
        bind(root, op.sort)
        for kid, child_sort in zip(kids, op.kid_sorts, strict=True):
            if kid[0] == "pv":
                bind(kid[1], child_sort)
            elif kid[0] == "cls":
                actual = lang.sort_of(kid[1], child_sort)
                if actual != child_sort:
                    raise SystemExit(f"{opname}: a {child_sort} child cannot contain a {actual} term")
    return sorts


def lower_substitution(lang, root, rhs, pvar_sorts, mp_of, cls_of, slot_of, new):
    """Lower `(subst body $x replacement)` through the body's local frame."""
    root_sort = pvar_sorts[root]
    symbols = lang.symbols_for(root_sort)
    body, slot, replacement = rhs[1:]
    assert body[0] == "pv" and replacement[0] == "pv", (
        f"{SUBST}: body and term must be variables, got {body}, {replacement}"
    )
    assert slot[0] == "sl", f"{SUBST}: the slot must be a slot literal, got {slot}"
    for pvar in (body[1], replacement[1]):
        if pvar_sorts[pvar] != root_sort:
            raise SystemExit(
                f"{SUBST}: {pvar!r} has sort {pvar_sorts[pvar]}, but the rewritten root has sort {root_sort}"
            )

    body_map, replacement_map, x = mp_of[body[1]], mp_of[replacement[1]], slot_of[slot[1]]
    needed, into_body, body_x, replacement_renaming, back_to_root = (
        new(name) for name in ("needed", "into_body", "body_x", "t_ren", "back")
    )
    # The primitive reads the class's frame out of a table it is told the name of; the
    # name is a carrier's, so it is always passed rather than left to a default.
    primitive_args = (
        f"{cls_of[body[1]]} {body_x} ({symbols.var} 0) {replacement_renaming} "
        f'{cls_of[replacement[1]]} "{symbols.class_slots}"'
    )
    return [
        f"(let {needed} (map-union (map-image {body_map}) (map-union (map-image {replacement_map}) (map-of {x} {x}))))",
        f"(let {into_body} (find-mapping-total (map-domain {body_map}) {needed} (map-domain {body_map}) {body_map}))",
        f"(let {body_x} (map-get {into_body} {x}))",
        f"(let {replacement_renaming} (compose-total {into_body} {replacement_map}))",
        f"(let {back_to_root} (compose (inverse {mp_of[root]}) (inverse {into_body})))",
        f"({symbols.subst_pending} {cls_of[root]} {back_to_root} "
        f"(slotted-subst-frame {primitive_args}) (slotted-subst {primitive_args}))",
    ]


class Query:
    """A solved multipattern: the facts that match it, and the frame they bind.

    A rule appends an action to this and a claim appends the facts that state it, so
    both ask the e-graph the same question about the same pattern. The frame is what
    the action or the claim reads:

      `cls_of[v]`   the leader of the class `v` matched
      `mp_of[v]`    its renaming from that class's slots into the pattern's, narrowed
                    to the slots the class actually has
      `slot_of`     the pattern slot each `$x` was solved to

    `new` and `pay_name` continue the query's own name supplies, so whatever is
    appended cannot collide with a name the pattern already used.

    `split`, `refined` and `pays` are for a rule that stores its matches (C13):
    `body[:split]` finds a match and binds `refined` to its refinements, `body[split:]`
    reads one refinement out and checks the conditions, and `pays` maps each payload
    variable the atoms bind to its sort. `split` is `None` when nothing is refined.
    """

    def __init__(
        self,
        body,
        cls_of,
        mp_of,
        slot_of,
        pvar_sorts,
        new,
        pay_name,
        frame=None,
        fname=None,
        split=None,
        refined=None,
        pays=None,
    ):
        self.body = body
        self.cls_of = cls_of
        self.mp_of = mp_of
        self.slot_of = slot_of
        self.pvar_sorts = pvar_sorts
        self.new = new
        self.pay_name = pay_name
        #: the egglog variable holding the refined frame, and the frame's name for a
        #: pattern variable
        self.frame = frame
        self.fname = fname
        self.split = split
        self.refined = refined
        self.pays = pays or {}


def compile_query(
    lang,
    atoms,
    conds=(),
    diseq=(),
    same=(),
    fresh=(),
    var_prefix="",
    refine=True,
    anchor=None,
):
    """Compile a flattened multipattern into the facts that match it, as FRAMES.

    egglog matches the atoms; the slotted part is a set of constraints on them. Each
    atom's columns become one `atom` value (C2, C4, C5, C7), the atoms are joined
    (C6, and the cliques), `refine` picks one merging of what is left open (C8),
    `mint` adds the right-hand side's fresh slots (C10), and the conditions read the
    result (C9). Nothing here is ordered: `frame-join` is associative and commutative,
    so the join tree below means nothing; egglog runs every primitive after the table
    join, once per matched row.
    """
    body, uid, used = [], [0], set()
    pvar_sorts = infer_pattern_sorts(lang, atoms)

    def named(base):
        """An egglog variable named for what it holds, suffixed only if the name is taken."""
        name = f"{var_prefix}{base}"
        while name in used:
            uid[0] += 1
            name = f"{var_prefix}{base}_{uid[0]}"
        used.add(name)
        return name

    def label(pv):
        """A pattern variable as it appears in an egglog variable name."""
        return pv.lstrip("?").lstrip("_") or "v"

    def fname(pv):
        """The frame's name for a pattern variable: the source's own, or `_t1` for one the
        flattener invented, which no author's name begins with."""
        return pv.lstrip("?")

    def kid_label(k, j):
        return label(k[1]) if k[0] == "pv" else ("lit_" + k[1][1:] if k[0] == "sl" else f"leaf{j}")

    def quoted(names):
        text = " ".join(f'"{n}"' for n in names)
        return f" {text}" if text else ""

    cls_of, pay_of, pay_sorts = {}, {}, {}
    binding = [True]

    def pay_name(n):
        if n not in pay_of:
            if not binding[0]:
                raise SystemExit(
                    f"the right-hand side names the payload variable {n!r}, which no "
                    "pattern binds -- there is nothing to take its value from"
                )
            pay_of[n] = named(f"pay_{n}")
        return pay_of[n]

    seen = set()  # pattern variables an earlier occurrence bound: later ones join a symmetry
    literals = set()
    atom_vars = []

    def occurrence(pv, syms):
        """Enumerate each repeated occurrence's reading as an ordinary relation join."""
        names = lang.symbols_for(pvar_sorts[pv])
        sv = named(f"sym_{label(pv)}")
        syms.append(f"({names.renames} {cls_of[pv]} {sv} {cls_of[pv]})")
        return " " + sv

    for idx, atom in enumerate(atoms):
        aroot, opname, kids = atom[0], atom[1], atom[2]
        op = lang[opname]
        if len(atom) > 3:
            pays = atom[3]
        else:
            if None in op.pays:
                raise SystemExit(
                    f"{opname}: a payload column with no value. An atom built by hand must "
                    "pin every payload its operator does not."
                )
            pays = op.pays
        edges = [named(f"e{idx}_{kid_label(k, j)}") for j, k in enumerate(kids)]
        for col, p in zip((c for c in op.sig if c not in SLOTTED), pays, strict=True):
            if isinstance(p, tuple) and p[0] == "ppv":
                pay_sorts[pay_name(p[1])] = col
        if aroot not in cls_of:
            cls_of[aroot] = named(f"cls_{label(aroot)}")
        rv = cls_of[aroot]
        syms, bindings, cols, reached = [], [], [], []

        root_slots = f"({lang.symbols_for(pvar_sorts[aroot]).class_slots} {rv})"
        again = aroot in seen
        bindings.append(f'(root "{fname(aroot)}" {root_slots}{occurrence(aroot, syms) if again else ""})')
        seen.add(aroot)
        for j, (k, kid_sort, e) in enumerate(zip(kids, op.kid_sorts, edges, strict=True)):
            if k[0] == "pv":
                if k[1] not in cls_of:
                    cls_of[k[1]] = named(f"cls_{label(k[1])}")
                cols.append(cls_of[k[1]])
                # the class's exact slots, so the renaming is no wider than the class (C4)
                slots = f"({lang.symbols_for(kid_sort).class_slots} {cls_of[k[1]]})"
                again = k[1] in seen
                bindings.append(f'(child "{fname(k[1])}" {e} {slots}{occurrence(k[1], syms) if again else ""})')
                seen.add(k[1])
            elif k[0] == "sl":
                cols.append(f"({lang.symbols_for(kid_sort).var} 0)")
                literals.add(k[1])
                bindings.append(f'({"bound" if j in op.binders else "lit"} "{k[1]}" {e})')
            else:
                cv = named(f"leaf{idx}_{j}")
                cols.append(cv)
                reached.append((k[1], cv, kid_sort, j))
                bindings.append(f"(leaf {e})")
        node = node_expr(op, edges, cols, pays, pay_name)
        body.append(f"(= {rv} {node})")
        for term, cv, kid_sort, j in reached:
            table = lang.symbols_for(kid_sort).renames
            body.append(f"({table} {lang.enc(term, kid_sort)} {named(f'leafren{idx}_{j}')} {cv})")
        body.extend(syms)
        # Atom identity is independent of every user variable's spelling.
        atom_label = f"@atom:{idx}"
        av = named(f"atom_{idx}")
        body.append(f'(= {av} (atom "{atom_label}" {" ".join(bindings)}))')
        atom_vars.append(av)
    binding[0] = False

    for a, b in same:
        for v in (a, b):
            if v not in cls_of:
                raise SystemExit(f"`=` names {v!r}, which no pattern binds")
        if pvar_sorts[a] != pvar_sorts[b]:
            raise SystemExit(f"`=` cannot identify {a!r} ({pvar_sorts[a]}) with {b!r} ({pvar_sorts[b]})")
        body.append(f"(= {cls_of[a]} {cls_of[b]})")

    # the frame: every atom's constraints, joined
    refined = split = None
    if not atom_vars:
        frame = "(frame)"
    else:
        frame = atom_vars[0]
        for part in atom_vars[1:]:
            frame = f"(frame-join {frame} {part})"
        if len(atom_vars) > 1:
            fv = named("f")
            body.append(f"(= {fv} {frame})")
            frame = fv
    if anchor is not None and atoms:
        # spelled in the root's slot names, so the action's equation is at the identity
        frame = f'(anchor {frame} "{fname(anchor)}")'
    if refine and atoms:
        refined, choice = named("refined"), named("choice")
        body.append(f"(= {refined} (refinements {frame}))")
        split = len(body)
        body.append(f"(Idx {choice})")
        frame = f"(vec-get {refined} {choice})"
    fresh = sorted(set(fresh))
    if fresh:
        frame = f"(mint {frame} (names{quoted(fresh)}))"
    m = named("m")
    body.append(f"(= {m} {frame})")

    mp_of = {pv: f'(ren {m} "{fname(pv)}")' for pv in cls_of}
    slot_of = {lit: f'(map-get (ren {m} "{lit}") 0)' for lit in sorted(literals | set(fresh))}

    for want, slot, pvars in conds:
        body.append(f'({"free" if want else "not-free"} {m} "{slot}" (names{quoted(fname(v) for v in pvars)}))')
    for a, b in same:
        body.append(f'(same {m} "{fname(a)}" "{fname(b)}")')
    for a, b in diseq:
        for v in (a, b):
            if v not in cls_of:
                raise SystemExit(f"`!=` names {v!r}, which no pattern binds")
        if pvar_sorts[a] != pvar_sorts[b]:
            raise SystemExit(f"`!=` cannot compare {a!r} ({pvar_sorts[a]}) with {b!r} ({pvar_sorts[b]})")
        body.append(f'(guard (or (bool-!= {cls_of[a]} {cls_of[b]}) (not (bool-same {m} "{fname(a)}" "{fname(b)}"))))')

    return Query(
        body,
        cls_of,
        mp_of,
        slot_of,
        pvar_sorts,
        named,
        pay_name,
        frame=m,
        fname=fname,
        split=split,
        refined=refined,
        pays=pay_sorts,
    )


def build_rhs(lang, term, expected_sort, q):
    """Build an RHS bottom-up in the frame's slots: one `let` per node, and one for its
    slot set (C11). A node's slots are its named columns' through `node-slots`, plus a
    built child's, with the binders' slots taken out of what they cover. Every new
    node uses the match's numbering; congruence later merges equivalent spellings.
    """
    lets = []

    def quoted(names):
        text = " ".join(f'"{n}"' for n in names)
        return f" {text}" if text else ""

    def go(t, sort):
        if t[0] == "pv":
            actual = q.pvar_sorts[t[1]]
            if actual != sort:
                raise SystemExit(f"right-hand side uses {t[1]!r} as {sort}, but the pattern binds it as {actual}")
            return q.mp_of[t[1]], q.cls_of[t[1]], ("name", q.fname(t[1]))
        if t[0] == "sl":
            return f'(ren {q.frame} "{t[1]}")', f"({lang.symbols_for(sort).var} 0)", ("name", t[1])
        op = lang[t[0]]
        if op.sort != sort:
            raise SystemExit(f"right-hand side builds {op.name}, which produces {op.sort}, where {sort} is required")
        args, pays = op.split(t[1:])
        if not args:
            if has_pay_var(t):
                value = q.new(f"built_{op.name.lower()}")
                lets.append(f"(let {value} {node_expr(op, [], [], pays, q.pay_name)})")
                return "(map-empty)", value, ("slots", "(map-empty)")
            return map_of(lang.edge(t)), lang.enc(t, sort), ("slots", "(map-empty)")
        kids = [go(arg, child_sort) for arg, child_sort in zip(args, op.kid_sorts, strict=True)]
        value = q.new(f"built_{op.name.lower()}")
        edges = [e for e, _, _ in kids]
        lets.append(f"(let {value} {node_expr(op, edges, [c for _, c, _ in kids], pays, q.pay_name)})")
        bound = [args[i][1] for i in op.binders]
        uncovered, covered, nested = [], [], []
        for i, (_e, _c, tag) in enumerate(kids):
            inside = i in op.binders or i == op.covered
            if tag[0] == "name":
                (covered if inside else uncovered).append(tag[1])
            elif inside and bound:
                nested.append(f"(without {q.frame} {tag[1]} (names{quoted(bound)}))")
            else:
                nested.append(tag[1])
        slots = f"(node-slots {q.frame} (names{quoted(uncovered)}) (names{quoted(covered)}) (names{quoted(bound)}))"
        for n in nested:
            slots = f"(map-union {slots} {n})"
        sv = f"{value}_slots"
        lets.append(f"(let {sv} {slots})")
        return sv, value, ("slots", sv)

    edge, cls, _ = go(term, expected_sort)
    return lets, edge, cls


def pinned_slots(atoms):
    """The slot literals a pattern writes, and so solves rather than mints."""
    return {k[1] for a in atoms for k in a[2] if isinstance(k, tuple) and k[0] == "sl"}


def compile_rule(
    lang,
    atoms,
    action,
    conds=(),
    diseq=(),
    same=(),
    fresh=(),
    refine=True,
    name=None,
    ruleset=None,
    naive=False,
):
    """Compile a flattened multipattern and its action into egglog rules.

    The pattern is `compile_query`'s; this adds C11, the action, and C13, the split:
    egglog runs a body's primitives after the whole join, once per row, and the join
    includes one row per refinement index, so a rule that refined inline would build
    its frame once per index. Instead the first rule finds a match and stores its
    refinements in a relation of its own; a second rule in the `slotted-apply`
    ruleset joins that relation with `Idx`, reads one refinement, checks the
    conditions and acts; and a third, in the same ruleset, deletes the row. The
    schedule grows `Idx` to the largest stored vector's length before applying any
    matches, so every refinement acts within that same user step.

    A right-hand-side slot the pattern never pins is FRESH BY DEFINITION, so it is
    inferred rather than declared -- the reference mints one on the spot
    (`Slot::fresh()` in rewrite/ematch.rs) with nothing written by the author. An
    explicit `fresh` is still honoured and adds nothing an inferred set does not hold.

    `name` and `ruleset` are the rule's; `naive` marks an action that reads and writes
    tables, which egglog allows only in a `:naive` rule.
    """
    q = compile_query(
        lang,
        atoms,
        conds=conds,
        diseq=diseq,
        same=same,
        fresh=set(fresh) | (slot_literals(action) - pinned_slots(atoms)),
        refine=refine,
        anchor=action[1],
    )
    body, cls_of, mp_of, slot_of = q.body, q.cls_of, q.mp_of, q.slot_of
    pvar_sorts, new = q.pvar_sorts, q.new

    root = action[1]
    root_sort = pvar_sorts[root]
    root_symbols = lang.symbols_for(root_sort)
    mr = mp_of[root]
    if action[0] == "build":
        rhs = action[2]
        if rhs[0] == "pv":
            # Equate two variables. The root's renaming is the identity, `a`'s need not
            # be, which is the one action egglog's `union` cannot express -- so from
            # mr*Root = ma*A follows Root = (mr^-1 . ma) * A, stated as `Equated` for the
            # machinery to orient (C11).
            if pvar_sorts[rhs[1]] != root_sort:
                raise SystemExit(
                    f"a {root_sort} rewrite cannot return pattern variable {rhs[1]!r} of sort {pvar_sorts[rhs[1]]}"
                )
            act = [f"({root_symbols.equated} {cls_of[root]} (compose (inverse {mr}) {mp_of[rhs[1]]}) {cls_of[rhs[1]]})"]
        elif rhs[0] == SUBST:
            act = lower_substitution(lang, root, rhs, pvar_sorts, mp_of, cls_of, slot_of, new)
        else:
            # The frame is anchored at the root, so the built node is an invocation in
            # the root's own frame and egglog's `union` is exactly the equation (C11).
            lets, _, built = build_rhs(lang, rhs, root_sort, q)
            act = lets + [f"(union {built} {cls_of[root]})"]
    else:
        # A depth-one action: the same union, over a node built from bound variables.
        pvs = action[3]
        action_op = lang[action[2]]
        if action_op.sort != root_sort:
            raise SystemExit(f"a {root_sort} rule cannot build {action_op.name}, which produces {action_op.sort}")
        for pv, kid_sort in zip(pvs, action_op.kid_sorts, strict=True):
            if pvar_sorts[pv] != kid_sort:
                raise SystemExit(f"{action_op.name}: child {pv!r} has sort {pvar_sorts[pv]}, not {kid_sort}")
        node = node_expr(action_op, [mp_of[v] for v in pvs], [cls_of[v] for v in pvs], action_op.pays)
        act = [f"(union {node} {cls_of[root]})"]

    def rule(body, act, *options):
        opts = "".join(f" {o}" for o in options if o)
        return "(rule (" + "\n       ".join(body) + ")\n      (" + "\n       ".join(act) + ")" + opts + ")"

    in_ruleset = f":ruleset {ruleset}" if ruleset else None
    if q.split is None:
        return rule(body, act, ":naive" if naive else None, in_ruleset, f':name "{name}"' if name else None)
    # C13: one row per match, its refinements and the classes the action reads
    columns = [q.refined, *cls_of.values(), *sorted(q.pays)]
    sorts = ["Frames", *(pvar_sorts[v] for v in cls_of), *(q.pays[v] for v in sorted(q.pays))]
    relation = match_relation(name, [*body[: q.split], *act])
    row = f"({relation} {' '.join(columns)})"
    return "\n".join(
        [
            f"(relation {relation} ({' '.join(sorts)}))",
            rule(
                body[: q.split],
                [row, f"(set (RefinementCount) (vec-length {q.refined}))"],
                in_ruleset,
                f':name "{name}"' if name else None,
            ),
            rule(
                [row, *body[q.split :]],
                act,
                ":naive" if naive else None,
                ":ruleset slotted-apply",
                f':name "{name}/apply"' if name else None,
            ),
            # every stored row is spent once the acting rule has read it, whether or not
            # a refinement passed the conditions; egglog finds a ruleset's matches
            # before it applies any action, so the drain never hides a row from it
            rule([row], [f"(delete {row})"], ":ruleset slotted-apply", f':name "{name}/drain"' if name else None),
        ]
    )


def match_relation(name, text):
    """The relation a rule's matches wait in: named after the rule, or after a hash of
    its match and action when the rule has no name, since two unnamed rules may share a
    match and differ in what they do with it. The `_` prefix is the compiler's, which no
    author's name begins with."""
    if name:
        stem = "".join(c if c.isalnum() or c in "-_" else "_" for c in name)
    else:
        stem = hashlib.sha1("\n".join(text).encode()).hexdigest()[:10]
    return f"_matched_{stem}"
