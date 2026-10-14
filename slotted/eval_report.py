"""Observation records and tables for slotted/slotted-eval.py.

No processes are launched here. Comparison evidence is tied to both observation
IDs, so merging cache batches cannot turn an unchecked pair into a verified one.
"""

import sys
import threading
import uuid
from collections import Counter
from dataclasses import asdict, dataclass

from benchmarking.reports.slotted import EXACT_PAIRS as EXACT_PAIRS
from benchmarking.reports.slotted import LABELS, workload_label
from benchmarking.reports.slotted import SIDES as SIDES


def side_label(side):
    """Display names; CLI selectors and cached treatment identities stay stable."""
    return LABELS.get(side, side)


def quiet_progress(row, phase):
    """Library callers collect observations without displaying CLI progress."""


class Progress:
    """One dot per sample; identify a phase only when it takes more than five seconds.

    Timer callbacks only print to stderr. Cancel and join before changing the display
    so a completed phase cannot report itself as still running.
    """

    delay = 5

    def __init__(self, parallel=False):
        self.timer = None
        self.workload = None
        self.line_open = False
        self.parallel = parallel

    def __enter__(self):
        return self

    def cancel(self):
        if self.timer is not None:
            self.timer.cancel()
            self.timer.join()
            self.timer = None

    def __exit__(self, *_):
        self.cancel()
        if self.line_open:
            print(file=sys.stderr, flush=True)

    def __call__(self, row, phase):
        self.cancel()
        if phase == "idle":
            return
        label = workload_label(row.study, row.case, row.rules)
        if self.parallel and phase == "done":
            print(".", end="", file=sys.stderr, flush=True)
            return
        if not self.parallel and row.workload() != self.workload:
            if self.line_open:
                print(file=sys.stderr)
            print(f"{label}: ", end="", file=sys.stderr, flush=True)
            self.workload, self.line_open = row.workload(), True
        if phase == "done":
            print("." if self.line_open else "  .", end="", file=sys.stderr, flush=True)
            self.line_open = True
            return

        def slow():
            if self.parallel:
                # Write a complete, short message at once so workers' text does not
                # interleave inside a message. Dots may arrive between messages.
                sys.stderr.write(f"\n  {label} / {row.side}: {phase} (Running ...)\n")
                sys.stderr.flush()
                return
            if self.line_open:
                print(file=sys.stderr)
            print(f"  {label} / {row.side}: {phase} (Running ...)", file=sys.stderr, flush=True)
            self.line_open = False

        self.timer = threading.Timer(self.delay, slow)
        self.timer.daemon = True
        self.timer.start()


@dataclass(frozen=True)
class Comparison:
    """A verdict about exactly two observations, including inconclusive outcomes."""

    encoding: str
    reference: str
    verdict: str


class Row:
    def __init__(self, study, case, side, rounds, rules=None):
        self.study, self.case, self.side, self.rounds, self.rules = study, case, side, rounds, rules
        self.jobs = 1
        self.observation = uuid.uuid4().hex
        self.goal, self.saturated, self.seconds = "?", "?", None
        self.classes, self.nodes = None, None
        self.checks = None  # the oracle's `CONFIG checks=` answer, for reference sides
        self.substitution = None  # the oracle's `CONFIG substitution=` answer
        self.paper = None  # Table 1's slotted row for this workload, when it has one
        #: encoding side: per reference side, how its final graph compares (`compare`)
        self.vs_ref = {}
        self.graph = None  # only used during comparison; not recorded in the cache
        self.graph_issue = None

    def workload(self):
        return self.study, self.case, self.rounds, self.rules

    def verdict(self, reference):
        if reference is None:
            return "inconclusive: reference observation unavailable"
        comparison = self.vs_ref.get(reference.side)
        if comparison is None:
            return "inconclusive: observations have not been compared"
        if (comparison.encoding, comparison.reference) != (self.observation, reference.observation):
            return "inconclusive: selected observations have not been compared"
        return comparison.verdict

    def as_dict(self, batch):
        """Untimed evidence; the shared cache owns timing and endpoint provenance."""
        d = {key: value for key, value in vars(self).items() if key not in ("graph", "seconds")}
        d["vs_ref"] = {side: asdict(comparison) for side, comparison in self.vs_ref.items()}
        d["batch"] = batch
        d["counts"] = True
        return d

    @classmethod
    def from_dict(cls, evidence):
        row = cls(evidence["study"], evidence["case"], evidence["side"], evidence["rounds"], evidence["rules"])
        for field in (
            "observation",
            "jobs",
            "goal",
            "saturated",
            "classes",
            "nodes",
            "checks",
            "substitution",
            "graph_issue",
        ):
            setattr(row, field, evidence[field])
        row.paper = tuple(evidence["paper"]) if evidence["paper"] is not None else None
        row.vs_ref = {side: Comparison(**comparison) for side, comparison in evidence["vs_ref"].items()}
        return row


# ------------------------------------------------------------------------- output
LONG_HEAD = (
    "study",
    "case",
    "side",
    "rounds",
    "rules",
    "jobs",
    "goal",
    "saturated",
    "seconds",
    "classes",
    "nodes",
    "vs reference",
    "graph issue",
    "paper (iters, nodes, classes, sat.)",
)
SUMMARY_NOTE = (
    "Seconds, including unsuccessful runs; — means unavailable. "
    "SDQL uses 44 rules unless noted. ref-nested uses syntactic substitution. "
    "Budgets, graph sizes, and snapshot-reference timings are in the full report."
)
ERROR_TITLE = "ERROR: evaluation checks failed"


def paper_cell(r):
    return "" if r.paper is None else f"{r.paper[0]}, {r.paper[1]:,}, {r.paper[2]:,}, {'yes' if r.paper[3] else 'no'}"


def long_cells(r):
    """One row's cells, as text, in `LONG_HEAD` order: the record of one run."""
    side = side_label(r.side) + reference_label(r)
    counts = ["" if n is None else str(n) for n in (r.classes, r.nodes)]
    return [
        r.study,
        r.case,
        side,
        str(r.rounds),
        str(r.rules or ""),
        str(r.jobs),
        r.goal,
        r.saturated,
        seconds_cell(r),
        *counts,
        vs_cell(r),
        r.graph_issue or "",
        paper_cell(r),
    ]


def vs_cell(r):
    return "; ".join(f"{side_label(side)}: {comparison.verdict}" for side, comparison in r.vs_ref.items())


def seconds_cell(r):
    return "" if r.seconds is None else f"{r.seconds:.3g}"


def graph_cell(r):
    """The final graph's size and saturation status, independent of goal outcome."""
    if r.classes is not None:
        return f"{r.classes}/{r.nodes}" + (f", sat. {r.saturated}" if r.saturated != "?" else "")
    return f"counts unavailable: {r.graph_issue}" if r.graph_issue else ""


def reference_label(*rows):
    labels = []
    for field, label in (("checks", "checks"), ("substitution", "subst")):
        values = {getattr(row, field) for row in rows}
        known = sorted(v for v in values if v is not None)
        if known:
            detail = "/".join(known)
            if None in values:
                detail += "/unknown"
            labels.append(f"{label} {detail}")
    if any(row.jobs > 1 for row in rows):
        labels.append("jobs " + "/".join(map(str, sorted({row.jobs for row in rows}))))
    return f" ({', '.join(labels)})" if labels else ""


def pivot(rows, sides):
    """One row per workload, with each side's goal, elapsed time, and graph separate."""
    columns = []
    for side in sides:
        label = reference_label(*(r for r in rows if r.side == side))
        name = side_label(side)
        columns.extend((f"{name} goal{label}", f"{name} elapsed (s)", f"{name} graph (classes/nodes, sat.)"))
    # the encoding's graph against each reference side it was compared with
    compared = [(e, s) for e in sides for s in sides if any(r.side == e and s in r.vs_ref for r in rows)]
    head = [
        "study",
        "case",
        "rounds",
        "rules",
        *columns,
        *(f"{side_label(e)} vs {side_label(s)}" for e, s in compared),
        "paper (iters, nodes, classes, sat.)",
    ]
    by_case, order = {}, []
    for r in rows:
        key = r.workload()
        if key not in by_case:
            by_case[key] = {"paper": paper_cell(r)}
            order.append(key)
        by_case[key][r.side] = [r.goal, seconds_cell(r), graph_cell(r)]
        for s, comparison in r.vs_ref.items():
            by_case[key][f"{r.side} vs {s}"] = comparison.verdict
    table = []
    for study, case, rounds, rules in order:
        got = by_case[(study, case, rounds, rules)]
        cells = [cell for s in sides for cell in got.get(s, ["", "", ""])]
        cells += [got.get(f"{e} vs {s}", "") for e, s in compared]
        table.append([study, case, str(rounds), str(rules or ""), *cells, got["paper"]])
    return head, table


def summary(rows, sides):
    """One benchmark per row, one timing per treatment; keep snapshot timings diagnostic."""
    shown = tuple(side for side in sides if side != "ref-nested-snapshot")
    head = ("Benchmark", *(side_label(side) for side in shown))
    groups = {}
    for row in rows:
        groups.setdefault(row.workload(), {})[row.side] = row
    labels = Counter(workload_label(study, case, rules) for study, case, _rounds, rules in groups)
    table = []
    for (study, case, rounds, rules), group in groups.items():
        label = workload_label(study, case, rules)
        if labels[label] > 1:
            label += f" [{rounds} rounds]"
        table.append([label, *(seconds_cell(group[side]) or "—" if side in group else "—" for side in shown)])
    return head, table


def report_sections(rows, sides, long=False, *, counts=True):
    full = (LONG_HEAD, [long_cells(r) for r in rows]) if long else pivot(rows, sides)
    note = SUMMARY_NOTE
    note += (
        " Checks require equal class/node counts and verified isomorphism for "
        "egglog ↔ ref-multi and egglog-no-aliasing ↔ ref-nested-snapshot (when both selected)."
        if counts
        else " Class/node counts and isomorphism checks are disabled (--no-counts)."
    )
    if any(row.jobs > 1 for row in rows):
        note += (
            " Includes parallel timings with CPU and memory contention; worker limits are in the full report. "
            "Use --jobs 1 for serial timings."
        )
    pairs = (
        ("Multipattern matching", ("encoding", "ref-multi")),
        ("Nested matching", ("encoding-no-aliasing", "ref-nested")),
    )
    sections = []
    for title, pair in pairs:
        shown = tuple(side for side in pair if side in sides)
        if shown:
            sections.append((title, "", *summary(rows, shown)))
    if sections:
        title, _, head, table = sections[-1]
        sections[-1] = title, note, head, table
    return [*sections, ("Full report", "" if sections else note, *full)]


def markdown(head, table, *, right_align=False):
    """A Markdown table with its columns padded, so it also reads aligned in a terminal."""
    table = [list(head)] + table
    widths = [max(len(row[i]) for row in table) for i in range(len(head))]

    def line(cells):
        return (
            "| "
            + " | ".join(
                c.rjust(w) if right_align and i else c.ljust(w)
                for i, (c, w) in enumerate(zip(cells, widths, strict=True))
            )
            + " |"
        )

    rule = "|" + "|".join("-" * (w + 1) + (":" if right_align and i else "-") for i, w in enumerate(widths)) + "|"
    return "\n".join([line(table[0]), rule] + [line(c) for c in table[1:]])


def markdown_report(sections, errors=()):
    blocks = []
    for title, note, head, table in sections:
        if title == "Full report" and errors:
            blocks.append(f"## {ERROR_TITLE}\n\n" + "\n".join(f"- {error}" for error in errors))
        blocks.append(
            f"## {title}\n\n{markdown(head, table, right_align=title != 'Full report')}"
            + (f"\n\n{note}" if note else "")
        )
    return "\n\n".join(blocks)


def html(sections, errors=()):
    """The summary and full table as a standalone page."""
    import html as h

    contents = []
    for title, note, head, table in sections:
        if title == "Full report" and errors:
            contents.append(
                f'<aside class="errors" role="alert"><h2>{ERROR_TITLE}</h2><ul>'
                + "".join(f"<li>{h.escape(error)}</li>" for error in errors)
                + "</ul></aside>"
            )
        head_cells = "".join(f"<th>{h.escape(c)}</th>" for c in head)
        body = []
        for cells in table:
            row_class = ' class="group"' if cells[0] else ""
            body.append(f"<tr{row_class}>" + "".join(f"<td>{h.escape(c)}</td>" for c in cells) + "</tr>")
        section_class = ' class="summary"' if title != "Full report" else ""
        contents.append(
            f"<section{section_class}><h2>{h.escape(title)}</h2><div class=scroll>"
            f"<table><thead><tr>{head_cells}</tr></thead><tbody>\n"
            + "\n".join(body)
            + "\n</tbody></table></div>"
            + (f"<p>{h.escape(note)}</p>" if note else "")
            + "</section>"
        )
    return (
        "<!doctype html><meta charset=utf-8><meta name=viewport content='width=device-width, initial-scale=1'>"
        "<title>slotted eval</title>"
        "<style>body{font:14px system-ui,sans-serif;margin:2em}table{border-collapse:collapse}"
        "section{margin-bottom:2.5em}.scroll{overflow-x:auto}p{max-width:85ch;color:#555;line-height:1.5}"
        "th,td{border:1px solid #bbb;padding:4px 10px;text-align:left;white-space:nowrap}"
        "th{background:#eee}tr:nth-child(even){background:#f7f7f7}"
        ".summary th,.summary td{border:0;padding:6px 12px}"
        ".summary tr{background:none}"
        ".summary th{background:none;border-bottom:2px solid #777}"
        ".summary tr.group td{border-top:1px solid #ccc}"
        ".summary th:nth-child(n+2),.summary td:nth-child(n+2){text-align:right}"
        ".summary td{font-variant-numeric:tabular-nums}"
        ".errors{border:3px solid #b91c1c;background:#fef2f2;color:#7f1d1d;padding:1em 1.5em;margin:1.5em 0}"
        ".errors h2{margin-top:0}.errors li{margin:.5em 0;overflow-wrap:anywhere}"
        "</style>\n" + "\n".join(contents) + "\n"
    )
