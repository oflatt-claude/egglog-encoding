"""Select slotted observations and build the CLI and nightly report.

Only shared cache records enter this module. Workload generation, subprocesses,
and graph search stay in the collector; rendering also works in the browser.
"""

from __future__ import annotations

import re
from collections import Counter
from collections.abc import Sequence
from dataclasses import dataclass
from datetime import datetime

from .catalog import (
    ReportBlock,
    ReportCatalog,
    ReportColumn,
    ReportMessage,
    ReportRow,
    ReportScalar,
    ReportSection,
    ReportTable,
    report_id,
    text_cell,
)
from .store import ReportRecord, SlottedEvidence

SIDES = ("encoding", "encoding-no-aliasing", "ref-multi", "ref-nested-snapshot", "ref-nested")
EXACT_PAIRS = {"encoding": "ref-multi", "encoding-no-aliasing": "ref-nested-snapshot"}
LABELS = {"encoding": "egglog", "encoding-no-aliasing": "egglog-no-aliasing"}
ERROR_TITLE = "SLOTTED CORRECTNESS CHECKS FAILED OR INCOMPLETE"
type Workload = tuple[str, str, int, int | None]


@dataclass(frozen=True)
class SlottedReport:
    """The error banner and CLI exit status come from the same checks."""

    catalog: ReportCatalog
    errors: tuple[str, ...]


def workload_label(study: str, case: str, rules: int | None) -> str:
    if study == "array" and (match := re.fullmatch(r"goal-2d-4f-N(\d+)", case)):
        return "Array N=" + match[1]
    if study == "sdql" and (
        match := re.fullmatch(r"(mmm_sum|mttkrp|mmm|ttm|batax)_(1st|2nd)-" + str(rules) + "rules", case)
    ):
        kernel, phase = match.groups()
        name = "ΣMMM" if kernel == "mmm_sum" else kernel.upper()
        suffix = f", {rules} rules" if rules != 44 else ""
        return f"{name} ({phase}{suffix})"
    suffix = f" ({rules} rules)" if rules is not None else ""
    return f"{study}: {case}{suffix}"


def elapsed_time(seconds: float | None, goal: str) -> str:
    """Completed processes retain elapsed time, even if they missed the goal."""
    if goal == "timeout":
        return "timeout"
    return "—" if seconds is None else f"{seconds:.3g}"


def count_issue(encoding: SlottedEvidence, reference: SlottedEvidence) -> str | None:
    """Raw counts independently constrain every positive isomorphism verdict."""
    missing = False
    for name in ("classes", "nodes"):
        a, b = encoding[name], reference[name]
        if a is None or b is None:
            missing = True
        elif a != b:
            return f"different: {name} {a} vs {b} (encoding vs reference)"
    return "inconclusive: counts unavailable" if missing else None


def comparison_verdict(encoding: SlottedEvidence, reference: SlottedEvidence | None) -> str:
    """A certificate applies only to the two observations it names."""
    if reference is None:
        return "inconclusive: reference observation unavailable"
    certificate = encoding["vs_ref"].get(reference["side"])
    if certificate is None or (certificate["encoding"], certificate["reference"]) != (
        encoding["observation"],
        reference["observation"],
    ):
        return "inconclusive: selected observations have not been compared"
    return certificate["verdict"]


def comparison_issue(encoding: SlottedEvidence, reference: SlottedEvidence | None) -> str | None:
    if reference is not None and (issue := count_issue(encoding, reference)):
        return issue
    verdict = comparison_verdict(encoding, reference)
    return None if verdict == "isomorphic" else verdict


def _workload(evidence: SlottedEvidence) -> Workload:
    return evidence["study"], evidence["case"], evidence["rounds"], evidence["rules"]


def select_slotted_records(records: Sequence[ReportRecord]) -> tuple[ReportRecord, ...]:
    """Select each named workload/budget's latest version, then its latest sides.

    Versions include the generated inputs, checking policy, parallelism, and
    timeout. A partial new version leaves missing sides; it cannot borrow old
    timings or certificates. Different rewrite budgets remain separate rows.
    """
    ordered = sorted(
        (
            (datetime.fromisoformat(record["started_at"]), i, record)
            for i, record in enumerate(records)
            if "slotted" in record
        ),
        key=lambda item: item[:2],
    )
    versions: dict[Workload, tuple[str, int]] = {}
    for _, _, record in ordered:
        versions[_workload(record["slotted"])] = record["file_sha256"], record["timeout_sec"]
    groups: dict[Workload, dict[str, ReportRecord]] = {key: {} for key in versions}
    for _, _, record in ordered:
        evidence = record["slotted"]
        key = _workload(evidence)
        if (record["file_sha256"], record["timeout_sec"]) == versions[key]:
            groups[key][evidence["side"]] = record
    return tuple(record for group in groups.values() for record in group.values())


def _row(identity: str, *values: ReportScalar) -> ReportRow:
    return ReportRow(identity, tuple(text_cell(value) for value in values))


def slotted_report(
    records: Sequence[ReportRecord], *, sides: Sequence[str] = SIDES, counts: bool = True
) -> SlottedReport:
    """Build timing tables and evidence using one selection and correctness policy."""
    groups: dict[Workload, dict[str, ReportRecord]] = {}
    for record in select_slotted_records(records):
        evidence = record["slotted"]
        groups.setdefault(_workload(evidence), {})[evidence["side"]] = record
    names = Counter(workload_label(study, case, rules) for study, case, _, rules in groups)
    labels = {
        key: workload_label(key[0], key[1], key[3])
        + (f" [{key[2]} rounds]" if names[workload_label(key[0], key[1], key[3])] > 1 else "")
        for key in groups
    }
    note = (
        "Elapsed seconds for completed runs, including missed goals; timeout means the time limit was reached. "
        "ref-nested uses syntactic substitution; snapshot-reference timings are diagnostic only. "
        "Each workload/budget shows its latest cached version. Parallel timings include resource contention."
    )
    if not counts:
        note += " Class/node counts and isomorphism checks are disabled (--no-counts)."
    blocks: list[ReportBlock] = []
    for name, title, pair in (
        ("multi", "Multipattern matching", ("encoding", "ref-multi")),
        ("nested", "Nested matching", ("encoding-no-aliasing", "ref-nested")),
    ):
        shown = tuple(side for side in pair if side in sides)
        if not shown:
            continue
        timing_rows = []
        for key, group in groups.items():
            cells = [text_cell(labels[key])]
            for side in shown:
                value = group.get(side)
                seconds = None if value is None else value["wall_sec"]
                label = "—" if value is None else elapsed_time(seconds, value["slotted"]["goal"])
                cells.append(text_cell(seconds, label))
            timing_rows.append(ReportRow(report_id(*key[:3], str(key[3])), tuple(cells)))
        blocks.append(
            ReportTable(
                "slotted-" + name,
                title,
                (ReportColumn("benchmark", "Benchmark"), *(ReportColumn(s, LABELS.get(s, s), "right") for s in shown)),
                tuple(timing_rows),
                note,
            )
        )

    errors: list[str] = [] if groups else ["No benchmark results."]
    sizes, comparisons, configuration, provenance_rows, graph_issues = [], [], [], [], []
    for key, group in groups.items():
        label = labels[key]
        for side in sides:
            selected = group.get(side)
            if selected is None:
                errors.append(f"{label}: missing {LABELS.get(side, side)} observation.")
                continue
            record = selected
            evidence = record["slotted"]
            if evidence["goal"] != "yes":
                errors.append(f"{label} / {LABELS.get(side, side)}: goal not reached ({evidence['goal']}).")
            name = LABELS.get(side, side)
            identity = evidence["observation"]
            if side in EXACT_PAIRS:
                for ref in sides:
                    if ref != EXACT_PAIRS[side] and ref not in evidence["vs_ref"]:
                        continue
                    reference = group.get(ref)
                    issue = comparison_issue(evidence, None if reference is None else reference["slotted"])
                    if not counts or not evidence["counts"]:
                        issue = "counts and isomorphism checks disabled"
                    comparisons.append(_row(report_id(identity, ref), label, name, ref, issue or "isomorphic"))
                    if counts and ref == EXACT_PAIRS[side] and issue:
                        errors.append(f"{label}: {LABELS.get(side, side)} vs {ref}: {issue}")
            provenance = f"{record['target_label'] or record['target_source']} {record['target_git_sha'][:12]}"
            if record["target_is_dirty"]:
                provenance += " dirty"
            paper = evidence["paper"]
            paper_text = "" if paper is None else f"{paper[0]}, {paper[1]}, {paper[2]}, {'yes' if paper[3] else 'no'}"
            sizes.append(
                _row(
                    identity,
                    label,
                    name,
                    evidence["rounds"],
                    elapsed_time(record["wall_sec"], evidence["goal"]),
                    evidence["goal"],
                    evidence["classes"],
                    evidence["nodes"],
                    evidence["saturated"],
                )
            )
            configuration.append(
                _row(
                    identity,
                    label,
                    name,
                    record["timeout_sec"],
                    evidence["jobs"],
                    evidence["checks"],
                    evidence["substitution"],
                    paper_text,
                )
            )
            provenance_rows.append(
                _row(
                    identity,
                    label,
                    name,
                    provenance,
                    record["binary_sha256"],
                    record["started_at"],
                )
            )
            if evidence["graph_issue"]:
                graph_issues.append(_row(identity, label, name, evidence["graph_issue"]))
    if errors:
        blocks.append(ReportMessage("slotted-errors", ERROR_TITLE, "\n".join(errors), "error"))
    tables = (
        (
            "sizes",
            "Slotted e-graph sizes",
            ("Benchmark", "Treatment", "Iterations", "Seconds", "Goal", "Classes", "Nodes", "Saturated"),
            sizes,
            None,
        ),
        (
            "comparisons",
            "Slotted graph comparisons",
            ("Benchmark", "Encoding", "Reference", "Verdict"),
            comparisons,
            "egglog must match ref-multi; egglog-no-aliasing must match ref-nested-snapshot, when both are selected. "
            "Equal raw class/node counts and a verified isomorphism are both required. "
            "Other comparisons are diagnostic.",
        ),
        ("diagnostics", "Slotted graph diagnostics", ("Benchmark", "Treatment", "Issue"), graph_issues, None),
        (
            "configuration",
            "Slotted run configuration",
            ("Benchmark", "Treatment", "Timeout (s)", "Jobs", "Reference checks", "Substitution", "Paper sizes"),
            configuration,
            "Paper sizes lists iterations, nodes, classes, and saturation from Table 1.",
        ),
        (
            "provenance",
            "Slotted provenance",
            ("Benchmark", "Treatment", "Target", "Binary SHA-256", "Collected"),
            provenance_rows,
            None,
        ),
    )
    for name, title, headers, rows, caption in tables:
        if rows:
            blocks.append(
                ReportTable(
                    "slotted-" + name,
                    title,
                    tuple(ReportColumn(str(i), name) for i, name in enumerate(headers)),
                    tuple(rows),
                    caption,
                )
            )
    return SlottedReport(ReportCatalog((ReportSection("slotted", "Slotted e-graphs", tuple(blocks)),)), tuple(errors))
