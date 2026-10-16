"""Slotted timing tables and correctness evidence from the shared report cache.

This module is also embedded in the interactive report. It only reads records;
no binary, reference library, compiler, or graph search is needed to render it.
"""

from __future__ import annotations

import re
from collections.abc import Sequence
from datetime import datetime

from .catalog import (
    ReportBlock,
    ReportCatalog,
    ReportColumn,
    ReportMessage,
    ReportRow,
    ReportSection,
    ReportTable,
    text_cell,
)
from .store import ReportRecord, SlottedEvidence

SIDES = ("encoding", "encoding-no-aliasing", "ref-multi", "ref-nested-snapshot", "ref-nested")
EXACT_PAIRS = {"encoding": "ref-multi", "encoding-no-aliasing": "ref-nested-snapshot"}
LABELS = {"encoding": "egglog", "encoding-no-aliasing": "egglog-no-aliasing"}


def workload_label(study: str, case: str, rules: int | None) -> str:
    """Paper labels shared by the terminal and nightly reports."""
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
    """A timeout is a censored observation, not a completed execution time."""
    if goal == "timeout":
        return "timeout"
    return "" if seconds is None else f"{seconds:.3g}"


def _label(evidence: SlottedEvidence) -> str:
    return workload_label(evidence["study"], evidence["case"], evidence["rules"])


def comparison_issue(encoding: SlottedEvidence, reference: SlottedEvidence | None) -> str | None:
    """Check raw counts and the exact certificate's observation identities."""
    if reference is None:
        return "inconclusive: reference observation unavailable"
    for name in ("classes", "nodes"):
        a, b = encoding[name], reference[name]
        if a is None or b is None:
            return "inconclusive: counts unavailable"
        if a != b:
            return f"different: {name} {a} vs {b} (encoding vs reference)"
    certificate = encoding["vs_ref"].get(reference["side"])
    if certificate is None or (certificate["encoding"], certificate["reference"]) != (
        encoding["observation"],
        reference["observation"],
    ):
        return "inconclusive: selected observations have not been compared"
    return None if certificate["verdict"] == "isomorphic" else certificate["verdict"]


def slotted_catalog(records: Sequence[ReportRecord]) -> ReportCatalog:
    """Show the latest workload versions, with no unverified equality claims.

    Workload hashes include the rewrite budget and checking policy. After choosing
    the latest version of each named workload, only matching hashes are shown.
    Within that version each side retains its own latest binary and provenance.
    """
    ordered = sorted(
        (
            (datetime.fromisoformat(record["started_at"]), i, record)
            for i, record in enumerate(records)
            if "slotted" in record
        ),
        key=lambda item: item[:2],
    )
    versions: dict[tuple[str, str], str] = {}
    for _, _, record in ordered:
        evidence = record["slotted"]
        versions[evidence["study"], evidence["case"]] = record["file_sha256"]
    groups: dict[tuple[str, str], dict[str, ReportRecord]] = {key: {} for key in versions}
    for _, _, record in ordered:
        evidence = record["slotted"]
        key = evidence["study"], evidence["case"]
        if record["file_sha256"] == versions[key]:
            groups[key][evidence["side"]] = record
    if not groups:
        return ReportCatalog(())

    blocks: list[ReportBlock] = []
    for name, title, pair in (
        ("multi", "Multipattern matching", ("encoding", "ref-multi")),
        ("nested", "Nested matching", ("encoding-no-aliasing", "ref-nested")),
    ):
        rows = []
        for key, group in groups.items():
            first = next(iter(group.values()))["slotted"]
            cells = [text_cell(_label(first))]
            for side in pair:
                value = group.get(side)
                seconds = None if value is None else value["wall_sec"]
                label = "—" if value is None else elapsed_time(seconds, value["slotted"]["goal"]) or "—"
                cells.append(text_cell(seconds, label))
            rows.append(ReportRow("/".join(key), tuple(cells)))
        blocks.append(
            ReportTable(
                "slotted-" + name,
                title,
                (
                    ReportColumn("benchmark", "Benchmark"),
                    *(ReportColumn(side, LABELS.get(side, side), "right") for side in pair),
                ),
                tuple(rows),
                "Seconds from one process; timeout means the time limit was reached. Latest cached workload versions; "
                "rewrite budgets, provenance and correctness results are below. "
                "Snapshot reference timings are diagnostic only.",
            )
        )

    errors: list[str] = []
    details = []
    for key, group in groups.items():
        label = _label(next(iter(group.values()))["slotted"])
        for side in SIDES:
            selected = group.get(side)
            if selected is None:
                errors.append(f"{label}: missing {LABELS.get(side, side)} observation.")
                continue
            record = selected
            evidence = record["slotted"]
            if evidence["goal"] != "yes":
                errors.append(f"{label} / {LABELS.get(side, side)}: goal not reached ({evidence['goal']}).")
            verdict = "—"
            if side in EXACT_PAIRS:
                if not evidence["counts"]:
                    verdict = "disabled"
                    errors.append(f"{label} / {LABELS.get(side, side)}: counts and isomorphism checks disabled.")
                else:
                    reference = group.get(EXACT_PAIRS[side])
                    issue = comparison_issue(evidence, None if reference is None else reference["slotted"])
                    verdict = issue or "isomorphic"
                    if issue:
                        errors.append(f"{label}: {LABELS.get(side, side)} vs {EXACT_PAIRS[side]}: {issue}")
            provenance = f"{record['target_label'] or record['target_source']} {record['target_git_sha'][:12]}"
            if record["target_is_dirty"]:
                provenance += " dirty"
            details.append(
                ReportRow(
                    "/".join((*key, side)),
                    tuple(
                        text_cell(value)
                        for value in (
                            label,
                            LABELS.get(side, side),
                            evidence["rounds"],
                            record["timeout_sec"],
                            evidence["jobs"],
                            evidence["goal"],
                            evidence["classes"],
                            evidence["nodes"],
                            verdict,
                            evidence["graph_issue"],
                            provenance,
                            record["binary_sha256"],
                            record["started_at"],
                        )
                    ),
                )
            )
    if errors:
        blocks.append(
            ReportMessage(
                "slotted-errors", "SLOTTED CORRECTNESS CHECKS FAILED OR INCOMPLETE", "\n".join(errors), "error"
            )
        )
    headers = (
        "Benchmark",
        "Treatment",
        "Iterations",
        "Timeout (s)",
        "Jobs",
        "Goal",
        "Classes",
        "Nodes",
        "Exact comparison",
        "Graph issue",
        "Target",
        "Binary SHA-256",
        "Collected",
    )
    blocks.append(
        ReportTable(
            "slotted-evidence",
            "Slotted correctness and provenance",
            tuple(ReportColumn(str(i), name) for i, name in enumerate(headers)),
            tuple(details),
            "egglog must match ref-multi; egglog-no-aliasing must match ref-nested-snapshot. "
            "Both class/node counts and a verified isomorphism are required. "
            "Parallel samples include resource contention.",
        )
    )
    return ReportCatalog((ReportSection("slotted", "Slotted e-graphs", tuple(blocks)),))
