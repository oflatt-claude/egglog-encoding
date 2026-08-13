"""Construct benchmark report records, targets, endpoints, and JSONL fixtures."""

from __future__ import annotations

from pathlib import Path
from typing import Literal

from benchmarking import models
from benchmarking.reports.store import (
    REPORT_SCHEMA_VERSION,
    ReportRecord,
    ReportStore,
    TimingLeafRecord,
    TimingSummaryRecord,
)

ROOT = Path(__file__).resolve().parents[1]


def make_record(
    _index: int,
    *,
    started_at: str,
    status: models.Status = "success",
    wall_sec: float | None = 1.0,
    max_rss_bytes: int | None = None,
    binary_sha256: str = "sha256:bin",
    file_sha256: str = "sha256:file",
    fact_directory_sha256: str = "",
    treatment: models.Treatment = "off",
    timeout_sec: int = 120,
    target_label: str | None = None,
    timing_summary: TimingSummaryRecord | None = None,
) -> ReportRecord:
    if status == "success" and timing_summary is None:
        timing_summary = make_timing_summary()
    return {
        "report_schema_version": REPORT_SCHEMA_VERSION,
        "started_at": started_at,
        "status": status,
        "target_label": target_label,
        "target_source": ".",
        "target_path": str(ROOT),
        "target_git_ref": "HEAD",
        "target_git_sha": "abc123",
        "target_is_dirty": False,
        "binary_sha256": binary_sha256,
        "file_path": "file.egg",
        "file_sha256": file_sha256,
        "fact_directory_path": None,
        "fact_directory_sha256": fact_directory_sha256,
        "treatment": treatment,
        "timeout_sec": timeout_sec,
        "wall_sec": None if status == "timed-out" else wall_sec,
        "max_rss_bytes": None if status == "timed-out" else max_rss_bytes,
        "error_exit_code": None,
        "error_signal": None,
        "error_message": "timed out" if status == "timed-out" else None,
        "timing_summary": timing_summary if status == "success" else None,
    }


def make_ruleset_timing(
    name: str = "rules",
    *,
    assembly_ns: int = 0,
    search_ns: int = 400_000_000,
    apply_ns: int = 200_000_000,
    execution_ns: int = 0,
    merge_ns: int = 200_000_000,
    rebuild_ns: int = 100_000_000,
    role: Literal["program", "equality"] = "program",
) -> tuple[TimingLeafRecord, ...]:
    """Construct one valid ruleset timing fixture."""

    responsibility = "equality" if role == "equality" else "program"
    return (
        {"path": [responsibility, "assembly", name], "ns": assembly_ns},
        {"path": [responsibility, "search", name], "ns": search_ns},
        {"path": [responsibility, "apply", name], "ns": apply_ns},
        {"path": [responsibility, "execution", name], "ns": execution_ns},
        {"path": [responsibility, "merge", name], "ns": merge_ns},
        {"path": ["equality", "rebuild", name], "ns": rebuild_ns},
    )


def make_timing_summary(
    *rulesets: tuple[TimingLeafRecord, ...],
    typecheck_ns: int = 0,
    frontend_parse_ns: int = 0,
    frontend_other_ns: int = 0,
    frontend_install_ns: int = 0,
    commands_actions_ns: int = 0,
    commands_check_ns: int = 0,
    commands_other_ns: int = 0,
) -> TimingSummaryRecord:
    """Construct a valid V3 timing-summary fixture."""

    timing_groups = rulesets or (make_ruleset_timing(),)
    timings: list[TimingLeafRecord] = [
        {"path": ["typecheck", "total"], "ns": typecheck_ns},
        {"path": ["frontend", "parse"], "ns": frontend_parse_ns},
        {"path": ["frontend", "other"], "ns": frontend_other_ns},
        {"path": ["frontend", "install"], "ns": frontend_install_ns},
        {"path": ["commands", "actions"], "ns": commands_actions_ns},
        {"path": ["commands", "check"], "ns": commands_check_ns},
        {"path": ["commands", "other"], "ns": commands_other_ns},
    ]
    timings.extend(leaf for group in timing_groups for leaf in group)
    timings.sort(key=lambda leaf: leaf["path"])
    return {
        "schema_version": 3,
        "timings": timings,
    }


def write_report(path: Path, *records: ReportRecord) -> None:
    """Write deterministic fixtures through the production JSONL boundary."""

    store = ReportStore(path)
    for record in records:
        store.append(record)


def make_target(
    *,
    target_label: str | None = None,
    binary_sha256: str = "sha256:bin",
    binary_path: Path | None = None,
) -> models.ResolvedTarget:
    return models.ResolvedTarget(
        request=models.TargetRequest(raw=".", source=".", label=target_label),
        row=models.TargetRow(
            source=".",
            path=str(ROOT),
            git_ref="HEAD",
            git_sha="abc123",
            is_dirty=False,
            label=target_label,
        ),
        binary_sha256=binary_sha256,
        binary_path=binary_path,
    )


def make_endpoint(
    *,
    target_label: str | None = None,
    binary_sha256: str = "sha256:bin",
    treatment: models.Treatment = "off",
) -> models.BenchmarkEndpoint:
    """Construct one resolved endpoint used by pair-report tests."""

    return models.BenchmarkEndpoint(
        make_target(target_label=target_label, binary_sha256=binary_sha256),
        treatment,
    )
