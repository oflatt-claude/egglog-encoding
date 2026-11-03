"""Test JSONL persistence, indexing, cache selection, and schema failures."""

from __future__ import annotations

import json
from pathlib import Path
from typing import cast

import pytest

from benchmarking.models import Status
from benchmarking.reports.store import (
    CacheKey,
    ReportRecord,
    ReportStore,
    RulesetTimingRecord,
    TimingSummaryRecord,
    parse_report_record,
)

from .report_fixtures import make_record, make_ruleset_timing, make_timing_summary, write_report


@pytest.mark.parametrize(
    ("status", "wall", "old_timeout", "timeout", "expected"),
    [
        ("success", 121.0, 120, 120, True),
        ("success", None, 120, 300, True),
        ("success", 50.0, 300, 120, True),
        ("success", 121.0, 300, 120, False),
        ("success", None, 300, 120, False),
        ("timed-out", None, 120, 120, True),
        ("timed-out", None, 120, 300, False),
        ("failure", 50.0, 120, 300, True),
    ],
)
def test_timeout_selection_preserves_success_and_failure_provenance(
    tmp_path: Path, status: Status, wall: float | None, old_timeout: int, timeout: int, expected: bool
) -> None:
    record = make_record(0, started_at="2026-10-27T00:00:00Z", status=status, wall_sec=wall, timeout_sec=old_timeout)
    path = tmp_path / "report.jsonl"
    write_report(path, record)
    before = path.read_bytes()
    store = ReportStore(path)
    key = CacheKey("sha256:bin", "sha256:file", "off")
    selected = store.latest_records(key, 1, timeout)
    assert bool(selected) is expected
    assert [r.row_index for r in store.grouped_report().latest_records(key, 1, timeout)] == [
        r.row_index for r in selected
    ]
    assert path.read_bytes() == before


@pytest.mark.parametrize("status", ["success", "failure", "timed-out"])
def test_allocator_profiles_never_share_observations(tmp_path: Path, status: Status) -> None:
    path = tmp_path / "report.jsonl"
    for i, cap in enumerate((None, 8 * 1024**3, 10 * 1024**3)):
        record = make_record(i, started_at=f"2026-10-27T00:00:0{i}Z", status=status, memory_limit_bytes=cap)
        if status == "failure":
            record["error_exit_code"] = 86
        ReportStore(path).append(record)
    store = ReportStore(path)
    for i, cap in enumerate((None, 8 * 1024**3, 10 * 1024**3)):
        key = CacheKey("sha256:bin", "sha256:file", "off", memory_limit_bytes=cap)
        assert [row.row_index for row in store.latest_records(key, 3, 120)] == [i]
        assert [r.row_index for r in store.grouped_report().latest_records(key, 3, 120)] == [i]


@pytest.mark.parametrize("setting", ["flags", "environment"])
def test_changed_execution_settings_invalidate_old_observations(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, setting: str
) -> None:
    from benchmarking.engines import PROCESS_ENV, TREATMENT_SPECS, TreatmentSpec

    path = tmp_path / "report.jsonl"
    write_report(path, make_record(0, started_at="2026-10-27T00:00:00Z"))
    if setting == "flags":
        monkeypatch.setitem(TREATMENT_SPECS, "off", TreatmentSpec("egglog", ("--changed-flag",)))
    else:
        monkeypatch.setitem(PROCESS_ENV, "RUST_LOG", "info")
    key = CacheKey("sha256:bin", "sha256:file", "off")
    assert not ReportStore(path).latest_records(key, 1, 120)


def test_raised_timeout_does_not_retry_control_failure(tmp_path: Path) -> None:
    record = make_record(0, started_at="2026-10-27T00:00:00Z", status="timed-out")
    record["error_message"] = "timed out; process-group cleanup failed: denied"
    store = ReportStore(tmp_path / "report.jsonl")
    store.append(record)
    assert len(store.latest_records(CacheKey("sha256:bin", "sha256:file", "off"), 1, 300)) == 1


def test_missing_report_is_an_empty_store_without_creating_files(tmp_path: Path) -> None:
    report = tmp_path / "nested" / "report.jsonl"

    ReportStore(report)

    assert not report.parent.exists()


def test_append_is_immediately_queryable(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(0, started_at="2026-07-15T12:00:00Z", target_label="current")
    store = ReportStore(report)

    store.append(record)
    pointer = store.find_label_pointer("current")

    assert pointer is not None
    assert pointer.binary_sha256 == record["binary_sha256"]
    raw = json.loads(report.read_text(encoding="utf-8"))
    assert raw == record
    assert "row_index" not in raw


def test_label_pointers_select_the_latest_binary_for_each_engine(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            target_label="current",
            binary_sha256="sha256:egglog",
            treatment="off",
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            target_label="current",
            binary_sha256="sha256:egg",
            treatment="egg",
        ),
    )
    store = ReportStore(report)
    egglog = store.find_label_pointer("current", "egglog")
    egg = store.find_label_pointer("current", "egg")
    latest = store.find_label_pointer("current")

    assert egglog is not None and egglog.binary_sha256 == "sha256:egglog"
    assert egg is not None and egg.binary_sha256 == "sha256:egg"
    assert latest is not None and latest.binary_sha256 == "sha256:egg"


def test_append_indexes_the_exact_record_it_persists(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(0, started_at="2026-07-15T12:00:00Z", wall_sec=2.5)
    key = CacheKey("sha256:bin", "sha256:file", "off")
    store = ReportStore(report)

    store.append(record)
    persisted = parse_report_record(report.read_bytes())
    current = store.latest_records(key, 1, 120)[0].record
    reopened = ReportStore(report)

    assert current == persisted == reopened.latest_records(key, 1, 120)[0].record
    assert store.records == reopened.records == (persisted,)
    assert current["wall_sec"] == 2.5


def test_report_path_metacharacters_are_literal_not_a_glob(tmp_path: Path) -> None:
    report = tmp_path / "a'quoted[?*].jsonl"
    sibling = tmp_path / "a?.jsonl"
    write_report(report, make_record(0, started_at="2026-07-15T12:00:00Z"))
    write_report(
        sibling,
        make_record(1, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:sibling"),
    )

    records = ReportStore(report).records

    assert [record["binary_sha256"] for record in records] == ["sha256:bin"]


def test_typed_dict_schema_and_nested_values_round_trip(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(
        0,
        started_at="2026-07-15T12:00:00Z",
        max_rss_bytes=1234,
        timing_summary=make_timing_summary(
            make_ruleset_timing(
                "rules/λ",
                search_ns=6,
                apply_ns=5,
                execution_ns=4,
                merge_ns=7,
            ),
            native_rebuild_ns=3,
        ),
    )

    ReportStore(report).append(record)
    loaded = parse_report_record(report.read_bytes())

    assert loaded == record
    assert set(loaded) == set(ReportRecord.__annotations__)
    summary = cast(TimingSummaryRecord, loaded["timing_summary"])
    assert tuple(summary) == tuple(TimingSummaryRecord.__annotations__)
    rulesets = cast(list[RulesetTimingRecord], summary["rulesets"])
    assert all(tuple(ruleset) == tuple(RulesetTimingRecord.__annotations__) for ruleset in rulesets)
    assert rulesets == [
        {
            "name": "rules/λ",
            "role": "program",
            "assembly_ns": 0,
            "search_ns": 6,
            "apply_ns": 5,
            "execution_ns": 4,
            "merge_ns": 7,
        }
    ]
    assert summary["native_rebuild_ns"] == 3


@pytest.mark.parametrize("schema_version", [None, 2], ids=["missing", "wrong"])
def test_incompatible_report_schema_fails_during_load(tmp_path: Path, schema_version: int | None) -> None:
    report = tmp_path / "report.jsonl"
    current = make_record(0, started_at="2026-07-15T12:00:00Z")
    old = cast(dict[str, object], make_record(1, started_at="2026-07-15T12:00:01Z"))
    if schema_version is None:
        del old["report_schema_version"]
    else:
        old["report_schema_version"] = schema_version
    report.write_text(f"{json.dumps(current)}\n{json.dumps(old)}\n", encoding="utf-8")

    with pytest.raises(ValueError, match=r"invalid or incompatible benchmark report.*recompute"):
        ReportStore(report)


@pytest.mark.parametrize("mixed", [False, True], ids=["old", "mixed"])
def test_incompatible_report_shapes_fail_during_load(tmp_path: Path, mixed: bool) -> None:
    report = tmp_path / "report.jsonl"
    current = make_record(0, started_at="2026-07-15T12:00:00Z")
    old = cast(dict[str, object], make_record(1, started_at="2026-07-15T12:00:01Z"))
    timing = cast(dict[str, object], old["timing_summary"])
    timing["schema_version"] = 2
    records = (current, old) if mixed else (old,)
    report.write_text("".join(f"{json.dumps(record)}\n" for record in records), encoding="utf-8")

    with pytest.raises(ValueError, match=r"invalid or incompatible benchmark report.*recompute"):
        ReportStore(report)


def test_success_without_timing_summary_is_an_incompatible_report(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    row = make_record(0, started_at="2026-07-15T12:00:00Z")
    row["timing_summary"] = None
    report.write_text(f"{json.dumps(row)}\n", encoding="utf-8")

    with pytest.raises(ValueError, match=r"invalid or incompatible benchmark report.*recompute"):
        ReportStore(report)


def test_bulk_status_selection_uses_all_cache_dimensions_and_jsonl_tie_order(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", status="failure"),
        make_record(1, started_at="2026-07-15T12:00:01Z", status="timed-out"),
        make_record(2, started_at="2026-07-15T12:00:01Z"),
        make_record(
            3,
            started_at="2026-07-15T12:00:02Z",
            fact_directory_sha256="sha256:other-facts",
        ),
    )
    exact = CacheKey("sha256:bin", "sha256:file", "off")
    other_facts = CacheKey(
        "sha256:bin",
        "sha256:file",
        "off",
        fact_directory_sha256="sha256:other-facts",
    )

    selected = ReportStore(report).selected_statuses_for_keys((exact, other_facts), 2, 120)

    assert selected[exact] == ("timed-out", "success")
    assert selected[other_facts] == ("success",)
