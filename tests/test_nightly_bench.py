"""Test that the nightly measures into the directory it publishes, starting clean."""

from __future__ import annotations

import importlib.util
import subprocess
from collections.abc import Sequence
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parents[1]


def load_nightly() -> Any:
    """Import the nightly script, which sits outside the importable packages."""

    spec = importlib.util.spec_from_file_location("nightly_bench", ROOT / "scripts" / "nightly_bench.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


nightly = load_nightly()


def fake_bench(calls: list[tuple[Path, str]], *, returncode: int = 0) -> Any:
    """Stand in for bench.py: record the cache it was handed, then append one row."""

    def run(command: Sequence[str], **_kwargs: object) -> subprocess.CompletedProcess[bytes]:
        report = Path(command[list(command).index("--report") + 1])
        calls.append((report, report.read_text(encoding="utf-8") if report.exists() else ""))
        if returncode == 0:
            with report.open("a") as handle:
                handle.write("{}\n")
            if "--open" in command:
                report.with_suffix(".html").write_text("page", encoding="utf-8")
        return subprocess.CompletedProcess(list(command), returncode)

    return run


def test_every_run_measures_into_the_published_cache(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "nightly" / "output"
    calls: list[tuple[Path, str]] = []
    monkeypatch.setattr(nightly.subprocess, "run", fake_bench(calls))

    assert nightly.main([str(output_dir)]) == 0

    endpoints = len(nightly.TARGETS) * len(nightly.TREATMENTS) + 1  # plus the render run
    assert len(calls) == endpoints
    assert {report for report, _ in calls} == {output_dir / "index.jsonl"}
    assert (output_dir / "index.jsonl").read_text(encoding="utf-8") == "{}\n" * endpoints
    assert (output_dir / "index.html").is_file()


def test_an_earlier_runs_rows_never_reach_bench(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "nightly" / "output"
    output_dir.mkdir(parents=True)
    # What an earlier run left behind, written under another report schema
    # version; ReportStore rejects such an artifact instead of migrating it.
    (output_dir / "index.jsonl").write_text('{"report_schema_version": 1}\n', encoding="utf-8")
    (output_dir / "index.html").write_text("stale page", encoding="utf-8")
    (output_dir / "notes.txt").write_text("not ours", encoding="utf-8")
    calls: list[tuple[Path, str]] = []
    monkeypatch.setattr(nightly.subprocess, "run", fake_bench(calls))

    assert nightly.main([str(output_dir)]) == 0

    assert calls[0][1] == "", "the first invocation must be handed an empty cache"
    assert "report_schema_version" not in (output_dir / "index.jsonl").read_text(encoding="utf-8")
    assert (output_dir / "index.html").read_text(encoding="utf-8") == "page"
    assert (output_dir / "notes.txt").read_text(encoding="utf-8") == "not ours", "cleared more than it publishes"


def test_a_failed_run_publishes_no_page(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "nightly" / "output"
    monkeypatch.setattr(nightly.subprocess, "run", fake_bench([]))
    assert nightly.main([str(output_dir)]) == 0

    monkeypatch.setattr(nightly.subprocess, "run", fake_bench([], returncode=1))
    assert nightly.main([str(output_dir)]) == 1

    # A stale page left standing is what made a nightly that ran nothing look healthy.
    assert not (output_dir / "index.html").exists()
