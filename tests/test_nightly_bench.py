"""Test that the nightly publishes the cache it measured into, starting empty."""

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


def fake_bench(reports: list[Path], *, returncode: int = 0) -> Any:
    """Stand in for bench.py: record the cache it was given and append one row."""

    def run(command: Sequence[str], **_kwargs: object) -> subprocess.CompletedProcess[bytes]:
        report = Path(command[list(command).index("--report") + 1])
        reports.append(report)
        if returncode == 0:
            with report.open("a") as handle:
                handle.write("{}\n")
            if "--open" in command:
                report.with_suffix(".html").write_text("page", encoding="utf-8")
        return subprocess.CompletedProcess(list(command), returncode)

    return run


def test_every_run_measures_into_the_published_cache(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "nightly" / "output"
    reports: list[Path] = []
    monkeypatch.setattr(nightly.subprocess, "run", fake_bench(reports))

    assert nightly.main([str(output_dir)]) == 0

    endpoints = len(nightly.TARGETS) * len(nightly.TREATMENTS) + 1  # plus the render run
    assert len(reports) == endpoints
    assert set(reports) == {output_dir.with_name("output.next") / "index.jsonl"}
    assert (output_dir / "index.jsonl").read_text(encoding="utf-8") == "{}\n" * endpoints
    assert (output_dir / "index.html").is_file()
    assert not output_dir.with_name("output.next").exists()


def test_a_published_cache_is_never_read_back_by_the_next_run(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    output_dir = tmp_path / "nightly" / "output"
    output_dir.mkdir(parents=True)
    # Rows an earlier run wrote under another report schema version; ReportStore
    # rejects the whole artifact rather than migrating it.
    (output_dir / "index.jsonl").write_text('{"report_schema_version": 1}\n', encoding="utf-8")
    reports: list[Path] = []
    monkeypatch.setattr(nightly.subprocess, "run", fake_bench(reports))

    assert nightly.main([str(output_dir)]) == 0

    assert all(not report.exists() or "schema_version" not in report.read_text(encoding="utf-8") for report in reports)
    assert "schema_version" not in (output_dir / "index.jsonl").read_text(encoding="utf-8")


def test_a_failed_run_leaves_the_previous_publish_in_place(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    output_dir = tmp_path / "nightly" / "output"
    monkeypatch.setattr(nightly.subprocess, "run", fake_bench([]))
    assert nightly.main([str(output_dir)]) == 0
    published = (output_dir / "index.jsonl").read_text(encoding="utf-8")

    monkeypatch.setattr(nightly.subprocess, "run", fake_bench([], returncode=1))
    assert nightly.main([str(output_dir)]) == 1

    assert (output_dir / "index.jsonl").read_text(encoding="utf-8") == published
    assert (output_dir / "index.html").is_file()
