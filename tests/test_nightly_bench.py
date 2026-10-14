"""Nightly collects proofs and slotted data before rendering one shared snapshot."""

from __future__ import annotations

import importlib
from pathlib import Path
from typing import Any

import pytest

from scripts import nightly_bench as nightly


@pytest.mark.parametrize("slotted_status", [0, 1])
def test_nightly_publishes_one_complete_report(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], slotted_status: int
) -> None:
    page, cache = tmp_path / "report.html", tmp_path / "report.jsonl"
    cache.write_text("proof observations\n")
    monkeypatch.setattr(nightly, "PAGE_PATH", page)
    monkeypatch.setattr(nightly, "REPORT_PATH", cache)
    calls = []

    def run(target: nightly.Target, endpoint: nightly.Endpoint, *, open_report: bool, rounds: int | None) -> int:
        calls.append((target, endpoint, open_report, rounds))
        if open_report:
            assert "slotted observations" in cache.read_text()
            page.write_text("one shared report")
        return 0

    def slotted(*, timeout: int, jobs: int) -> int:
        assert (timeout, jobs) == (17, 2)
        with cache.open("a") as handle:
            handle.write("slotted observations\n")
        return slotted_status

    monkeypatch.setattr(nightly, "_run", run)
    monkeypatch.setattr(nightly, "_run_slotted", slotted)
    output = tmp_path / "published"
    assert nightly.main([str(output), "--rounds", "1", "--slotted-timeout", "17", "--slotted-jobs", "2"]) == 0
    assert len(calls) == len(nightly.TARGETS) * len(nightly.ENDPOINTS) + 1
    assert calls[-1] == (nightly.BRANCH, nightly.HEADLINE, True, 1)
    assert (output / "index.html").read_bytes() == page.read_bytes()
    assert (output / "index.jsonl").read_bytes() == cache.read_bytes()
    assert sorted(p.name for p in output.iterdir()) == ["index.html", "index.jsonl"]
    assert ("incomplete or failed" in capsys.readouterr().err) == bool(slotted_status)


def test_failed_collection_preserves_previous_publication(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output = tmp_path / "published"
    output.mkdir()
    (output / "index.html").write_text("previous complete report")
    monkeypatch.setattr(nightly, "_run", lambda *args, **kwargs: 0)

    def fail(**kwargs: Any) -> int:
        raise ValueError("cache incompatible")

    monkeypatch.setattr(nightly, "_run_slotted", fail)
    assert nightly.main([str(output)]) == 1
    assert (output / "index.html").read_text() == "previous complete report"


def test_slotted_nightly_uses_shared_cache_and_paper_budgets(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    evaluator = importlib.import_module("slotted.slotted-eval")
    builds, calls = [], []
    monkeypatch.setattr(evaluator, "build", lambda **kwargs: builds.append(kwargs))

    def collect(argv: list[str]) -> int:
        calls.append(argv)
        return 1

    monkeypatch.setattr(evaluator, "main", collect)
    report = tmp_path / "all.jsonl"
    assert evaluator.nightly(report, env={"PATH": "test-cargo"}, jobs=2, timeout=17) == 1
    assert builds == [{"env": {"PATH": "test-cargo"}}]
    argv = calls[0]
    assert argv[argv.index("--report") + 1] == str(report)
    assert argv[argv.index("--params") + 1 : argv.index("--report")] == ["0", "1", "2", "3"]
    assert "--rounds" not in argv  # Proof sample counts never change rewrite budgets.
    assert "--html" not in argv
