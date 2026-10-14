"""Nightly composition preserves proof reports and slotted correctness failures."""

from __future__ import annotations

import importlib
from pathlib import Path
from typing import Any

import pytest

from scripts import nightly_bench as nightly


@pytest.mark.parametrize("slotted_status", [0, 1])
def test_nightly_publishes_both_reports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], slotted_status: int
) -> None:
    page = tmp_path / "proofs.html"
    script = '<script>const fragment = "</body>";</script>'
    page.write_text(f'<html><body><main id="eval-live-root">proof provenance</main>{script}</body></html>')
    cache = tmp_path / "proofs.jsonl"
    cache.write_text('{"proof observations":"unchanged"}\n')
    monkeypatch.setattr(nightly, "PAGE_PATH", page)
    monkeypatch.setattr(nightly, "REPORT_PATH", cache)
    calls = []

    def run(target: nightly.Target, endpoint: nightly.Endpoint, *, open_report: bool, rounds: int | None) -> int:
        calls.append((target, endpoint, open_report, rounds))
        return 0

    def slotted(directory: Path, *, timeout: int, jobs: int) -> int:
        assert (timeout, jobs) == (17, 2)
        (directory / "slotted.html").write_text("<h2>Multipattern matching</h2><p>comparison error banner</p>")
        (directory / "slotted.md").write_text("| egglog | ref-multi |\n")
        (directory / "slotted.jsonl").write_text('{"slotted observations":"new"}\n')
        return slotted_status

    monkeypatch.setattr(nightly, "_run", run)
    monkeypatch.setattr(nightly, "_run_slotted", slotted)
    output = tmp_path / "published"
    assert nightly.main([str(output), "--rounds", "1", "--slotted-timeout", "17", "--slotted-jobs", "2"]) == 0
    assert len(calls) == len(nightly.TARGETS) * len(nightly.ENDPOINTS) + 1
    assert calls[-1] == (nightly.BRANCH, nightly.HEADLINE, True, 1)
    index = (output / "index.html").read_text()
    assert 'id="eval-live-root">proof provenance' in index
    assert script in index
    assert index.index('id="slotted-report"') > index.index("</script>")
    assert 'src="slotted.html"' in index
    assert (output / "index.jsonl").read_bytes() == cache.read_bytes()
    assert "comparison error banner" in (output / "slotted.html").read_text()
    assert ("incomplete or failed" in capsys.readouterr().err) == bool(slotted_status)


def test_failed_slotted_collection_preserves_previous_publication(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    page = tmp_path / "new.html"
    page.write_text("<html><body>new proof report</body></html>")
    output = tmp_path / "published"
    output.mkdir()
    (output / "index.html").write_text("previous complete report")
    monkeypatch.setattr(nightly, "PAGE_PATH", page)
    monkeypatch.setattr(nightly, "_run", lambda *args, **kwargs: 0)
    monkeypatch.setattr(nightly, "_run_slotted", lambda *args, **kwargs: 1)
    assert nightly.main([str(output)]) == 1
    assert (output / "index.html").read_text() == "previous complete report"


def test_slotted_nightly_uses_public_collector_and_paper_budgets(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    evaluator = importlib.import_module("slotted.slotted-eval")
    builds = []
    monkeypatch.setattr(evaluator, "build", lambda **kwargs: builds.append(kwargs))

    def collect(args: Any, sides: Any, parser: Any, **kwargs: Any) -> list[Any]:
        assert args.no_build and args.counts
        assert args.params == [0, 1, 2, 3]
        assert args.rounds is None  # Proof sampling rounds never change rewrite budgets.
        assert args.jobs == 2 and args.timeout == 17
        assert sides == evaluator.SIDES
        return []  # Explicit failure must still produce a reviewable report.

    monkeypatch.setattr(evaluator, "collect", collect)
    assert evaluator.nightly(tmp_path, env={"PATH": "test-cargo"}, jobs=2, timeout=17) == 1
    assert builds == [{"env": {"PATH": "test-cargo"}}]
    assert "No benchmark results" in (tmp_path / "slotted.html").read_text()
    assert "No benchmark results" in (tmp_path / "slotted.md").read_text()
    assert (tmp_path / "slotted.jsonl").is_file()
