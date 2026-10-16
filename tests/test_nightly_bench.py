"""Nightly chooses CLI arguments and publishes the resulting shared cache."""

from __future__ import annotations

import subprocess
from collections.abc import Sequence
from pathlib import Path
from typing import Any

import pytest

from scripts import nightly_bench as nightly


@pytest.mark.parametrize("slotted_status", [0, 1, 2])
@pytest.mark.parametrize("explicit_options", [False, True])
def test_nightly_uses_only_the_public_cli(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    slotted_status: int,
    explicit_options: bool,
) -> None:
    output = tmp_path / "published"
    output.mkdir()
    page, cache = output / "index.html", output / "index.jsonl"
    page.write_text("previous report")
    cache.write_text("previous observations")
    calls = []

    def run(command: Sequence[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        assert command[:2] == [nightly.sys.executable, str(nightly.BENCH_SCRIPT)]
        assert kwargs["cwd"] == nightly.REPO_ROOT
        assert kwargs["env"]["PATH"].split(nightly.os.pathsep)[0] == str(nightly.CARGO_BIN_DIR)
        assert kwargs["env"]["BROWSER"] == "true"
        args = list(command[2:])
        assert args[args.index("--report") + 1] == str(cache)
        calls.append(args)
        if len(calls) == 1:
            assert not page.exists() and not cache.exists()
        if args[0] == "slotted":
            timeout, jobs = ("17", "2") if explicit_options else ("150", "1")
            assert args == [
                "slotted",
                "--timeout",
                timeout,
                "--jobs",
                jobs,
                "--params",
                "0",
                "1",
                "2",
                "3",
                "--report",
                str(cache),
            ]
            assert "proof observations" in cache.read_text()
            if slotted_status != 2:
                with cache.open("a") as handle:
                    handle.write("slotted observations\n")
            return subprocess.CompletedProcess(command, slotted_status)
        assert args[args.index("--rounds") + 1] == "1"
        if "--open" in args:
            assert "slotted observations" in cache.read_text()
            page.write_text("one shared report")
        else:
            with cache.open("a") as handle:
                handle.write("proof observations\n")
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(nightly.subprocess, "run", run)
    extra = ["--slotted-timeout", "17", "--slotted-jobs", "2"] if explicit_options else []
    assert nightly.main([str(output), "--rounds", "1", *extra]) == (1 if slotted_status == 2 else 0)
    expected = len(nightly.TARGETS) * len(nightly.TREATMENTS) + (1 if slotted_status == 2 else 2)
    assert len(calls) == expected
    if slotted_status == 2:
        assert not page.exists()
    else:
        assert "--open" in calls[-1]
        assert page.read_text() == "one shared report"
        assert sorted(p.name for p in output.iterdir()) == ["index.html", "index.jsonl"]
    assert ("incomplete or failed" in capsys.readouterr().err) == (slotted_status == 1)
