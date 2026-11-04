"""Test controlled native launch policy and local versus invocation failures."""

from __future__ import annotations

import io
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

import pytest
from rich.console import Console

from benchmarking import benchmark, collection, config, figures, native_memory, nightly, processes, profile
from benchmarking.reports.store import ReportStore

from .report_fixtures import make_target
from .test_collection import planned_run


@pytest.mark.parametrize(
    "arguments,expected",
    [
        ([], native_memory.NATIVE_LIMIT_BYTES),
        (["--memory-limit"], native_memory.NATIVE_LIMIT_BYTES),
        (["--no-memory-limit"], None),
        (["--memory-limit-gib", "0.5"], 536870912),
        (["--memory-limit-gib", "1.25"], 1342177280),
        (["--memory-limit-bytes", "12345"], 12345),
    ],
)
def test_comparison_memory_budget_reaches_both_endpoints(arguments: list[str], expected: int | None) -> None:
    args = benchmark.parse_benchmark_args(["example.egg", *arguments])
    assert args.files == ["example.egg"]
    assert {endpoint.memory_limit_bytes for endpoint in benchmark.endpoint_requests(args)} == {expected}


def test_figure_memory_budget_preserves_positional_names() -> None:
    args, _ = figures.parse_args(["--memory-limit-gib", "1.25", "math-runtime"])
    assert args.names == ["math-runtime"]
    assert args.memory_limit_bytes == 1342177280
    assert profile.parse_profile_args(["example.egg", "--memory-limit-gib", "1.25"]).memory_limit_bytes == 1342177280


@pytest.mark.parametrize("value", ["0", "-1", "nan", "inf", "-inf", "1e309", "1e300", "invalid", "1e-12"])
def test_invalid_gib_limits_are_argument_errors(value: str, capsys: pytest.CaptureFixture[str]) -> None:
    with pytest.raises(SystemExit) as error:
        benchmark.parse_benchmark_args([f"--memory-limit-gib={value}"])
    assert error.value.code == 2
    captured = capsys.readouterr()
    assert "--memory-limit-gib" in captured.err and "positive finite" in captured.err
    assert "Traceback" not in captured.err


@pytest.mark.parametrize(
    "arguments",
    [
        ["--memory-limit", "--memory-limit-gib", "2.5"],
        ["--memory-limit", "--memory-limit-bytes", "12345"],
        ["--memory-limit", "--no-memory-limit"],
        ["--memory-limit-gib", "2.5", "--memory-limit-bytes", "12345"],
        ["--memory-limit-gib", "2.5", "--no-memory-limit"],
        ["--memory-limit-bytes", "12345", "--no-memory-limit"],
    ],
)
def test_memory_limit_options_remain_mutually_exclusive(arguments: list[str]) -> None:
    with pytest.raises(SystemExit) as error:
        benchmark.parse_benchmark_args(arguments)
    assert error.value.code == 2


@pytest.mark.parametrize(
    "parse", [benchmark.parse_benchmark_args, figures.parse_args, profile.parse_profile_args, nightly.main]
)
def test_memory_help_uses_gib_and_hides_byte_compatibility_option(
    parse: Callable[[list[str]], object], capsys: pytest.CaptureFixture[str]
) -> None:
    with pytest.raises(SystemExit) as error:
        parse(["--help"])
    assert error.value.code == 0
    help_text = " ".join(capsys.readouterr().out.split())
    assert "--memory-limit-gib GiB" in help_text
    assert "default: 10 GiB" in help_text
    assert "--no-memory-limit" in help_text
    assert "--memory-limit-bytes" not in help_text
    assert str(native_memory.NATIVE_LIMIT_BYTES) not in help_text


def test_native_command_uses_explicit_limit_and_fixed_startup_policy() -> None:
    command, env = native_memory.native_memory_command(["engine", "--help"], {"RUST_LOG": "error"})
    assert command == ["engine", "--memory-limit-bytes=10737418240", "--help"]
    assert env == {"RUST_LOG": "error", **native_memory.NATIVE_ALLOCATOR_ENV}
    assert native_memory.native_memory_command(["engine"], {}, 123)[0] == ["engine", "--memory-limit-bytes=123"]
    assert native_memory.native_memory_command(["engine"], {}, None) == (["engine"], native_memory.NATIVE_ALLOCATOR_ENV)


def test_entrypoints_share_resource_defaults() -> None:
    comparison = benchmark.parse_benchmark_args([])
    figure, _ = figures.parse_args([])
    profiling = profile.parse_profile_args(["example.egg"])
    assert {args.timeout_sec for args in (comparison, figure, profiling)} == {config.DEFAULT_TIMEOUT_SEC}
    assert {args.memory_limit_bytes for args in (comparison, figure, profiling)} == {config.DEFAULT_MEMORY_LIMIT_BYTES}


@pytest.mark.parametrize(
    ("code", "controlled", "stop"), [(86, True, False), (86, False, False), (87, True, True), (87, False, False)]
)
def test_native_exit_protocol_does_not_depend_on_diagnostic_text(
    tmp_path: Path, code: int, controlled: bool, stop: bool
) -> None:
    binary_name = tmp_path / "engine"
    binary_name.write_text(
        f"#!{sys.executable}\nimport sys\nprint('arbitrary diagnostic',file=sys.stderr)\nsys.exit({code})\n"
    )
    binary_name.chmod(0o755)
    result = processes.run_command(
        [str(binary_name)], tmp_path, 5, memory_limit_bytes=native_memory.NATIVE_LIMIT_BYTES if controlled else None
    )
    assert result.status == ("memory-limited" if controlled and code == 86 else "failure")
    assert result.stop_collection is stop
    assert result.error is not None and result.error.exit_code == code
    assert result.error.message == "arbitrary diagnostic"
    assert result.timing.wall_sec is not None and result.timing.max_rss_bytes is not None


@pytest.mark.parametrize("code", [86, 87])
def test_native_outcome_is_retained_before_local_skip_or_invocation_stop(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, code: int
) -> None:
    run = planned_run(required=3)
    other = planned_run(filename="other.egg", required=1)
    plan = collection.CollectionPlan(make_target(binary_path=tmp_path / "engine"), (run, other))
    calls = 0

    def observe(*_args: object) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        return collection.ProcessObservation(
            processes.TimingResult(
                "memory-limited" if code == 86 else "failure",
                processes.TimingRow(),
                processes.ErrorRow(
                    "native failure",
                    exit_code=code,
                ),
                stop_collection=code == 87,
            ),
            None,
        )

    monkeypatch.setattr(collection, "run_process", observe)
    store = ReportStore(tmp_path / "report.jsonl")
    if code == 87:
        with pytest.raises(ValueError, match="failed observation was retained"):
            collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
        assert calls == store.row_count == 1
    else:
        collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
        assert calls == store.row_count == 2
    assert store.records[0]["status"] == ("memory-limited" if code == 86 else "failure")
    assert store.records[0]["memory_limit_bytes"] == native_memory.NATIVE_LIMIT_BYTES


def test_older_binary_rejecting_native_option_fails_preflight(tmp_path: Path) -> None:
    binary_name = tmp_path / "engine"
    binary_name.write_text(
        f"#!{sys.executable}\nimport sys\n"
        "assert sys.argv[1] == '--memory-limit-bytes=10737418240'\n"
        "print('unsupported native option',file=sys.stderr)\nsys.exit(2)\n"
    )
    binary_name.chmod(0o755)
    plan = collection.CollectionPlan(make_target(binary_path=binary_name), (planned_run(required=1),))
    with pytest.raises(ValueError, match="preflight failed.*unsupported native option"):
        collection.preflight_collection(plan, 5)


def test_unexpected_sigkill_is_a_stop_without_an_oom_claim(tmp_path: Path) -> None:
    result = processes.run_command(
        [sys.executable, "-c", "import os,signal; os.kill(os.getpid(), signal.SIGKILL)"], tmp_path, 5
    )
    assert result.stop_collection
    assert result.error is not None and "cause unknown" in result.error.message
    assert "OOM" not in result.error.message


@pytest.mark.parametrize("exit_code", [0, 2, None])
def test_cleanup_failure_retains_attempt_before_stopping(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, exit_code: int | None
) -> None:
    cleanup = processes.terminate_process_group
    calls = 0

    def failed_cleanup(process: subprocess.Popen[str] | subprocess.Popen[bytes]) -> None:
        cleanup(process)
        raise PermissionError("process-group cleanup failed")

    def observe(*_args: object) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        child_code = (
            "import time; time.sleep(60)" if exit_code is None else f"print('complete'); raise SystemExit({exit_code})"
        )
        result = processes.run_command([sys.executable, "-c", child_code], tmp_path, 1)
        return collection.ProcessObservation(result, None)

    monkeypatch.setattr(processes, "terminate_process_group", failed_cleanup)
    monkeypatch.setattr(collection, "run_process", observe)
    plan = collection.CollectionPlan(
        make_target(binary_path=tmp_path / "engine"),
        (planned_run(required=2), planned_run(filename="other.egg", required=1)),
    )
    store = ReportStore(tmp_path / "report.jsonl")
    with pytest.raises(ValueError, match="cleanup failed.*failed observation was retained"):
        collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
    assert calls == store.row_count == 1
    record = store.records[0]
    if exit_code is None:
        assert record["status"] == "failure"
        assert record["wall_sec"] is None and record["max_rss_bytes"] is None
    else:
        assert record["status"] == "failure"
        assert record["wall_sec"] is not None and record["wall_sec"] > 0
        assert record["max_rss_bytes"] is not None and record["max_rss_bytes"] > 0


@pytest.mark.parametrize("stage", ["launch", "wait"])
def test_process_setup_failure_does_not_fabricate_an_observation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, stage: str
) -> None:
    calls = 0

    def failed_wait(*_args: object) -> None:
        raise OSError("wait failed before a process outcome was available")

    def observe(*_args: object) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        command = [str(tmp_path / "missing")] if stage == "launch" else [sys.executable, "-c", "pass"]
        return collection.ProcessObservation(processes.run_command(command, tmp_path, 5), None)

    if stage == "wait":
        monkeypatch.setattr(processes, "wait4_process", failed_wait)
    monkeypatch.setattr(collection, "run_process", observe)
    plan = collection.CollectionPlan(
        make_target(binary_path=tmp_path / "engine"),
        (planned_run(required=2), planned_run(filename="other.egg", required=1)),
    )
    store = ReportStore(tmp_path / "report.jsonl")
    with pytest.raises(OSError):
        collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
    assert calls == 1
    assert store.row_count == 0
