"""Mixed proof/slotted caches preserve endpoint identities and exact certificates."""

from __future__ import annotations

import argparse
import base64
import copy
import importlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from benchmarking import models
from benchmarking.reports.catalog import ReportTable
from benchmarking.reports.interactive import write_interactive_report
from benchmarking.reports.interactive_runtime import InteractiveRuntime, scope_for_comparison
from benchmarking.reports.slotted import ERROR_TITLE, EXACT_PAIRS, SIDES, select_slotted_records, slotted_report
from benchmarking.reports.store import ReportStore, serialize_grouped_report

from .report_fixtures import make_endpoint, make_record, make_timing_summary

ROOT = Path(__file__).resolve().parents[1]


def _case(tmp_path: Path) -> tuple[Any, Any, Any, tuple[str, int], list[Any]]:
    evaluator = importlib.import_module("slotted.slotted-eval")
    cache_module = importlib.import_module("eval_cache")
    report_module = importlib.import_module("eval_observation")
    egglog, reference = tmp_path / "egglog", tmp_path / "reference"
    egglog.write_bytes(b"encoding binary")
    reference.write_bytes(b"reference binary")
    config = evaluator.Config(egglog, reference, group_cap=10)
    args = argparse.Namespace(counts=True, timeout=30, jobs=1, force_run=False)
    task = ("array", 0)
    cache = cache_module.Cache(tmp_path / "all.jsonl", ROOT, config, args, {task: "generated source"})
    rows = [evaluator.Row("array", "goal-2d-4f-N0", side, 6) for side in evaluator.SIDES]
    for row in rows:
        row.goal, row.classes, row.nodes, row.seconds = "yes", 2, 3, 0.125
    by_side = {row.side: row for row in rows}
    for encoding, ref in EXACT_PAIRS.items():
        enc, oracle = by_side[encoding], by_side[ref]
        enc.vs_ref[ref] = report_module.Comparison(enc.observation, oracle.observation, "isomorphic")
    return cache, config, args, task, rows


def test_shared_cache_reuses_only_exact_inputs_and_compared_observations(tmp_path: Path) -> None:
    cache, config, args, task, rows = _case(tmp_path)
    module = importlib.import_module("eval_cache")
    sides = tuple(row.side for row in rows)
    proof = make_record(0, started_at="2026-01-01T00:00:00Z")
    cache.store.append(proof)
    assert cache.reuse(task, sides) is None
    cache.append(task, rows)
    reused = cache.reuse(task, sides)
    assert [record["slotted"]["observation"] for record in reused] == [row.observation for row in rows]
    assert all(record["wall_sec"] == 0.125 for record in reused)
    assert cache.store.records[0] == proof
    assert cache.store.row_count == 6  # Reuse does not append duplicate observations.

    def reload(program: str = "generated source") -> Any:
        return module.Cache(cache.store.path, ROOT, config, args, {task: program})

    assert reload("changed source").reuse(task, sides) is None
    args.timeout = 31
    assert reload().reuse(task, sides) is None
    args.timeout = 30
    args.jobs = 2
    assert reload().reuse(task, sides) is None
    args.jobs = 1
    args.counts = False
    assert reload().reuse(task, sides) is None
    args.counts = True
    args.force_run = True
    assert reload().reuse(task, sides) is None
    args.force_run = False
    config.xmulti.write_bytes(b"new reference binary")
    assert reload().reuse(task, sides) is None

    # Even equal sizes do not certify a new reference observation against old
    # encoding data. The collector must recollect this partial group together.
    rows[2].observation = "new-reference-observation"
    cache.append(task, [rows[2]])
    assert cache.reuse(task, sides) is None
    loaded = select_slotted_records(cache.store.records)
    assert len(loaded) == 5
    assert "selected observations have not been compared" in str(slotted_report(loaded).errors)


def test_single_page_embeds_shared_data_and_slotted_tables_without_iframe(tmp_path: Path) -> None:
    cache, _config, _args, task, rows = _case(tmp_path)
    proof_off = make_record(0, started_at="2026-01-01T00:00:00Z", treatment="off")
    proof_on = make_record(1, started_at="2026-01-01T00:00:01Z", treatment="proofs")
    cache.store.append(proof_off)
    cache.store.append(proof_on)
    cache.append(task, rows)
    store = ReportStore(cache.store.path)
    grouped = store.grouped_report()
    cache_bytes = store.path.read_bytes()
    comparison = models.ComparisonSpec(
        make_endpoint(treatment="off"),
        make_endpoint(treatment="proofs"),
        (models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file"),),
        1,
        120,
    )
    runtime = InteractiveRuntime(grouped, scope_for_comparison(comparison))
    payload = json.dumps(runtime.initial_payload(comparison))
    assert "Multipattern matching" in payload and "Nested matching" in payload
    assert "SLOTTED CORRECTNESS" not in payload
    assert "slotted-reference" in payload
    assert "Slotted e-graph sizes" in json.dumps(runtime.apply(scope_for_comparison(comparison)))
    path = write_interactive_report(grouped, comparison, tmp_path / "page.html")
    page = path.read_text()
    assert '<iframe src="slotted.html"' not in page
    match = re.search(r'<script id="report-envelope"[^>]*>(.*?)</script>', page)
    assert match
    envelope = json.loads(base64.b64decode(match[1]))
    assert base64.b64decode(envelope["report_grouped_base64"]) == serialize_grouped_report(grouped)
    assert envelope["initial_payload"]["sections"][-1]["id"] == "slotted"

    # Cached reference endpoints use their own engine identity when retargeted.
    selectors = json.loads(json.dumps(runtime.payload()))["selectors"]
    endpoints = {choice["treatment"]: choice["id"] for choice in selectors["endpoints"]}
    slotted_file = next(choice["id"] for choice in selectors["files"] if "goal-2d-4f-N0" in choice["label"])
    for encoding, reference in (("slotted", "multi"), ("slotted-no-aliasing", "nested-snapshot")):
        retargeted = runtime.apply(
            {
                "baseline_endpoint_id": endpoints[reference],
                "candidate_endpoint_id": endpoints[encoding],
                "file_ids": [slotted_file],
                "timeout_sec": 30,
                "rounds": 1,
            }
        )
        assert "Slotted e-graph sizes" in json.dumps(retargeted)
    assert store.path.read_bytes() == cache_bytes

    # A bogus positive certificate must not conceal wrong raw counts.
    rows[0].nodes += 1
    cache.append(task, [rows[0]])
    catalog = slotted_report(cache.store.records).catalog
    assert "different: nodes" in str(catalog)
    assert "SLOTTED CORRECTNESS CHECKS FAILED OR INCOMPLETE" in str(catalog)


def test_timeout_cells_show_the_outcome_in_cli_and_nightly(tmp_path: Path) -> None:
    cache, _config, _args, task, rows = _case(tmp_path)
    encoding = rows[0]
    encoding.goal, encoding.seconds = "timeout", 300.125
    cache.append(task, rows)

    catalog = slotted_report(cache.store.records).catalog
    table = catalog.sections[0].blocks[0]
    assert isinstance(table, ReportTable)
    assert table.rows[0].cells[1].display == "timeout"
    # Keep elapsed time in the cache and cell data, but don't print it as a result.
    assert cache.store.records[0]["wall_sec"] == 300.125
    assert table.rows[0].cells[1].raw == 300.125


@pytest.mark.parametrize("encoding,reference", EXACT_PAIRS.items())
@pytest.mark.parametrize("phase", ["timed run", "graph dump"])
def test_reference_timeouts_leave_comparisons_unverified_without_error_banners(
    tmp_path: Path, capsys: pytest.CaptureFixture[str], encoding: str, reference: str, phase: str
) -> None:
    cache, _, _, task, rows = _case(tmp_path)
    enc, ref = (next(row for row in rows if row.side == side) for side in (encoding, reference))
    ref.goal = "timeout" if phase == "timed run" else "yes"
    ref.classes = ref.nodes = None
    ref.graph_issue = f"reference {phase} exceeded timeout"
    observation = importlib.import_module("eval_observation")
    enc.vs_ref[reference] = observation.Comparison(enc.observation, ref.observation, "inconclusive: counts unavailable")
    records = cache.append(task, rows)
    report = slotted_report(records)
    assert not report.errors
    assert "not compared: reference timeout" in str(report.catalog)
    assert ERROR_TITLE not in str(report.catalog)
    evaluator = importlib.import_module("slotted.slotted-eval")
    assert evaluator.main(["--from", str(cache.store.path)]) == 0
    assert ERROR_TITLE not in capsys.readouterr().out

    # A reference timeout cannot excuse an encoding failure or a known mismatch.
    encoding_evidence = next(r["slotted"] for r in records if r["slotted"]["side"] == encoding)
    reference_evidence = next(r["slotted"] for r in records if r["slotted"]["side"] == reference)
    encoding_evidence["graph_issue"] = "encoding graph unreadable"
    assert slotted_report(records).errors
    encoding_evidence["graph_issue"] = None
    encoding_evidence["nodes"] = None
    assert slotted_report(records).errors
    encoding_evidence["nodes"] = enc.nodes
    reference_evidence["classes"] = enc.classes
    reference_evidence["nodes"] = enc.nodes + 1
    assert "different: nodes" in str(slotted_report(records).errors)
    reference_evidence["nodes"] = enc.nodes
    encoding_evidence["vs_ref"][reference]["verdict"] = "different: symmetry groups"
    assert "different: symmetry groups" in str(slotted_report(records).errors)


def test_unsupported_treatments_are_distinct_from_missing_comparisons(tmp_path: Path) -> None:
    cache, _, _, task, rows = _case(tmp_path)
    active = [row for row in rows if row.side in ("encoding", "ref-multi")]
    for row in active:
        row.study, row.case = "logic", "first-order-logic"
        row.unsupported = dict.fromkeys(
            ("encoding-no-aliasing", "ref-nested", "ref-nested-snapshot"), "multipattern side conditions"
        )
    records = cache.append(task, active)
    assert cache.reuse(task, tuple(row.side for row in active)) == records
    report = slotted_report(records)
    assert not report.errors
    nested = report.catalog.sections[0].blocks[1]
    assert isinstance(nested, ReportTable)
    assert [cell.display for cell in nested.rows[0].cells] == ["first-order-logic", "unsupported", "unsupported"]
    assert all(cell.raw is None for cell in nested.rows[0].cells[1:])
    assert "multipattern side conditions" in str(report.catalog)

    # Explicitly unsupported treatments cannot excuse a missing supported pair,
    # or waive its independent count and isomorphism obligations.
    assert "missing ref-multi" in str(slotted_report(records[:1]).errors)
    records[0]["slotted"]["nodes"] += 1
    assert "different: nodes" in str(slotted_report(records).errors)
    records[0]["slotted"]["nodes"] -= 1
    records[0]["slotted"]["vs_ref"].clear()
    assert "not been compared" in str(slotted_report(records).errors)
    assert cache.reuse(task, tuple(row.side for row in active)) is None


def test_collector_never_runs_unsupported_treatments(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _, config, args, _, _ = _case(tmp_path)
    evaluator = importlib.import_module("slotted.slotted-eval")
    workloads = importlib.import_module("eval_workloads")
    verification = importlib.import_module("eval_verify")
    workload = workloads.prepare(("logic", "first-order-logic"))
    ran, graphed = [], []

    def encoding(_program: str, _name: str, row: Any, *_args: Any, **_kwargs: Any) -> None:
        ran.append(row.side)
        row.goal, row.seconds = "yes", 0.01

    def reference(_spec: str, row: Any, *_args: Any, **_kwargs: Any) -> None:
        ran.append(row.side)
        row.goal, row.seconds = "yes", 0.01

    def graph(_workload: Any, row: Any, *_args: Any, **_kwargs: Any) -> None:
        graphed.append(row.side)

    monkeypatch.setattr(evaluator, "run_egglog", encoding)
    monkeypatch.setattr(evaluator, "run_reference", reference)
    monkeypatch.setattr(verification, "collect_graph", graph)
    monkeypatch.setattr(verification, "compare", lambda *_args: None)
    rows = evaluator.collect_workload(workload, args, SIDES, config, lambda *_args: None)
    assert ran == graphed == ["encoding", "ref-multi"]
    assert all(row.unsupported == workload.unsupported for row in rows)


def test_logic_inputs_keep_the_fixture_budget_and_survive_source_changes(tmp_path: Path) -> None:
    importlib.import_module("slotted.slotted-eval")
    workloads = importlib.import_module("eval_workloads")
    path = tmp_path / "logic.egg"
    original = (ROOT / "slotted/tests/rudi/first-order-logic2.egg").read_text()
    path.write_text(original)
    workload = workloads.logic_workload(path)
    assert workload.rounds == 5
    assert "(run 5)" in workload.program and workload.multi.startswith("rounds 5\n")
    zero = workloads.logic_workload(path, rounds=0)
    assert "(run 0)" in zero.program and zero.multi.startswith("rounds 0\n")
    assert "(check" not in zero.graph_program
    assert zero.unsupported == workload.unsupported
    path.unlink()
    assert workload.lang.default_sort == "L" and "Forall" in workload.lang.ops
    with pytest.raises(ValueError, match="single nested pattern"):
        workload.reference("ref-nested")


def test_reference_treatments_cannot_silently_run_proofs() -> None:
    from benchmarking.engines import TREATMENTS
    from benchmarking.targets import workload_command

    fixture = models.FileSpec("example.egg", Path("/example.egg"), "sha256:example")
    assert "--slotted" in workload_command(Path("egglog"), fixture, "slotted")
    assert "--slotted-no-aliasing" in workload_command(Path("egglog"), fixture, "slotted-no-aliasing")
    for treatment in ("multi", "nested", "nested-snapshot"):
        assert treatment not in TREATMENTS
        with pytest.raises(ValueError, match="reference matcher"):
            workload_command(Path("xmulti"), fixture, treatment)


@pytest.mark.parametrize("change", ["workload", "timeout"])
def test_partial_new_version_cannot_borrow_old_reference_timings(
    tmp_path: Path, capsys: pytest.CaptureFixture[str], change: str
) -> None:
    cache, config, args, task, rows = _case(tmp_path)
    cache.append(task, rows)
    cache_module = importlib.import_module("eval_cache")
    observation = importlib.import_module("eval_observation")
    evaluator = importlib.import_module("slotted.slotted-eval")
    if change == "timeout":
        args.timeout += 1
    updated = cache_module.Cache(
        cache.store.path,
        ROOT,
        config,
        args,
        {task: "changed source" if change == "workload" else "generated source"},
    )
    pair = copy.deepcopy([row for row in rows if row.side in ("encoding-no-aliasing", "ref-nested-snapshot")])
    for row in pair:
        row.observation = "new-" + row.observation
        row.nodes, row.seconds = 30, 9.0
    pair[0].vs_ref = {pair[1].side: observation.Comparison(pair[0].observation, pair[1].observation, "isomorphic")}
    updated.append(task, pair)
    report = slotted_report(updated.store.records)
    selected = select_slotted_records(updated.store.records)
    assert {r["slotted"]["side"] for r in selected} == {r.side for r in pair}
    assert "missing ref-nested observation" in str(report.errors)
    nested = report.catalog.sections[0].blocks[1]
    assert isinstance(nested, ReportTable)
    assert [c.display for c in nested.rows[0].cells] == ["Array N=0", "9", "—"]
    assert evaluator.main(["--from", str(cache.store.path)]) == 1
    output = capsys.readouterr().out
    assert "| Array N=0 | 9 | — |" in output
    assert ERROR_TITLE in output and "0.125" not in output


def test_reused_diagnostic_certificates_are_checked_against_selected_observations(tmp_path: Path) -> None:
    cache, _, _, task, rows = _case(tmp_path)
    observation = importlib.import_module("eval_observation")
    by_side = {r.side: r for r in rows}
    encoding, nested = by_side["encoding"], by_side["ref-nested"]
    encoding.vs_ref[nested.side] = observation.Comparison(encoding.observation, nested.observation, "isomorphic")
    cache.append(task, rows)
    newer = copy.deepcopy(nested)
    newer.observation = "new-reference"
    newer.graph_issue = "reference graph dump exceeded timeout"
    cache.append(task, [newer])
    reused = cache.reuse(task, SIDES)
    assert reused is not None
    report = slotted_report(reused)
    assert not report.errors  # This pair is diagnostic; both required pairs still match.
    table = next(block for block in report.catalog.sections[0].blocks if block.id == "slotted-comparisons")
    assert isinstance(table, ReportTable)
    comparisons = {row.cells[2].display: row.cells[3].display for row in table.rows if row.cells[1].display == "egglog"}
    assert comparisons["ref-multi"] == "isomorphic"
    assert comparisons["ref-nested"] == "not compared: reference timeout"


@pytest.mark.parametrize("encoding,reference", EXACT_PAIRS.items())
@pytest.mark.parametrize("problem", ["counts", "missing-counts", "identity", "verdict", "certificate", "disabled"])
def test_exact_gate_rejects_bad_counts_and_certificates(
    tmp_path: Path, encoding: str, reference: str, problem: str
) -> None:
    cache, _, _, task, rows = _case(tmp_path)
    records = cache.append(task, rows)
    evidence = next(r["slotted"] for r in records if r["slotted"]["side"] == encoding)
    if problem == "counts":
        evidence["nodes"] += 1
    elif problem == "missing-counts":
        evidence["classes"] = None
    elif problem == "identity":
        evidence["observation"] = "another-run"
    elif problem == "verdict":
        evidence["vs_ref"][reference]["verdict"] = "inconclusive: search cap"
    elif problem == "certificate":
        evidence["vs_ref"].clear()
    else:
        evidence["counts"] = False
    assert slotted_report(records).errors
    assert not slotted_report(records, counts=False).errors


@pytest.mark.parametrize("outcome,display", [("no", "0.125"), ("error", "0.125"), ("timeout", "timeout")])
def test_unsuccessful_goals_keep_elapsed_time_separate(tmp_path: Path, outcome: str, display: str) -> None:
    cache, _, _, task, rows = _case(tmp_path)
    rows[-1].goal = outcome
    report = slotted_report(cache.append(task, rows))
    assert bool(report.errors) == (outcome != "timeout")
    nested = report.catalog.sections[0].blocks[1]
    assert isinstance(nested, ReportTable)
    assert nested.rows[0].cells[-1].display == display
    assert bool(slotted_report(cache.store.records, counts=False).errors) == (outcome != "timeout")


def test_missing_instrumentation_is_unavailable_but_wall_times_remain_comparable(tmp_path: Path) -> None:
    from benchmarking.reports.analysis import analyze_pair
    from benchmarking.reports.interactive_runtime import _endpoint_from_record, _file_from_record

    cache, _, _, task, rows = _case(tmp_path)
    rows[0].seconds, rows[2].seconds = 0.500, 0.125
    records = cache.append(task, rows)
    comparison = models.ComparisonSpec(
        _endpoint_from_record(records[2]),
        _endpoint_from_record(records[0]),
        (_file_from_record(records[0]),),
        1,
        30,
    )
    grouped = cache.store.grouped_report()
    analysis = analyze_pair(grouped, comparison, "rulesets")
    assert analysis.files[0].ratio.estimate.point == 4
    assert not analysis.timing
    runtime = InteractiveRuntime(grouped, scope_for_comparison(comparison))
    payload = json.loads(json.dumps(runtime.payload()))
    phase_text = json.dumps([s for s in payload["sections"] if s["id"] in ("phases", "rulesets")])
    assert "Phase timings are unavailable for the selected endpoints." in phase_text
    assert "Source rules shown: 0/0" not in phase_text
    assert "0%  0 ms" not in phase_text

    # Actual phase data remains usable for these same treatments.
    for record in (records[0], records[2]):
        instrumented = copy.deepcopy(record)
        instrumented["timing_summary"] = make_timing_summary()
        cache.store.append(instrumented)
    analysis = analyze_pair(cache.store.grouped_report(), comparison, "rulesets")
    assert analysis.files[0].ratio.estimate.point == 4
    assert analysis.timing[1].issue is None
    assert analysis.timing[1].wall_delta_ns == 375_000_000


def test_reference_timing_environment_ignores_debug_flags(monkeypatch: pytest.MonkeyPatch) -> None:
    importlib.import_module("slotted.slotted-eval")
    run = importlib.import_module("eval_run")
    flags = ("XMULTI_DEBUG", "XMULTI_DEBUG_RULE", "XMULTI_TRACE")
    for flag in flags:
        monkeypatch.setenv(flag, "1")
    monkeypatch.setenv("XMULTI_SUBST", "invalid")
    for side, policy in (("ref-nested", "syntactic"), ("ref-multi", "snapshot"), ("ref-nested-snapshot", "snapshot")):
        env = run.oracle_env(side, 10)
        assert not any(flag in env for flag in flags)
        assert env["XMULTI_SUBST"] == policy
        assert env["XMULTI_GROUP_SLOT_CAP"] == "10"
        assert env["PATH"] == os.environ["PATH"]


def test_saved_cli_and_nightly_use_identical_catalog_without_loading_graph_checker(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    from benchmarking.reports.render import render_markdown_report_document

    cache, _, _, task, rows = _case(tmp_path)
    records = cache.append(task, rows)
    evaluator = importlib.import_module("slotted.slotted-eval")
    page = tmp_path / "slotted.html"
    assert evaluator.main(["--from", str(cache.store.path), "--html", str(page)]) == 0
    assert capsys.readouterr().out.strip() == render_markdown_report_document(slotted_report(records).catalog)
    assert "Multipattern matching" in page.read_text() and "Nested matching" in page.read_text()
    code = """
import importlib, sys
module = importlib.import_module("slotted.slotted-eval")
assert module.main(["--from", sys.argv[1]]) == 0
assert not {"isomorphism", "eval_verify", "eval_workloads"}.intersection(sys.modules)
"""
    result = subprocess.run(
        [sys.executable, "-c", code, str(cache.store.path)], capture_output=True, text=True, cwd=ROOT
    )
    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize("error", [subprocess.CalledProcessError(1, ["cargo", "build"]), RuntimeError("reader bug")])
def test_collection_failure_has_distinct_exit_status(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, error: Exception
) -> None:
    evaluator = importlib.import_module("slotted.slotted-eval")

    def fail_build() -> None:
        raise error

    monkeypatch.setattr(evaluator, "build", fail_build)
    path = tmp_path / "observations.jsonl"
    assert evaluator.main(["array", "--params", "0", "--report", str(path)]) == 2
    assert not path.exists()


def test_saved_selection_uses_timestamp_order_and_keeps_rewrite_budgets(tmp_path: Path) -> None:
    cache, _, _, task, rows = _case(tmp_path)
    records = cache.append(task, rows)
    older = copy.deepcopy(records[0])
    older["started_at"], older["wall_sec"] = "2000-01-01T00:00:00Z", 999
    cache.store.append(older)
    selected = select_slotted_records(cache.store.records)
    assert selected[0]["wall_sec"] == 0.125
    longer = copy.deepcopy(records[0])
    longer["slotted"]["rounds"] = 12
    longer["file_sha256"] = "sha256:longer-workload"
    cache.store.append(longer)
    table = slotted_report(cache.store.records).catalog.sections[0].blocks[0]
    assert isinstance(table, ReportTable)
    assert [r.cells[0].display for r in table.rows] == ["Array N=0 [6 rounds]", "Array N=0 [12 rounds]"]
