"""Mixed proof/slotted caches preserve endpoint identities and exact certificates."""

from __future__ import annotations

import argparse
import base64
import importlib
import json
import re
from pathlib import Path
from typing import Any

import pytest

from benchmarking import models
from benchmarking.reports.catalog import ReportTable
from benchmarking.reports.interactive import write_interactive_report
from benchmarking.reports.interactive_runtime import InteractiveRuntime, scope_for_comparison
from benchmarking.reports.slotted import slotted_catalog
from benchmarking.reports.store import ReportStore

from .report_fixtures import make_endpoint, make_record

ROOT = Path(__file__).resolve().parents[1]


def _case(tmp_path: Path) -> tuple[Any, Any, Any, tuple[str, int], list[Any]]:
    evaluator = importlib.import_module("slotted.slotted-eval")
    cache_module = importlib.import_module("eval_cache")
    report_module = importlib.import_module("eval_report")
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
    for encoding, ref in report_module.EXACT_PAIRS.items():
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
    assert [row.observation for row in reused] == [row.observation for row in rows]
    assert all(row.seconds == 0.125 for row in reused)
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
    loaded, _ = module.load_rows(cache.store.path, merged=False)
    assert len(loaded) == 5  # A partial collection still reports reused earlier rows.
    assert loaded[0].verdict(loaded[2]).startswith("inconclusive:")


def test_single_page_embeds_shared_data_and_slotted_tables_without_iframe(tmp_path: Path) -> None:
    cache, _config, _args, task, rows = _case(tmp_path)
    proof_off = make_record(0, started_at="2026-01-01T00:00:00Z", treatment="off")
    proof_on = make_record(1, started_at="2026-01-01T00:00:01Z", treatment="proofs")
    cache.store.append(proof_off)
    cache.store.append(proof_on)
    cache.append(task, rows)
    store = ReportStore(cache.store.path)
    comparison = models.ComparisonSpec(
        make_endpoint(treatment="off"),
        make_endpoint(treatment="proofs"),
        (models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file"),),
        1,
        120,
    )
    runtime = InteractiveRuntime(store, scope_for_comparison(comparison))
    payload = json.dumps(runtime.initial_payload(comparison))
    assert "Multipattern matching" in payload and "Nested matching" in payload
    assert "SLOTTED CORRECTNESS" not in payload
    assert "slotted-reference" in payload
    assert "Slotted correctness and provenance" in json.dumps(runtime.apply(scope_for_comparison(comparison)))
    path = write_interactive_report(store, comparison, tmp_path / "page.html")
    page = path.read_text()
    assert '<iframe src="slotted.html"' not in page
    match = re.search(r'<script id="report-envelope"[^>]*>(.*?)</script>', page)
    assert match
    envelope = json.loads(base64.b64decode(match[1]))
    assert base64.b64decode(envelope["report_jsonl_base64"]) == store.path.read_bytes()
    assert envelope["initial_payload"]["sections"][-1]["id"] == "slotted"

    # A bogus positive certificate must not conceal wrong raw counts.
    rows[0].nodes += 1
    cache.append(task, [rows[0]])
    catalog = slotted_catalog(cache.store.records)
    assert "different: nodes" in str(catalog)
    assert "SLOTTED CORRECTNESS CHECKS FAILED OR INCOMPLETE" in str(catalog)


def test_timeout_cells_show_the_outcome_in_cli_and_nightly(tmp_path: Path) -> None:
    cache, _config, _args, task, rows = _case(tmp_path)
    reports = importlib.import_module("eval_report")
    encoding = rows[0]
    encoding.goal, encoding.seconds = "timeout", 300.125
    cache.append(task, rows)

    assert reports.seconds_cell(encoding) == "timeout"
    assert reports.summary(rows, ("encoding", "ref-multi"))[1][0][1:] == ["timeout", "0.125"]
    catalog = slotted_catalog(cache.store.records)
    table = catalog.sections[0].blocks[0]
    assert isinstance(table, ReportTable)
    assert table.rows[0].cells[1].display == "timeout"
    # Keep elapsed time in the cache and cell data, but don't print it as a result.
    assert cache.store.records[0]["wall_sec"] == 300.125
    assert table.rows[0].cells[1].raw == 300.125


def test_reference_treatments_cannot_silently_run_proofs() -> None:
    from benchmarking.targets import treatment_flags

    assert treatment_flags("slotted") == ["--slotted"]
    assert treatment_flags("slotted-no-aliasing") == ["--slotted", "--slotted-no-aliasing"]
    for treatment in ("multi", "nested", "nested-snapshot"):
        with pytest.raises(ValueError, match="reference matcher"):
            treatment_flags(treatment)
