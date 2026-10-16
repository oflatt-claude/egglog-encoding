"""Persist slotted timings and graph comparison evidence in ReportStore.

A workload key hashes the generated inputs, checking policy and implementation.
Binary hashes identify each endpoint independently. Exact comparisons remain tied
to observation IDs: partially reusable groups are recollected together so no new
observation inherits an old pair's certificate.
"""

import hashlib
import json
import subprocess
from dataclasses import asdict
from datetime import UTC, datetime

from benchmarking.models import TargetRow
from benchmarking.reports.store import REPORT_SCHEMA_VERSION, CacheKey, ReportStore

ENDPOINTS = {
    "encoding": "slotted",
    "encoding-no-aliasing": "slotted-no-aliasing",
    "ref-multi": "multi",
    "ref-nested": "nested",
    "ref-nested-snapshot": "nested-snapshot",
}


def digest(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def file_digest(path):
    with path.open("rb") as handle:
        return "sha256:" + hashlib.file_digest(handle, "sha256").hexdigest()


def target(root, *, reference=False):
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=root, text=True).strip()

    # The xmulti binary includes its pinned reference dependency. Its own binary
    # hash is the cache identity; this provenance records the harness checkout.
    return TargetRow(
        source=".",
        path=str(root),
        git_ref="HEAD",
        git_sha=git("rev-parse", "HEAD"),
        is_dirty=bool(git("status", "--porcelain")),
        label="slotted-reference" if reference else "branch",
    )


def record(row, batch, *, key, provenance, counts):
    """Build a report record with timing, provenance, and graph evidence."""
    evidence = row.as_dict(batch)
    evidence["counts"] = counts
    status = "success" if row.goal == "yes" else "timed-out" if row.goal == "timeout" else "failure"
    return {
        "report_schema_version": REPORT_SCHEMA_VERSION,
        "started_at": datetime.now(UTC).isoformat(),
        "status": status,
        **{"target_" + name: value for name, value in asdict(provenance).items()},
        "binary_sha256": key.binary_sha256,
        "file_path": f"slotted/{row.study}/{row.case} [{row.rounds} iterations]",
        "file_sha256": key.file_sha256,
        "fact_directory_path": None,
        "fact_directory_sha256": "",
        "disequality_encoding": key.disequality_encoding,
        "treatment": key.treatment,
        "timeout_sec": key.timeout_sec,
        # Retain elapsed time even on a failed goal, as in the paper tables.
        "wall_sec": row.seconds,
        "max_rss_bytes": None,
        "error_exit_code": None,
        "error_signal": None,
        "error_message": None if status == "success" else row.goal,
        "timing_summary": None,
        "slotted": evidence,
    }


def row_from_record(record):
    from eval_report import Row

    row = Row.from_dict(record["slotted"])
    row.seconds = record["wall_sec"]
    return row


def load_rows(path, merged):
    """Select the latest slotted observations, including reused earlier batches.

    ``merged`` remains a CLI compatibility alias; cache reuse makes a batch-only
    report incomplete whenever an invocation collects just part of its plan.
    """
    from dataclasses import replace

    records = [r for r in ReportStore(path).records if "slotted" in r]
    if not records:
        return [], None
    latest = {}
    for record_ in records:
        row = row_from_record(record_)
        latest[*row.workload(), row.side] = row
    for row in latest.values():
        for side, comparison in row.vs_ref.items():
            reference = latest.get((*row.workload(), side))
            row.vs_ref[side] = replace(comparison, verdict=row.verdict(reference))
    return list(latest.values()), None if merged else records[-1]["started_at"]


class Cache:
    def __init__(self, path, root, config, args, manifests):
        self.store = ReportStore(path)
        self.counts, self.timeout = args.counts, args.timeout
        self.force = getattr(args, "force_run", False)
        self.batch = datetime.now(UTC).isoformat()
        self.binaries = {
            "encoding": file_digest(config.egglog),
            "reference": file_digest(config.xmulti),
        }
        self.targets = {False: target(root), True: target(root, reference=True)}
        # Hash the generated workload and all code that determines the reference
        # translation or checks its result. Editing report styling does not change
        # the measured program or invalidate its certificates.
        dependencies = [
            "slotted/slotted-eval.py",
            "slotted/eval_cache.py",
            "slotted/eval_run.py",
            "slotted/eval_verify.py",
            "slotted/eval_workloads.py",
            "slotted/paper_fixtures.py",
            "slotted/slotted-egglog.py",
            "slotted/slotted-encoder.py",
            "slotted/xdiff/xdiff.py",
            "slotted/xdiff/xarray.py",
            "slotted/xdiff/xsdql.py",
            "slotted/xdiff/isomorphism.py",
        ]
        sources = {name: file_digest(root / name) for name in dependencies}
        sources.update({str(p.relative_to(root)): file_digest(p) for p in (root / "slotted/languages").glob("*.egg")})
        self.hashes = {
            task: digest(
                json.dumps(
                    {
                        "workload": manifest,
                        "sources": sources,
                        "counts": args.counts,
                        "group_cap": config.group_cap,
                        "jobs": args.jobs,
                    },
                    sort_keys=True,
                ).encode()
            )
            for task, manifest in manifests.items()
        }

    def key(self, task, side):
        return CacheKey(
            self.binaries["reference" if side.startswith("ref-") else "encoding"],
            self.hashes[task],
            ENDPOINTS[side],
            self.timeout,
        )

    def reuse(self, task, sides):
        if self.force:
            return None
        selected = [self.store.latest_records(self.key(task, side), 1) for side in sides]
        if any(not rows for rows in selected):
            return None
        rows = [row_from_record(records[0].record) for records in selected]
        if self.counts:
            from eval_report import EXACT_PAIRS

            by_side = {row.side: row for row in rows}
            for encoding, reference in EXACT_PAIRS.items():
                if encoding in by_side and reference in by_side:
                    comparison = by_side[encoding].vs_ref.get(reference)
                    if comparison is None or (comparison.encoding, comparison.reference) != (
                        by_side[encoding].observation,
                        by_side[reference].observation,
                    ):
                        return None
        return rows

    def append(self, task, rows):
        for row in rows:
            self.store.append(
                record(
                    row,
                    self.batch,
                    key=self.key(task, row.side),
                    provenance=self.targets[row.side.startswith("ref-")],
                    counts=self.counts,
                )
            )
