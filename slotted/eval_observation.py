"""Transient observations collected before conversion to shared report records."""

import uuid
from dataclasses import asdict, dataclass

from benchmarking.reports.slotted import comparison_verdict


@dataclass(frozen=True)
class Comparison:
    """A verdict about exactly two observations, including inconclusive outcomes."""

    encoding: str
    reference: str
    verdict: str


class Row:
    def __init__(self, study, case, side, rounds, rules=None):
        self.study, self.case, self.side, self.rounds, self.rules = study, case, side, rounds, rules
        self.jobs = 1
        self.observation = uuid.uuid4().hex
        self.goal, self.saturated, self.seconds = "?", "?", None
        self.classes, self.nodes = None, None
        self.checks = None  # the oracle's `CONFIG checks=` answer, for reference sides
        self.substitution = None  # the oracle's `CONFIG substitution=` answer
        self.paper = None  # Table 1's slotted row for this workload, when it has one
        self.unsupported = {}  # Treatments this workload cannot express, with reasons.
        #: encoding side: per reference side, how its final graph compares (`compare`)
        self.vs_ref = {}
        self.graph = None  # only used during comparison; not recorded in the cache
        self.graph_issue = None

    def workload(self):
        return self.study, self.case, self.rounds, self.rules

    def verdict(self, reference):
        return comparison_verdict(self.as_dict(""), None if reference is None else reference.as_dict(""))

    def as_dict(self, batch):
        """Untimed evidence; the shared cache owns timing and endpoint provenance."""
        d = {key: value for key, value in vars(self).items() if key not in ("graph", "seconds")}
        d["vs_ref"] = {side: asdict(comparison) for side, comparison in self.vs_ref.items()}
        d["batch"] = batch
        d["counts"] = True
        return d
