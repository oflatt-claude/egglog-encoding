"""In-memory results of one treatment on one workload; nothing is cached."""

from dataclasses import dataclass, field


@dataclass(eq=False)
class Row:
    study: str
    case: str
    side: str
    rounds: int
    rules: int | None = None
    goal: str = "?"
    saturated: str = "?"
    seconds: float | None = None
    classes: int | None = None
    nodes: int | None = None
    checks: str | None = None
    substitution: str | None = None
    unsupported: dict[str, str] = field(default_factory=dict)
    vs_ref: dict = field(default_factory=dict, repr=False)
    graph: object = field(default=None, repr=False)
    graph_issue: str | None = None

    def workload(self):
        return self.study, self.case, self.rounds, self.rules

    def verdict(self, reference):
        if reference is None:
            return "inconclusive: reference observation unavailable"
        comparison = self.vs_ref.get(reference.side)
        if comparison is None or comparison.encoding is not self or comparison.reference is not reference:
            return "inconclusive: selected observations have not been compared"
        return comparison.verdict

    def as_dict(self):
        return {
            **{key: value for key, value in vars(self).items() if key not in ("graph", "vs_ref")},
            "vs_ref": {side: comparison.verdict for side, comparison in self.vs_ref.items()},
        }


@dataclass(frozen=True)
class Comparison:
    """Keep the actual compared rows together so a verdict cannot certify another run."""

    encoding: Row
    reference: Row
    verdict: str
