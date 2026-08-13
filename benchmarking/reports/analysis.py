"""Compute renderer-neutral statistics for one benchmark endpoint pair.

This module selects observations, estimates means and confidence intervals,
computes Fieller ratios, exhaustively attributes wall time, and ranks changed
rulesets. Persistence lives in :mod:`benchmarking.reports.store`; all labels,
units, and presentation policy live in :mod:`benchmarking.reports.presentation`.
"""

from __future__ import annotations

import math
import statistics
from typing import Literal, NamedTuple, cast

from scipy import stats

from ..models import ComparisonSpec, DetailLevel
from .store import CacheKey, IndexedRecord, ReportStore

MetricName = Literal["wall_sec", "max_rss_bytes"]
ResultClass = Literal["higher", "invalid", "lower", "point_only", "unclear"]
SummaryKind = Literal["suite", "lowest_file", "highest_file"]
MechanismName = Literal["typecheck", "frontend", "program", "equality", "commands", "residual"]
RulesetPhaseName = Literal["assembly", "search", "apply", "execution", "merge", "rebuild"]
RulesetMechanism = Literal["program", "equality"]
RulesetRowKind = Literal["aggregate", "ruleset", "native_rebuild", "other"]
OptimizationScenario = Literal[
    "typecheck",
    "frontend",
    "frontend_and_typecheck",
    "equality_assembly",
    "equality",
    "program",
    "non_program",
    "all_recorded",
]

type _MetricKey = tuple[int, int, MetricName]
type _ObservationKey = tuple[int, int]
type _TimingPath = tuple[str, ...]

_METRICS: tuple[MetricName, ...] = ("wall_sec", "max_rss_bytes")
_RULESET_PHASES: tuple[RulesetPhaseName, ...] = (
    "assembly",
    "search",
    "apply",
    "execution",
    "merge",
    "rebuild",
)
_RULESET_MECHANISMS: tuple[RulesetMechanism, ...] = ("program", "equality")
_MECHANISMS: tuple[MechanismName, ...] = (
    "typecheck",
    "frontend",
    "program",
    "equality",
    "commands",
    "residual",
)
RULESET_CONTRIBUTOR_LIMIT = 5


class Estimate(NamedTuple):
    """One point estimate and its optional confidence interval."""

    point: float | None
    ci_low: float | None
    ci_high: float | None


class RatioEstimate(NamedTuple):
    """One ratio estimate plus its interpretation and availability issue."""

    estimate: Estimate
    result_class: ResultClass
    issue: str | None


class PhaseValues(NamedTuple):
    """Six recorded timing components aggregated for one observation/ruleset."""

    assembly: float
    search: float
    apply: float
    execution: float
    merge: float
    rebuild: float


class RulesetDelta(NamedTuple):
    """One exact total delta and its six timing-component deltas."""

    total: float
    phases: PhaseValues


class SummaryView(NamedTuple):
    """One suite or per-file tail summary."""

    metric: MetricName
    summary_kind: SummaryKind
    file_order: int | None
    ratio: RatioEstimate


class FileComparisonView(NamedTuple):
    """One file/metric comparison."""

    file_order: int
    metric: MetricName
    baseline: Estimate
    candidate: Estimate
    ratio: RatioEstimate


class SlowdownCell(NamedTuple):
    """One mechanism's delta and share of the observed wall slowdown."""

    delta_ns: float | None
    slowdown_share: float | None


class SlowdownValues(NamedTuple):
    """The six additive mechanism cells displayed for one row."""

    typecheck: SlowdownCell
    frontend: SlowdownCell
    program: SlowdownCell
    equality: SlowdownCell
    commands: SlowdownCell
    residual: SlowdownCell


class SlowdownDecompositionView(NamedTuple):
    """One per-file or suite-wide additive slowdown decomposition."""

    file_order: int | None
    wall_delta_ns: float | None
    mechanisms: SlowdownValues
    residual_warning: bool
    issue: str | None


class RulesetContributorView(NamedTuple):
    """One mechanism parent, named child, native rebuild, or exact remainder."""

    file_order: int
    kind: RulesetRowKind
    mechanism: RulesetMechanism
    name: str
    ruleset_count: int
    delta: RulesetDelta


class OptimizationCeilingView(NamedTuple):
    """One suite-wide accounting counterfactual with no causal-speedup claim."""

    scenario: OptimizationScenario
    reset_delta_ns: float
    remaining_delta_ns: float
    counterfactual_ratio: float


class PairReportViewData(NamedTuple):
    """Typed analysis collections requested by one cumulative detail level."""

    summary: tuple[SummaryView, ...]
    files: tuple[FileComparisonView, ...]
    decomposition: tuple[SlowdownDecompositionView, ...]
    ceilings: tuple[OptimizationCeilingView, ...]
    rulesets: tuple[RulesetContributorView, ...]


class _MetricEstimate(NamedTuple):
    sample_count: int
    estimate: Estimate
    var_mean: float | None
    issue: str | None


class _TimingAggregate(NamedTuple):
    """Aligned samples for the open timing paths in one endpoint/file selection."""

    observation_count: int
    paths: dict[_TimingPath, list[float]]
    residuals: list[float]


def analyze_pair(
    store: ReportStore,
    comparison: ComparisonSpec,
    detail: DetailLevel,
) -> PairReportViewData:
    """Return every presentation row requested for one exact endpoint pair."""

    observations = _selected_observations(store, comparison)
    issues = {key: _selection_issue(rows, comparison.rounds) for key, rows in observations.items()}
    t_critical = None if comparison.rounds < 2 else float(stats.t.ppf(0.975, comparison.rounds - 1))
    estimates = _metric_estimates(observations, issues, t_critical)
    file_rows = _file_comparisons(comparison, estimates, t_critical)
    summary = _summary_rows(comparison, estimates, file_rows, t_critical)

    if detail == "summary":
        return PairReportViewData(summary, (), (), (), ())
    if detail == "files":
        return PairReportViewData(summary, file_rows, (), (), ())

    timing = _timing_aggregates(observations)
    decomposition = _slowdown_decomposition(comparison, timing, issues, estimates)
    ceilings = _optimization_ceilings(comparison, timing, estimates, decomposition)
    if detail == "phases":
        return PairReportViewData(summary, file_rows, decomposition, ceilings, ())
    rulesets = _ruleset_contributors(comparison, timing, issues)
    return PairReportViewData(summary, file_rows, decomposition, ceilings, rulesets)


def _selected_observations(
    store: ReportStore,
    comparison: ComparisonSpec,
) -> dict[_ObservationKey, tuple[IndexedRecord, ...]]:
    selected: dict[_ObservationKey, tuple[IndexedRecord, ...]] = {}
    for endpoint_order, endpoint in enumerate((comparison.baseline, comparison.candidate)):
        for file_order, file in enumerate(comparison.files):
            key = CacheKey.for_endpoint(endpoint, file, comparison.timeout_sec)
            selected[(endpoint_order, file_order)] = store.latest_records(key, comparison.rounds)
    return selected


def _selection_issue(rows: tuple[IndexedRecord, ...], rounds: int) -> str | None:
    if len(rows) < rounds:
        return f"missing {rounds - len(rows)} row(s)"
    statuses = tuple(row.record["status"] for row in rows)
    if "failure" in statuses:
        return "failure row selected"
    if "timed-out" in statuses:
        return "timeout row selected"
    return None


def _metric_estimates(
    observations: dict[_ObservationKey, tuple[IndexedRecord, ...]],
    issues: dict[_ObservationKey, str | None],
    t_critical: float | None,
) -> dict[_MetricKey, _MetricEstimate]:
    result: dict[_MetricKey, _MetricEstimate] = {}
    for (endpoint_order, file_order), rows in observations.items():
        for metric in _METRICS:
            values = [float(value) for row in rows if (value := row.record[metric]) is not None]
            issue = issues[(endpoint_order, file_order)]
            if issue is None and len(values) != len(rows):
                issue = "wall time unavailable" if metric == "wall_sec" else "peak RSS unavailable"
            result[(endpoint_order, file_order, metric)] = _sample_estimate(values, issue, t_critical)
    return result


def _file_comparisons(
    comparison: ComparisonSpec,
    estimates: dict[_MetricKey, _MetricEstimate],
    t_critical: float | None,
) -> tuple[FileComparisonView, ...]:
    rows: list[FileComparisonView] = []
    for file_order in range(len(comparison.files)):
        for metric in _METRICS:
            baseline = estimates[(0, file_order, metric)]
            candidate = estimates[(1, file_order, metric)]
            rows.append(
                FileComparisonView(
                    file_order,
                    metric,
                    baseline.estimate,
                    candidate.estimate,
                    _ratio_estimate(baseline, candidate, t_critical),
                )
            )
    return tuple(rows)


def _ratio_estimate(
    baseline: _MetricEstimate,
    candidate: _MetricEstimate,
    t_critical: float | None,
) -> RatioEstimate:
    baseline_mean = baseline.estimate.point
    candidate_mean = candidate.estimate.point
    issue = baseline.issue or candidate.issue
    if issue is not None:
        return RatioEstimate(Estimate(None, None, None), "invalid", issue)
    if baseline_mean is None or candidate_mean is None:
        return RatioEstimate(Estimate(None, None, None), "invalid", "estimate unavailable")
    if baseline_mean <= 0:
        return RatioEstimate(Estimate(None, None, None), "invalid", "baseline mean is not positive")

    point = candidate_mean / baseline_mean
    if min(baseline.sample_count, candidate.sample_count) < 2:
        return RatioEstimate(Estimate(point, None, None), "point_only", "CI undefined for n < 2")
    if baseline.var_mean is None or candidate.var_mean is None or t_critical is None:
        raise ValueError("multi-sample ratio is missing variance or its t critical value")
    critical_squared = t_critical * t_critical
    fieller_a = baseline_mean * baseline_mean - critical_squared * baseline.var_mean
    fieller_d = candidate_mean * candidate_mean - critical_squared * candidate.var_mean
    radicand = (baseline_mean * candidate_mean) ** 2 - fieller_a * fieller_d
    if fieller_a <= 0 or radicand < 0:
        return RatioEstimate(Estimate(point, None, None), "point_only", "Fieller interval undefined")
    center = baseline_mean * candidate_mean / fieller_a
    half_width = math.sqrt(radicand) / fieller_a
    ci_low = center - half_width
    ci_high = center + half_width
    return RatioEstimate(Estimate(point, ci_low, ci_high), _result_class(point, ci_low, ci_high), None)


def _result_class(point: float | None, ci_low: float | None, ci_high: float | None) -> ResultClass:
    if point is None:
        return "invalid"
    if ci_low is None or ci_high is None:
        return "point_only"
    if ci_high < 1.0:
        return "lower"
    if ci_low > 1.0:
        return "higher"
    return "unclear"


def _summary_rows(
    comparison: ComparisonSpec,
    estimates: dict[_MetricKey, _MetricEstimate],
    file_rows: tuple[FileComparisonView, ...],
    t_critical: float | None,
) -> tuple[SummaryView, ...]:
    baseline = [estimates[(0, order, "wall_sec")] for order in range(len(comparison.files))]
    candidate = [estimates[(1, order, "wall_sec")] for order in range(len(comparison.files))]
    first_issue = next(
        (
            issue
            for baseline_estimate, candidate_estimate in zip(baseline, candidate, strict=True)
            if (issue := baseline_estimate.issue or candidate_estimate.issue) is not None
        ),
        None,
    )
    sample_count = min(estimate.sample_count for estimate in baseline)
    suite_ratio = _ratio_estimate(
        _MetricEstimate(
            sample_count,
            Estimate(math.fsum(estimate.estimate.point or 0.0 for estimate in baseline), None, None),
            math.fsum(estimate.var_mean or 0.0 for estimate in baseline),
            first_issue,
        ),
        _MetricEstimate(
            sample_count,
            Estimate(math.fsum(estimate.estimate.point or 0.0 for estimate in candidate), None, None),
            math.fsum(estimate.var_mean or 0.0 for estimate in candidate),
            None,
        ),
        t_critical,
    )
    rows = [SummaryView("wall_sec", "suite", None, suite_ratio)]
    tail_specs: tuple[tuple[MetricName, SummaryKind], ...] = (
        ("wall_sec", "lowest_file"),
        ("wall_sec", "highest_file"),
        ("max_rss_bytes", "lowest_file"),
        ("max_rss_bytes", "highest_file"),
    )
    for metric, kind in tail_specs:
        metric_rows = tuple(row for row in file_rows if row.metric == metric)
        comparable = tuple(row for row in metric_rows if row.ratio.estimate.point is not None)
        selected: FileComparisonView | None
        if kind == "lowest_file":
            selected = min(comparable, key=lambda row: (row.ratio.estimate.point, row.file_order), default=None)
        else:
            selected = max(comparable, key=lambda row: (row.ratio.estimate.point, row.file_order), default=None)
        if selected is None:
            issue = (
                next(
                    (row.ratio.issue for row in metric_rows if row.ratio.estimate.point is None),
                    None,
                )
                or "no comparable files"
            )
            ratio = RatioEstimate(Estimate(None, None, None), "invalid", issue)
            file_order = None
        else:
            ratio = selected.ratio
            file_order = selected.file_order
        rows.append(SummaryView(metric, kind, file_order, ratio))
    return tuple(rows)


def _slowdown_decomposition(
    comparison: ComparisonSpec,
    timing: dict[_ObservationKey, _TimingAggregate],
    issues: dict[_ObservationKey, str | None],
    metric_estimates: dict[_MetricKey, _MetricEstimate],
) -> tuple[SlowdownDecompositionView, ...]:
    points: dict[tuple[int, int, MechanismName], float | None] = {}
    for (endpoint_order, file_order), aggregate in timing.items():
        for mechanism in _MECHANISMS:
            issue = issues[(endpoint_order, file_order)]
            if mechanism == "residual" and issue is None:
                issue = metric_estimates[(endpoint_order, file_order, "wall_sec")].issue
            paths = [path for path in aggregate.paths if path[0] == mechanism]
            values = aggregate.residuals if mechanism == "residual" else _sum_path_samples(aggregate, paths)
            points[(endpoint_order, file_order, mechanism)] = (
                statistics.fmean(values) if issue is None and values else None
            )

    result: list[SlowdownDecompositionView] = []
    for file_order in range(len(comparison.files)):
        baseline_wall = metric_estimates[(0, file_order, "wall_sec")].estimate.point
        candidate_wall = metric_estimates[(1, file_order, "wall_sec")].estimate.point
        wall_delta_ns = (
            None
            if baseline_wall is None or candidate_wall is None
            else (candidate_wall - baseline_wall) * 1_000_000_000.0
        )
        cells: list[SlowdownCell] = []
        for mechanism in _MECHANISMS:
            baseline_point = points[(0, file_order, mechanism)]
            candidate_point = points[(1, file_order, mechanism)]
            delta = None if baseline_point is None or candidate_point is None else candidate_point - baseline_point
            cells.append(SlowdownCell(delta, _share(delta, wall_delta_ns)))
        baseline_residual = points[(0, file_order, "residual")]
        candidate_residual = points[(1, file_order, "residual")]
        issue = (
            issues[(0, file_order)]
            or issues[(1, file_order)]
            or metric_estimates[(0, file_order, "wall_sec")].issue
            or metric_estimates[(1, file_order, "wall_sec")].issue
        )
        result.append(
            SlowdownDecompositionView(
                file_order,
                wall_delta_ns,
                SlowdownValues(*cells),
                (baseline_residual is not None and baseline_residual < 0)
                or (candidate_residual is not None and candidate_residual < 0),
                issue,
            )
        )

    suite_issue = next((row.issue for row in result if row.issue is not None), None)
    if suite_issue is None:
        suite_wall_delta = sum(cast(float, row.wall_delta_ns) for row in result)
        suite_cells = []
        for mechanism_index in range(len(_MECHANISMS)):
            delta = sum(cast(float, row.mechanisms[mechanism_index].delta_ns) for row in result)
            suite_cells.append(SlowdownCell(delta, _share(delta, suite_wall_delta)))
    else:
        suite_wall_delta = None
        suite_cells = [SlowdownCell(None, None) for _ in _MECHANISMS]
    suite = SlowdownDecompositionView(
        None,
        suite_wall_delta,
        SlowdownValues(*suite_cells),
        any(row.residual_warning for row in result),
        suite_issue,
    )
    return (suite, *result)


def _optimization_ceilings(
    comparison: ComparisonSpec,
    timing: dict[_ObservationKey, _TimingAggregate],
    metric_estimates: dict[_MetricKey, _MetricEstimate],
    decomposition: tuple[SlowdownDecompositionView, ...],
) -> tuple[OptimizationCeilingView, ...]:
    """Reset selected suite deltas to zero as optimistic accounting bounds."""

    scenarios: tuple[OptimizationScenario, ...] = (
        "typecheck",
        "frontend",
        "frontend_and_typecheck",
        "equality_assembly",
        "equality",
        "program",
        "non_program",
        "all_recorded",
    )
    if decomposition[0].issue is not None:
        return ()
    baseline_points = [
        metric_estimates[(0, file_order, "wall_sec")].estimate.point for file_order in range(len(comparison.files))
    ]
    candidate_points = [
        metric_estimates[(1, file_order, "wall_sec")].estimate.point for file_order in range(len(comparison.files))
    ]
    if None in baseline_points or None in candidate_points:
        return ()

    baseline_wall_ns = math.fsum(cast(float, point) for point in baseline_points) * 1_000_000_000.0
    candidate_wall_ns = math.fsum(cast(float, point) for point in candidate_points) * 1_000_000_000.0
    if baseline_wall_ns <= 0 or candidate_wall_ns <= baseline_wall_ns:
        return ()

    equality_assembly_delta = 0.0
    for file_order in range(len(comparison.files)):
        endpoint_means = []
        for endpoint_order in (0, 1):
            aggregate = timing[(endpoint_order, file_order)]
            paths = [
                path for path in aggregate.paths if len(path) >= 2 and path[0] == "equality" and path[1] == "assembly"
            ]
            endpoint_means.append(statistics.fmean(_sum_path_samples(aggregate, paths)))
        equality_assembly_delta += endpoint_means[1] - endpoint_means[0]

    suite = decomposition[0]
    deltas = suite.mechanisms
    mechanism_deltas = (deltas.typecheck, deltas.frontend, deltas.program, deltas.equality, deltas.commands)
    if any(cell.delta_ns is None for cell in mechanism_deltas):
        return ()
    typecheck = cast(float, deltas.typecheck.delta_ns)
    frontend = cast(float, deltas.frontend.delta_ns)
    program = cast(float, deltas.program.delta_ns)
    equality = cast(float, deltas.equality.delta_ns)
    commands = cast(float, deltas.commands.delta_ns)
    positive = tuple(max(delta, 0.0) for delta in (typecheck, frontend, program, equality, commands))
    typecheck_added, frontend_added, program_added, equality_added, commands_added = positive
    reset_deltas = (
        typecheck_added,
        frontend_added,
        typecheck_added + frontend_added,
        max(equality_assembly_delta, 0.0),
        equality_added,
        program_added,
        typecheck_added + frontend_added + equality_added + commands_added,
        math.fsum(positive),
    )
    wall_delta = candidate_wall_ns - baseline_wall_ns
    return tuple(
        OptimizationCeilingView(
            scenario,
            reset_delta,
            wall_delta - reset_delta,
            (candidate_wall_ns - reset_delta) / baseline_wall_ns,
        )
        for scenario, reset_delta in zip(scenarios, reset_deltas, strict=True)
    )


def _timing_aggregates(
    observations: dict[_ObservationKey, tuple[IndexedRecord, ...]],
) -> dict[_ObservationKey, _TimingAggregate]:
    result: dict[_ObservationKey, _TimingAggregate] = {}
    for key, rows in observations.items():
        aggregate = _TimingAggregate(len(rows), {}, [])
        for observation_index, row in enumerate(rows):
            record = row.record
            if record["status"] != "success":
                for samples in aggregate.paths.values():
                    samples.append(0.0)
                continue
            summary = record["timing_summary"]
            if summary is None:
                raise ValueError("successful benchmark record is missing its timing summary")
            observation: dict[_TimingPath, float] = {}
            recorded = 0.0
            for leaf in summary["timings"]:
                path = tuple(leaf["path"])
                if not path:
                    raise ValueError("timing path must not be empty")
                if path[0] == "residual":
                    raise ValueError("residual is derived rather than recorded")
                if path[0] not in _MECHANISMS[:-1]:
                    raise ValueError(f"unknown timing responsibility {path[0]!r}")
                duration = float(leaf["ns"])
                observation[path] = observation.get(path, 0.0) + duration
                recorded += duration
            for path, samples in aggregate.paths.items():
                samples.append(observation.pop(path, 0.0))
            for path, duration in observation.items():
                aggregate.paths[path] = [0.0] * observation_index + [duration]
            wall_sec = record["wall_sec"]
            if wall_sec is not None:
                aggregate.residuals.append(wall_sec * 1_000_000_000.0 - recorded)
        result[key] = aggregate
    return result


def _sum_path_samples(aggregate: _TimingAggregate, paths: list[_TimingPath]) -> list[float]:
    """Add selected exclusive leaves observation by observation."""

    return [math.fsum(aggregate.paths[path][index] for path in paths) for index in range(aggregate.observation_count)]


def _ruleset_contributors(
    comparison: ComparisonSpec,
    timing: dict[_ObservationKey, _TimingAggregate],
    issues: dict[_ObservationKey, str | None],
) -> tuple[RulesetContributorView, ...]:
    """Unfold Program and Equality into truthful per-file child partitions."""

    result: list[RulesetContributorView] = []
    for file_order in range(len(comparison.files)):
        if issues[(0, file_order)] is not None or issues[(1, file_order)] is not None:
            continue
        source_names = sorted(
            {
                path[2]
                for endpoint_order in (0, 1)
                for path in timing[(endpoint_order, file_order)].paths
                if len(path) == 3 and path[0] == "program"
            }
        )
        maintenance_names = sorted(
            {
                path[2]
                for endpoint_order in (0, 1)
                for path in timing[(endpoint_order, file_order)].paths
                if len(path) == 3 and path[0] == "equality" and path[1] != "rebuild"
            }
        )

        names_by_mechanism = {"program": source_names, "equality": maintenance_names}
        children: dict[RulesetMechanism, list[RulesetContributorView]] = {"program": [], "equality": []}
        for mechanism in _RULESET_MECHANISMS:
            for name in names_by_mechanism[mechanism]:
                delta = _ruleset_phase_deltas(timing, file_order, name, mechanism)
                if any(delta.phases):
                    children[mechanism].append(RulesetContributorView(file_order, "ruleset", mechanism, name, 1, delta))
            children[mechanism].sort(key=lambda row: (-abs(row.delta.total), row.name))

        source_rebuild_deltas: list[float] = [
            rebuild_delta
            for name in source_names
            if (
                rebuild_delta := _ruleset_phase_delta(
                    timing,
                    file_order,
                    name,
                    "equality",
                    "rebuild",
                )
            )
            != 0
        ]
        if source_rebuild_deltas:
            rebuild_delta = math.fsum(source_rebuild_deltas)
            children["equality"].append(
                RulesetContributorView(
                    file_order,
                    "native_rebuild",
                    "equality",
                    "",
                    0,
                    RulesetDelta(
                        rebuild_delta,
                        PhaseValues(0.0, 0.0, 0.0, 0.0, 0.0, rebuild_delta),
                    ),
                )
            )

        for mechanism in _RULESET_MECHANISMS:
            group = children[mechanism]
            result.append(
                RulesetContributorView(
                    file_order,
                    "aggregate",
                    mechanism,
                    "",
                    sum(row.ruleset_count for row in group),
                    _sum_ruleset_deltas(group),
                )
            )
            if mechanism == "program" and len(group) > RULESET_CONTRIBUTOR_LIMIT:
                omitted = group[RULESET_CONTRIBUTOR_LIMIT:]
                result.extend(group[:RULESET_CONTRIBUTOR_LIMIT])
                result.append(
                    RulesetContributorView(
                        file_order,
                        "other",
                        mechanism,
                        "",
                        len(omitted),
                        _sum_ruleset_deltas(omitted),
                    )
                )
            else:
                result.extend(group)
    return tuple(result)


def _ruleset_phase_delta(
    timing: dict[_ObservationKey, _TimingAggregate],
    file_order: int,
    name: str,
    responsibility: RulesetMechanism,
    phase: RulesetPhaseName,
) -> float:
    """Subtract one named responsibility/phase mean across the endpoints."""

    def mean(endpoint_order: int) -> float:
        aggregate = timing[(endpoint_order, file_order)]
        paths: list[_TimingPath] = [
            path
            for path in aggregate.paths
            if len(path) == 3 and path[0] == responsibility and path[1] == phase and path[2] == name
        ]
        if not paths:
            return 0.0
        return statistics.fmean(_sum_path_samples(aggregate, paths))

    return mean(1) - mean(0)


def _ruleset_phase_deltas(
    timing: dict[_ObservationKey, _TimingAggregate],
    file_order: int,
    name: str,
    responsibility: RulesetMechanism,
) -> RulesetDelta:
    """Return own-work Program phases or complete Equality-maintenance phases."""

    phases = PhaseValues(
        *(
            0.0
            if responsibility == "program" and phase == "rebuild"
            else _ruleset_phase_delta(timing, file_order, name, responsibility, phase)
            for phase in _RULESET_PHASES
        )
    )
    return RulesetDelta(math.fsum(phases), phases)


def _sum_ruleset_deltas(rows: list[RulesetContributorView]) -> RulesetDelta:
    """Sum a ruleset partition without losing phase-level additivity."""

    phases = PhaseValues(*(math.fsum(row.delta.phases[index] for row in rows) for index in range(len(_RULESET_PHASES))))
    return RulesetDelta(math.fsum(row.delta.total for row in rows), phases)


def _sample_estimate(
    values: list[float],
    issue: str | None,
    t_critical: float | None,
) -> _MetricEstimate:
    mean = statistics.fmean(values) if issue is None and values else None
    var_mean: float | None = None
    ci_low: float | None = None
    ci_high: float | None = None
    if mean is not None and len(values) >= 2:
        var_mean = statistics.variance(values) / len(values)
        if t_critical is None:
            raise ValueError("multi-sample estimate is missing its t critical value")
        half_width = t_critical * math.sqrt(var_mean)
        ci_low = mean - half_width
        ci_high = mean + half_width
    return _MetricEstimate(len(values), Estimate(mean, ci_low, ci_high), var_mean, issue)


def _share(numerator: float | None, denominator: float | None, *, scale: float = 1.0) -> float | None:
    if numerator is None or denominator is None or denominator == 0:
        return None
    return numerator / (denominator * scale)
