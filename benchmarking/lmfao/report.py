"""Execution comparison and separate preparation costs for the LMFAO case study."""

from __future__ import annotations

from typing import Any


def preparation_costs(plans: dict[str, Any], builds: dict[str, Any], aliases: dict[str, str]) -> dict[str, Any]:
    result = {}
    for label in ["original", *plans]:
        executed = aliases.get(label, label)
        phases = {
            **(plans[label]["phases_seconds"] if label in plans else {}),
            "code_generation": builds[executed]["generation_seconds"],
            "compilation": builds[executed]["compilation_seconds"],
        }
        result[label] = {
            "phases_seconds": phases,
            "statistics_seconds": phases.get("statistics_loading", 0) + phases.get("statistics_queries", 0),
            "optimization_and_generation_seconds": sum(
                seconds
                for phase, seconds in phases.items()
                if phase not in ("statistics_loading", "statistics_queries", "compilation")
            ),
            "compilation_seconds": phases["compilation"],
            "one_time_phase_sum_seconds": sum(phases.values()),
            "execution_label": executed,
        }
    return result


def comparison_markdown(report: dict[str, Any]) -> str:
    lines = [
        "| Variant / engine | Allowed roots | Shared producers | Computation median (s) | Runs |",
        "|---|---|---|---:|---:|",
    ]
    costs = [
        "| Variant / engine | Statistics (s) | Optimization + generation (s) | C++ compilation (s) |",
        "|---|---:|---:|---:|",
    ]
    configurations = {
        "single-root": ("Sales only", "Enabled"),
        "roots": ("All six", "Disabled"),
        "shared": ("All six", "Enabled"),
    }
    for label in ["original", *report["optimizer"]]:
        if label == "original":
            name, roots, sharing = "Original LMFAO", "Original policy", "Original merging"
        else:
            variant, _, engine = label.partition("-slotted")
            name = f"{variant} / {'native multipattern' if engine else 'egglog'}"
            roots, sharing = configurations[variant]
        if label not in report["accounted_pipeline"]:
            lines.append(f"| {name} | {roots} | {sharing} | unavailable | — |")
            costs.append(f"| {name} | — | — | — |")
            continue
        preparation = report["accounted_pipeline"][label]
        timing = report["execution"][preparation["execution_label"]]["computation_seconds"]
        lines.append(f"| {name} | {roots} | {sharing} | {timing['median_seconds']:.4f} | {timing['samples']} |")
        values = [
            preparation[key]
            for key in ("statistics_seconds", "optimization_and_generation_seconds", "compilation_seconds")
        ]
        costs.append(f"| {name} | " + " | ".join(f"{v:.4f}" for v in values) + " |")
    lines.extend(
        [
            "",
            "Table: Execution of the original 140-query Favorita covariance workload through the same corrected "
            "LMFAO C++ backend. Within each egraph engine, compare shared with single-root to isolate the benefit "
            "of root choice, and shared with roots to isolate shared-producer merging. Queries, data, cost model "
            "and backend are fixed across these ablations. All variants retain identical-subexpression reuse and "
            "backend multi-output optimization. Times are medians of warm executions, excluding statistics, "
            "optimization, code generation, compilation, data loading and sorting. This matches the paper's "
            "computation timing scope, but uses medians rather than its means; dataset size and hardware come "
            "from metadata.json. Only selected variants are shown. Unavailable plans are not timing results; "
            "see pipeline.json for failure details. "
            "Identical plans reuse execution observations as recorded by execution_aliases.",
            "",
            "Preparation costs are separate observations, one per phase:",
            "",
            *costs,
            "",
            "Statistics includes loading the data used for cardinality collection. Optimization + generation "
            "includes rewriting/export, decoding, extraction, serialization and C++ generation; original LMFAO's "
            "logical optimization is included in generation. Independent correctness checks are excluded for both. "
            "Whole-process execution, including loading and sorting, remains in pipeline.json.",
            "",
            "For N executions of a reused plan, the estimated cost is statistics + optimization/generation + "
            "compilation + N × execution. This is an amortization model, not a measured end-to-end runtime; "
            "state whether execution includes loading and sorting. Recollecting statistics or recompiling "
            "incurs those costs again.",
        ]
    )
    return "\n".join(lines) + "\n"
