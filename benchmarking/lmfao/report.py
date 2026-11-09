"""Execution comparison and separate preparation costs for the LMFAO case study."""

from __future__ import annotations

import json
from typing import Any

from . import model


def preparation_costs(plans: dict[str, Any], builds: dict[str, Any], aliases: dict[str, str]) -> dict[str, Any]:
    result = {}
    for label in ["original", *(["paper"] if "paper" in builds else []), *plans]:
        executed = aliases.get(label, label)
        generation = builds[label]["generation_seconds"]
        compilation = builds[executed]["compilation_seconds"]
        result[label] = {
            "optimization_and_generation_seconds": generation,
            "compilation_seconds": compilation,
            "one_time_phase_sum_seconds": generation + compilation,
            "execution_label": executed,
        }
    return result


def comparison_rows(report: dict[str, Any]) -> list[list[str]]:
    rows = []
    names = {
        "original": "LMFAO configured roots",
        "paper": "LMFAO + paper root heuristic",
        "slotted": "Slotted egglog",
        "debruijn": "Ordinary egglog (de Bruijn)",
    }
    for label, name in names.items():
        optimization = report["optimizer"].get(label, {})
        timing = optimization.get("process_seconds")
        runtime = f"{timing['median_seconds']:.3f}" if timing else "—"
        memory = optimization.get("max_rss_bytes")
        rss = f"{memory / 1024**2:.1f}" if memory is not None else "—"
        if label not in report["accounted_pipeline"]:
            failures = sorted({row["status"] for row in optimization.get("failures", [])})
            reason = (
                ", ".join(failures) or optimization.get("pipeline_issue") or optimization.get("issue") or "unavailable"
            )
            rows.append(
                [
                    f"{name} ({reason})",
                    runtime,
                    rss,
                    "—",
                    "—",
                    "—",
                    "—",
                    f"{optimization.get('completed_samples', 0)} completed, "
                    f"{len(optimization.get('failures', []))} failed",
                ]
            )
            continue
        preparation = report["accounted_pipeline"][label]
        timing = report["execution"][preparation["execution_label"]]["computation_seconds"]
        execution = timing["median_seconds"]
        egraph_samples = optimization.get("completed_samples", "—")
        plan = report["plan_summaries"][label]
        rows.append(
            [
                name,
                runtime,
                rss,
                f"{preparation['optimization_and_generation_seconds']:.3f}",
                f"{preparation['compilation_seconds']:.3f}",
                f"{execution:.4f}",
                f"{plan['views']} / {plan['aggregate_columns']}",
                f"{egraph_samples} egraph / {timing['samples']} execution",
            ]
        )
    return rows


def comparison_caption(report: dict[str, Any]) -> str:
    limit = report["optimizer_memory_limit_bytes"]
    bound = f"{limit / 1024**3:g} GiB allocator/address-space cap" if limit is not None else "no memory cap"
    lines = [
        "The original 140-query Favorita covariance workload on the public 2M-Sales-row fragment, using the "
        "same pinned frontend and corrected C++ backend. This replicates the workload and pipeline, not the "
        "paper's full 127M-row experiment. The paper-heuristic control uses our implementation of its section 3.3 "
        "coverage heuristic; it is distinct from the roots shipped in the artifact.",
        "",
        "Both egraph modes use hoisting, independent-loop interchange and tuple fusion on the same nested bag sums. "
        "Shared views are derived from fused reductions; the same joint DAG extractor selects the plan. "
        f"Both modes have the same {report['rewrite_round_budget']}-round budget and {bound}. "
        "Ordinary egglog uses de Bruijn indices with explicit shift/swap rules. "
        "A resource failure is reported as a failure, never as an execution speedup.",
        "",
        "The sample counts show completed egraph and execution runs; collection stops after a resource failure. "
        "Egraph time and peak RSS are medians of separate optimizer processes, including parsing and rewriting "
        "but excluding extraction. Optimization + generation is one measured preparation run, "
        "including query export, translation, rewriting, DAG extraction and code generation. "
        "C++ compilation is separate. "
        "Computation is the median of warm runs, excluding loading, sorting and checking, as in the paper's "
        "timing scope. Identical selected plans reuse compilation/execution observations, charged in full; "
        "pipeline.json records those aliases, samples, hashes and all output checks.",
    ]
    return "\n".join(lines) + "\n"


def comparison_markdown(report: dict[str, Any]) -> str:
    lines = [
        "| Method | Egraph (s) | Peak RSS (MiB) | Optimization + generation (s) | "
        "C++ compilation (s) | Computation (s) | Views / columns | Samples |",
        "|---|---:|---:|---:|---:|---:|---:|---|",
        *("| " + " | ".join(row) + " |" for row in comparison_rows(report)),
        "",
        comparison_caption(report),
    ]
    return "\n".join(lines)


def paper_results(report: dict[str, Any]) -> dict[str, str]:
    """Format the checked execution table for the shared paper publisher."""
    if not {"original", "paper", "slotted"} <= report["accounted_pipeline"].keys() or any(
        item.get("pipeline_issue") for item in report["optimizer"].values()
    ):
        raise ValueError("LMFAO execution comparison is incomplete; no paper table replaced")
    escapes = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "—": r"\textemdash{}",
    }

    def tex(value: str) -> str:
        return "".join(escapes.get(c, c) for c in value)

    table = [
        "% GENERATED: ./bench.py figures lmfao; provenance in lmfao.results.json",
        r"\begingroup\scriptsize\setlength{\tabcolsep}{3pt}",
        r"\begin{tabular}{lrrrrrrl}",
        r"Method & \shortstack{Egraph\\(s)} & \shortstack{Peak RSS\\(MiB)} & "
        r"\shortstack{Optimize +\\generate (s)} & \shortstack{C++ compile\\(s)} & "
        r"\shortstack{Compute\\(s)} & \shortstack{Views /\\columns} & \shortstack{Samples\\egraph / exec.} \\",
        r"\hline",
    ]
    for row in comparison_rows(report):
        cells = list(map(tex, row))
        cells[0] = r"\shortstack[l]{" + tex(row[0]).replace(" (", r"\\(") + "}"
        cells[-1] = (
            r"\shortstack[l]{"
            + tex(row[-1]).replace(" egraph", "").replace(" execution", "").replace(", ", r"\\")
            + "}"
        )
        table.append(" & ".join(cells) + r" \\")
    table += [r"\end{tabular}", r"\endgroup", ""]
    return {
        "lmfao.table.tex": "\n".join(table),
        "lmfao.caption.tex": tex(" ".join(comparison_caption(report).split())) + "\n",
        "lmfao.md": comparison_markdown(report),
        "lmfao.results.json": json.dumps(report, indent=2, allow_nan=False) + "\n",
    }


def plan_text(plan: dict[str, Any]) -> str:
    """Render selected view equations and query references in serialized ID order."""
    names = [a for a, _ in model.WORKLOAD.attributes]
    tables = list(model.WORKLOAD.relations)
    lines = []
    for i, view in enumerate(plan["views"]):
        keys = ", ".join(names[k] for k in view["keys"])
        columns = []
        for j, aggregate in enumerate(view["aggregates"]):
            factors = [
                name if power == 1 else f"{name}^{power}"
                for f in aggregate["functions"]
                for name, power in [model.WORKLOAD.functions[f]]
            ]
            factors += [f"V{v}.a{a}" for v, a in aggregate["incoming"]]
            inputs = [tables[view["origin"]], *(f"V{v}" for v, _ in aggregate["incoming"])]
            columns.append(f"  a{j} = SUM({' * '.join(factors) or '1'}) FROM {' NATURAL JOIN '.join(inputs)}")
        lines += [f"V{i}[{keys}] ({tables[view['origin']]} -> {tables[view['destination']]}):", *columns, ""]
    for i, output in enumerate(plan["outputs"]):
        query = model.WORKLOAD.queries[i]
        keys, weight = ", ".join(query.groups), " * ".join(query.factors) or "1"
        lines.append(f"q{i}[{keys}] = V{output['view']}.a{output['aggregate']}  # SUM({weight}) over the full join")
    return "\n".join(lines) + "\n"
