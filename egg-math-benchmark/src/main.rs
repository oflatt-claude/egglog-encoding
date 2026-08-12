use anyhow::{Context, Result, ensure};
use clap::{Parser, ValueEnum};
use egg::{RecExpr, Runner, SimpleScheduler, StopReason};
use egglog_reports::{RulesetTimingV2, TimingSummaryV2};
use std::{
    fs::File,
    io::BufWriter,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

mod math;

use math::Math;

const ITERATIONS: usize = 11;
const CHECK_LEFT: &str = "(+ (cos x) (cos x))";
const CHECK_RIGHT: &str = "(d x (+ (sin x) (sin x)))";

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
enum ProofMode {
    #[default]
    Off,
    Enabled,
    Extract,
    Check,
}

impl ProofMode {
    fn records_proofs(self) -> bool {
        self != Self::Off
    }
}

#[derive(Debug, Parser)]
#[command(about = "Run the fixed PLDI 2023 Math workload with current egg")]
struct Args {
    #[arg(long, value_enum, default_value_t)]
    proof_mode: ProofMode,
    #[arg(long)]
    timing_summary: Option<PathBuf>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let timing = run_math(args.proof_mode)?;
    if let Some(path) = args.timing_summary {
        write_timing_summary(&path, &timing)?;
    }
    Ok(())
}

fn run_math(proof_mode: ProofMode) -> Result<TimingSummaryV2> {
    let left: RecExpr<Math> = CHECK_LEFT.parse().expect("fixed left check must parse");
    let right: RecExpr<Math> = CHECK_RIGHT.parse().expect("fixed right check must parse");
    let rules = math::rules();
    let mut runner = Runner::default()
        .with_scheduler(SimpleScheduler)
        .with_iter_limit(ITERATIONS)
        .with_node_limit(usize::MAX)
        .with_time_limit(Duration::MAX);
    if proof_mode.records_proofs() {
        runner = runner.with_explanations_enabled();
    }
    for start in math::start_expressions() {
        let expression = start.parse().expect("fixed Math seed must parse");
        runner = runner.with_expr(&expression);
    }
    runner = runner.run(&rules);

    let report = runner.report();
    ensure!(
        report.iterations == ITERATIONS,
        "egg stopped after {} of {ITERATIONS} required iterations: {:?}",
        report.iterations,
        report.stop_reason
    );
    ensure!(
        matches!(report.stop_reason, StopReason::IterationLimit(limit) if limit == ITERATIONS),
        "egg did not stop at the requested iteration limit: {:?}",
        report.stop_reason
    );

    let left_id = runner
        .egraph
        .lookup_expr(&left)
        .context("fixed left check expression is absent after iteration 11")?;
    let right_id = runner
        .egraph
        .lookup_expr(&right)
        .context("fixed right check expression is absent after iteration 11")?;
    ensure!(
        runner.egraph.find(left_id) == runner.egraph.find(right_id),
        "terminal equality is not established after iteration 11"
    );

    let proof_postprocessing_started = Instant::now();
    let proof_postprocessing_ns = if matches!(proof_mode, ProofMode::Extract | ProofMode::Check) {
        let mut explanation = runner.explain_equivalence(&left, &right);
        explanation.make_flat_explanation();
        if proof_mode == ProofMode::Check {
            explanation.check_proof(&rules);
        }
        duration_to_ns(proof_postprocessing_started.elapsed())
    } else {
        0
    };

    Ok(TimingSummaryV2 {
        schema_version: 2,
        rulesets: vec![RulesetTimingV2 {
            name: String::new(),
            search_ns: seconds_to_ns(report.search_time),
            apply_ns: seconds_to_ns(report.apply_time),
            unattributed_ns: seconds_to_ns(
                (report.total_time - report.search_time - report.apply_time - report.rebuild_time)
                    .max(0.0),
            )
            .saturating_add(proof_postprocessing_ns),
            merge_ns: 0,
            rebuild_ns: seconds_to_ns(report.rebuild_time),
        }],
    })
}

fn write_timing_summary(path: &Path, timing: &TimingSummaryV2) -> Result<()> {
    let file = File::create(path)
        .with_context(|| format!("failed to create timing summary {}", path.display()))?;
    serde_json::to_writer(BufWriter::new(file), timing)
        .with_context(|| format!("failed to write timing summary {}", path.display()))
}

fn seconds_to_ns(seconds: f64) -> u64 {
    if !seconds.is_finite() || seconds <= 0.0 {
        return 0;
    }
    (seconds * 1_000_000_000.0).min(u64::MAX as f64) as u64
}

fn duration_to_ns(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_math_workload_runs_and_checks_at_iteration_eleven() {
        run_math(ProofMode::Check).unwrap();
    }
}
