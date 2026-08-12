//! Minimal current-egg runner for the PLDI 2023 Math workload.

use anyhow::{Context, Result, ensure};
use egg::{RecExpr, Runner, SimpleScheduler, StopReason};
use egglog_reports::{RulesetTimingV2, TimingSummaryV2};
use std::{fs::File, io::BufWriter, path::Path, time::Duration};

mod math;

pub use math::Math;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ProofMode {
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

#[derive(Clone, Debug, PartialEq)]
pub struct MathRun {
    pub iterations: usize,
    pub nodes: usize,
    pub classes: usize,
    pub timing: TimingSummaryV2,
}

pub fn run_math(
    iterations: usize,
    check_left: &str,
    check_right: &str,
    proof_mode: ProofMode,
) -> Result<MathRun> {
    ensure!(iterations > 0, "--iterations must be greater than zero");

    let left = parse_expr("--check-left", check_left)?;
    let right = parse_expr("--check-right", check_right)?;
    let rules = math::rules();
    let mut runner = Runner::default()
        .with_scheduler(SimpleScheduler)
        .with_iter_limit(iterations)
        .with_node_limit(usize::MAX)
        .with_time_limit(Duration::MAX);
    if proof_mode.records_proofs() {
        runner = runner.with_explanations_enabled();
    }
    for start in math::start_expressions() {
        runner = runner.with_expr(&parse_expr("Math seed", start)?);
    }
    runner = runner.run(&rules);

    let report = runner.report();
    ensure!(
        report.iterations == iterations,
        "egg stopped after {} of {iterations} required iterations: {:?}",
        report.iterations,
        report.stop_reason
    );
    ensure!(
        matches!(report.stop_reason, StopReason::IterationLimit(limit) if limit == iterations),
        "egg did not stop at the requested iteration limit: {:?}",
        report.stop_reason
    );

    let left_id = runner.egraph.lookup_expr(&left).with_context(|| {
        format!("left check expression is absent after {iterations} iterations")
    })?;
    let right_id = runner.egraph.lookup_expr(&right).with_context(|| {
        format!("right check expression is absent after {iterations} iterations")
    })?;
    ensure!(
        runner.egraph.find(left_id) == runner.egraph.find(right_id),
        "terminal equality is not established after {iterations} iterations"
    );

    if matches!(proof_mode, ProofMode::Extract | ProofMode::Check) {
        let mut explanation = runner.explain_equivalence(&left, &right);
        explanation.make_flat_explanation();
        if proof_mode == ProofMode::Check {
            explanation.check_proof(&rules);
        }
    }

    Ok(MathRun {
        iterations: report.iterations,
        nodes: report.egraph_nodes,
        classes: report.egraph_classes,
        timing: TimingSummaryV2 {
            schema_version: 2,
            rulesets: vec![RulesetTimingV2 {
                name: String::new(),
                search_ns: seconds_to_ns(report.search_time),
                apply_ns: seconds_to_ns(report.apply_time),
                unattributed_ns: seconds_to_ns(
                    (report.total_time
                        - report.search_time
                        - report.apply_time
                        - report.rebuild_time)
                        .max(0.0),
                ),
                merge_ns: 0,
                rebuild_ns: seconds_to_ns(report.rebuild_time),
            }],
        },
    })
}

pub fn write_timing_summary(path: &Path, timing: &TimingSummaryV2) -> Result<()> {
    let file = File::create(path)
        .with_context(|| format!("failed to create timing summary {}", path.display()))?;
    serde_json::to_writer(BufWriter::new(file), timing)
        .with_context(|| format!("failed to write timing summary {}", path.display()))
}

fn parse_expr(label: &str, source: &str) -> Result<RecExpr<Math>> {
    source
        .parse()
        .with_context(|| format!("failed to parse {label} expression {source:?}"))
}

fn seconds_to_ns(seconds: f64) -> u64 {
    if !seconds.is_finite() || seconds <= 0.0 {
        return 0;
    }
    (seconds * 1_000_000_000.0).min(u64::MAX as f64) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATION_ELEVEN_LEFT: &str = "(+ (cos x) (cos x))";
    const ITERATION_ELEVEN_RIGHT: &str = "(d x (+ (sin x) (sin x)))";

    #[test]
    fn runs_one_iteration_and_checks_a_new_equivalence() {
        let result = run_math(1, "(+ x (cos x))", "(+ (cos x) x)", ProofMode::Check).unwrap();
        assert_eq!(result.iterations, 1);
        assert!(result.nodes > result.classes);
    }

    #[test]
    fn rejects_a_check_that_is_not_yet_true() {
        let error = run_math(1, "(i (ln x) x)", "x", ProofMode::Off).unwrap_err();
        assert!(error.to_string().contains("terminal equality"));
    }

    #[test]
    fn terminal_equality_requires_iteration_eleven() {
        let error = run_math(
            10,
            ITERATION_ELEVEN_LEFT,
            ITERATION_ELEVEN_RIGHT,
            ProofMode::Off,
        )
        .unwrap_err();
        assert!(error.to_string().contains("terminal equality"));

        let result = run_math(
            11,
            ITERATION_ELEVEN_LEFT,
            ITERATION_ELEVEN_RIGHT,
            ProofMode::Check,
        )
        .unwrap();
        assert_eq!(result.iterations, 11);
    }
}
