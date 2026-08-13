use clap::clap_derive::ValueEnum;
use rustc_hash::FxHasher;
use serde::Serialize;
use std::{
    fmt::{Display, Formatter},
    hash::BuildHasherDefault,
    sync::Arc,
};
use web_time::Duration;

pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;

#[derive(ValueEnum, Default, Serialize, Debug, Clone, Copy)]
pub enum ReportLevel {
    /// Report pre-merge, merge, and rebuild time.
    ///
    /// Pre-merge time is split into search, apply, and unattributed time when
    /// execution can attribute those phases without overlap.
    #[default]
    TimeOnly,
    /// Report [`ReportLevel::TimeOnly`] and query plan for each rule
    WithPlan,
    /// Report [`ReportLevel::WithPlan`] and the detailed statistics at each stage of the query plan.
    StageInfo,
}

#[derive(Serialize, Clone, Debug)]
pub struct SingleScan(pub String, pub (String, i64));
#[derive(Serialize, Clone, Debug)]
pub struct Scan(pub String, pub Vec<(String, i64)>);

#[derive(Serialize, Clone, Debug)]
pub enum Stage {
    Intersect {
        scans: Vec<SingleScan>,
    },
    FusedIntersect {
        cover: Scan,             // build side
        to_intersect: Vec<Scan>, // probe sides
    },
}

#[derive(Serialize, Clone, Debug)]
pub struct StageStats {
    pub num_candidates: usize,
    pub num_succeeded: usize,
}

#[derive(Serialize, Clone, Debug, Default)]
pub struct Plan {
    pub stages: Vec<(
        Stage,
        Option<StageStats>,
        // indices of next stages
        Vec<usize>,
    )>,
}

#[derive(Debug, Serialize, Clone, Default)]
pub struct RuleReport {
    pub plan: Option<Plan>,
    pub search_and_apply_time: Duration,
    // TODO: succeeding matches
    pub num_matches: usize,
}

#[derive(Debug, Serialize, Clone, Default)]
pub struct RuleSetReport {
    pub changed: bool,
    pub rule_reports: HashMap<Arc<str>, Vec<RuleReport>>,
    /// Timed work before staged updates are merged, either as one elapsed
    /// duration or as an exhaustive serial phase breakdown.
    pub pre_merge: PreMergeTiming,
    pub merge_time: Duration,
}

/// Timing for work before staged updates are merged.
///
/// Parallel execution reports one wall-clock duration because search and apply
/// can overlap. Serial execution reports an additive phase breakdown and
/// derives `unattributed` so the components close its measured outer interval.
#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
pub enum PreMergeTiming {
    /// One wall-clock duration for execution modes whose search and apply work
    /// can overlap.
    Combined { elapsed: Duration },
    /// Non-overlapping components of serial pre-merge timing.
    Split {
        search: Duration,
        apply: Duration,
        /// Remainder of a measured outer pre-merge interval after search and
        /// apply.
        unattributed: Duration,
    },
}

impl Default for PreMergeTiming {
    fn default() -> Self {
        Self::Combined {
            elapsed: Duration::ZERO,
        }
    }
}

impl PreMergeTiming {
    pub fn total(self) -> Duration {
        match self {
            Self::Combined { elapsed } => elapsed,
            Self::Split {
                search,
                apply,
                unattributed,
            } => search + apply + unattributed,
        }
    }

    fn union(&mut self, other: Self) {
        *self = match (*self, other) {
            (
                Self::Split {
                    search: left_search,
                    apply: left_apply,
                    unattributed: left_unattributed,
                },
                Self::Split {
                    search: right_search,
                    apply: right_apply,
                    unattributed: right_unattributed,
                },
            ) => Self::Split {
                search: left_search + right_search,
                apply: left_apply + right_apply,
                unattributed: left_unattributed + right_unattributed,
            },
            (left, right) => Self::Combined {
                elapsed: left.total() + right.total(),
            },
        };
    }
}

/// Aggregated timing for all iterations of one ruleset.
#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq, Default)]
pub struct RulesetTiming {
    /// Building the executable ruleset for each invocation, including lazy
    /// cached-plan creation on first use.
    pub assembly: Duration,
    /// Execution before staged updates are merged.
    pub pre_merge: PreMergeTiming,
    /// Resolving and installing staged updates.
    pub merge: Duration,
    /// Rebuilding indexes and e-graph state after merge.
    pub rebuild: Duration,
}

impl RulesetTiming {
    pub fn total(self) -> Duration {
        self.assembly + self.pre_merge.total() + self.merge + self.rebuild
    }

    fn union(&mut self, other: Self) {
        self.assembly += other.assembly;
        self.pre_merge.union(other.pre_merge);
        self.merge += other.merge;
        self.rebuild += other.rebuild;
    }
}

impl RuleSetReport {
    pub fn num_matches(&self, rule: &str) -> usize {
        self.rule_reports
            .get(rule)
            .map(|r| r.iter().map(|r| r.num_matches).sum())
            .unwrap_or(0)
    }

    pub fn rule_search_and_apply_time(&self, rule: &str) -> Duration {
        self.rule_reports
            .get(rule)
            .map(|r| r.iter().map(|r| r.search_and_apply_time).sum())
            .unwrap_or(Duration::ZERO)
    }
}

#[derive(Debug, Serialize, Clone, Default)]
pub struct IterationReport {
    /// Preparing this invocation's executable ruleset before execution starts.
    pub assembly_time: Duration,
    pub rule_set_report: RuleSetReport,
    pub rebuild_time: Duration,
}

impl IterationReport {
    pub fn changed(&self) -> bool {
        self.rule_set_report.changed
    }

    pub fn rule_reports(&self) -> &HashMap<Arc<str>, Vec<RuleReport>> {
        &self.rule_set_report.rule_reports
    }

    pub fn rules(&self) -> impl Iterator<Item = &Arc<str>> {
        self.rule_set_report.rule_reports.keys()
    }

    /// Total exclusive wall-clock work recorded for this invocation.
    pub fn total_time(&self) -> Duration {
        self.assembly_time
            + self.rule_set_report.pre_merge.total()
            + self.rule_set_report.merge_time
            + self.rebuild_time
    }
}

/// Running a schedule produces a report of the results.
/// This includes rough timing information and whether
/// the database was updated.
/// Calling `union` on two run reports adds the timing
/// information together.
#[derive(Debug, Serialize, Clone)]
pub struct RunReport {
    // Since `IterationReport`s are immutable, we can reference count them to avoid
    // expensive cloning when e-graphs are cloned.
    pub iterations: Vec<Arc<IterationReport>>,
    /// If any changes were made to the database.
    pub updated: bool,
    /// True if this run observed no database changes and there is no deferred
    /// scheduler work requiring another iteration.
    pub can_stop: bool,
    pub search_and_apply_time_per_rule: HashMap<Arc<str>, Duration>,
    pub num_matches_per_rule: HashMap<Arc<str>, usize>,
    pub ruleset_timings: HashMap<Arc<str>, RulesetTiming>,
}

impl Default for RunReport {
    fn default() -> Self {
        Self {
            iterations: Vec::new(),
            updated: false,
            can_stop: true,
            search_and_apply_time_per_rule: HashMap::default(),
            num_matches_per_rule: HashMap::default(),
            ruleset_timings: HashMap::default(),
        }
    }
}

impl Display for RunReport {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut rule_times_vec: Vec<_> = self.search_and_apply_time_per_rule.iter().collect();
        rule_times_vec.sort_by_key(|(_, time)| **time);

        for (rule, time) in rule_times_vec {
            let name = Self::truncate_rule_name(rule.to_string());
            let time = time.as_secs_f64();
            let num_matches = self.num_matches_per_rule.get(rule).copied().unwrap_or(0);
            writeln!(
                f,
                "Rule {name}: search and apply {time:.3}s, num matches {num_matches}",
            )?;
        }

        for (ruleset, timing) in &self.ruleset_timings {
            let assembly_time = timing.assembly.as_secs_f64();
            let merge_time = timing.merge.as_secs_f64();
            let rebuild_time = timing.rebuild.as_secs_f64();
            match timing.pre_merge {
                PreMergeTiming::Split {
                    search,
                    apply,
                    unattributed,
                } => {
                    writeln!(
                        f,
                        "Ruleset {ruleset}: assembly {assembly_time:.3}s, search {:.3}s, apply {:.3}s, unattributed {:.3}s, merge {merge_time:.3}s, rebuild {rebuild_time:.3}s",
                        search.as_secs_f64(),
                        apply.as_secs_f64(),
                        unattributed.as_secs_f64(),
                    )?;
                }
                PreMergeTiming::Combined { elapsed } => {
                    writeln!(
                        f,
                        "Ruleset {ruleset}: assembly {assembly_time:.3}s, pre-merge {:.3}s, merge {merge_time:.3}s, rebuild {rebuild_time:.3}s",
                        elapsed.as_secs_f64(),
                    )?;
                }
            }
        }

        Ok(())
    }
}

impl RunReport {
    /// add a ... and a maximum size to the name
    /// for printing, since they may be the rule itself
    fn truncate_rule_name(mut s: String) -> String {
        // replace newlines in s with a space
        s = s.replace('\n', " ");
        if s.len() > 80 {
            s.truncate(80);
            s.push_str("...");
        }
        s
    }

    fn union_times(
        times: &mut HashMap<Arc<str>, Duration>,
        other_times: HashMap<Arc<str>, Duration>,
    ) {
        for (k, v) in other_times {
            *times.entry(k).or_default() += v;
        }
    }

    fn union_counts(counts: &mut HashMap<Arc<str>, usize>, other_counts: HashMap<Arc<str>, usize>) {
        for (k, v) in other_counts {
            *counts.entry(k).or_default() += v;
        }
    }

    pub fn singleton(ruleset: &str, iteration: IterationReport) -> Self {
        let mut report = RunReport::default();

        for rule in iteration.rules() {
            *report
                .search_and_apply_time_per_rule
                .entry(rule.clone())
                .or_default() += iteration.rule_set_report.rule_search_and_apply_time(rule);
            *report.num_matches_per_rule.entry(rule.clone()).or_default() +=
                iteration.rule_set_report.num_matches(rule);
        }

        let ruleset: Arc<str> = ruleset.into();
        report.ruleset_timings.insert(
            ruleset,
            RulesetTiming {
                assembly: iteration.assembly_time,
                pre_merge: iteration.rule_set_report.pre_merge,
                merge: iteration.rule_set_report.merge_time,
                rebuild: iteration.rebuild_time,
            },
        );
        report.updated = iteration.changed();
        report.can_stop = !report.updated;
        report.iterations.push(Arc::new(iteration));

        report
    }

    pub fn add_iteration(&mut self, ruleset: &str, iteration: IterationReport) {
        self.union(RunReport::singleton(ruleset, iteration));
    }

    /// Total wall-clock work recorded by all ruleset phase timers.
    pub fn total_ruleset_time(&self) -> Duration {
        self.ruleset_timings
            .values()
            .copied()
            .map(RulesetTiming::total)
            .sum()
    }

    /// Merge two reports.
    pub fn union(&mut self, other: Self) {
        self.iterations.extend(other.iterations);
        self.updated |= other.updated;
        self.can_stop &= other.can_stop;
        RunReport::union_times(
            &mut self.search_and_apply_time_per_rule,
            other.search_and_apply_time_per_rule,
        );
        RunReport::union_counts(&mut self.num_matches_per_rule, other.num_matches_per_rule);
        for (ruleset, timing) in other.ruleset_timings {
            self.ruleset_timings
                .entry(ruleset)
                .and_modify(|current| current.union(timing))
                .or_insert(timing);
        }
    }
}

/// One exclusive timing leaf in the benchmark transport.
///
/// Static mechanism and phase names occupy the first two segments. Ruleset
/// leaves add the exact ruleset name as a third segment. Segments are stored
/// separately so user names containing `/` remain unambiguous.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimingLeafV3 {
    pub path: Vec<String>,
    pub ns: u64,
}

/// Versioned, deterministic timing transport for successful egglog runs.
///
/// The values are exclusive wall-clock leaves: their sum can be subtracted
/// once from process wall time to derive residual. Parent totals are never
/// stored. Construction sorts paths lexicographically, rejects duplicate paths
/// as a producer bug, saturates nanoseconds at [`u64::MAX`], and never
/// truncates the leaf list.
#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct TimingSummaryV3 {
    pub schema_version: u32,
    pub timings: Vec<TimingLeafV3>,
}

/// A requested timing summary contains a ruleset whose split phase timing was
/// not recorded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhaseTimingUnavailable {
    pub ruleset: String,
}

impl Display for PhaseTimingUnavailable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "split pre-merge timing is unavailable for ruleset {ruleset:?}",
            ruleset = self.ruleset,
        )
    }
}

impl std::error::Error for PhaseTimingUnavailable {}

impl TimingSummaryV3 {
    pub fn new(timings: impl IntoIterator<Item = (Vec<String>, Duration)>) -> Self {
        let mut timings = timings
            .into_iter()
            .map(|(path, duration)| TimingLeafV3 {
                path,
                ns: duration_ns(duration),
            })
            .collect::<Vec<_>>();
        assert!(
            timings.iter().all(|timing| !timing.path.is_empty()),
            "timing paths must not be empty"
        );
        timings.sort_unstable_by(|left, right| left.path.cmp(&right.path));
        assert!(
            timings.windows(2).all(|pair| pair[0].path != pair[1].path),
            "duplicate timing path"
        );

        Self {
            schema_version: 3,
            timings,
        }
    }
}

fn duration_ns(duration: Duration) -> u64 {
    duration.as_nanos().min(u64::MAX as u128) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    fn split(search: u64, apply: u64, unattributed: u64) -> PreMergeTiming {
        PreMergeTiming::Split {
            search: Duration::from_nanos(search),
            apply: Duration::from_nanos(apply),
            unattributed: Duration::from_nanos(unattributed),
        }
    }

    #[test]
    fn timing_summary_v3_exact_json_is_sorted_and_segmented() {
        let summary = TimingSummaryV3::new([
            (
                vec!["program".into(), "search".into(), "rules/λ".into()],
                Duration::new(1, 234),
            ),
            (
                vec!["commands".into(), "check".into()],
                Duration::from_nanos(6),
            ),
            (
                vec!["equality".into(), "rebuild".into(), "rules/λ".into()],
                Duration::from_nanos(67),
            ),
            (
                vec!["frontend".into(), "parse".into()],
                Duration::from_nanos(1),
            ),
            (
                vec!["typecheck".into(), "total".into()],
                Duration::from_nanos(2),
            ),
        ]);
        let json = serde_json::to_string(&summary).unwrap();

        assert_eq!(
            json,
            r#"{"schema_version":3,"timings":[{"path":["commands","check"],"ns":6},{"path":["equality","rebuild","rules/λ"],"ns":67},{"path":["frontend","parse"],"ns":1},{"path":["program","search","rules/λ"],"ns":1000000234},{"path":["typecheck","total"],"ns":2}]}"#
        );
    }

    #[test]
    fn timing_summary_v3_empty_report_golden() {
        let summary = TimingSummaryV3::new([]);
        let json = serde_json::to_string(&summary).unwrap();

        assert_eq!(json, r#"{"schema_version":3,"timings":[]}"#);
    }

    #[test]
    #[should_panic(expected = "timing paths must not be empty")]
    fn timing_summary_v3_rejects_an_empty_path() {
        TimingSummaryV3::new([(vec![], Duration::ZERO)]);
    }

    #[test]
    fn run_report_aggregates_every_iteration_of_a_ruleset() {
        let mut report = RunReport::default();
        report.add_iteration(
            "timed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    pre_merge: split(11, 7, 3),
                    merge_time: Duration::from_nanos(13),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(17),
                assembly_time: Duration::from_nanos(2),
            },
        );
        report.add_iteration(
            "timed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    pre_merge: split(19, 5, 4),
                    merge_time: Duration::from_nanos(23),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(29),
                assembly_time: Duration::from_nanos(3),
            },
        );

        assert_eq!(
            report.ruleset_timings["timed"].pre_merge.total(),
            Duration::from_nanos(49)
        );
        assert_eq!(
            report.ruleset_timings["timed"].total(),
            Duration::from_nanos(136)
        );
    }

    #[test]
    fn timing_summary_v3_does_not_truncate_leaves() {
        let summary = TimingSummaryV3::new((0..40).rev().map(|index| {
            (
                vec![
                    "program".into(),
                    "search".into(),
                    format!("ruleset-{index:02}"),
                ],
                Duration::from_nanos(index + 1),
            )
        }));

        assert_eq!(summary.timings.len(), 40);
        assert_eq!(summary.timings.first().unwrap().path[2], "ruleset-00");
        assert_eq!(summary.timings.last().unwrap().path[2], "ruleset-39");
    }

    #[test]
    fn timing_summary_v3_saturates_nanoseconds_to_u64() {
        let summary = TimingSummaryV3::new([(
            vec!["program".into(), "search".into(), "long".into()],
            Duration::from_secs(u64::MAX),
        )]);

        assert_eq!(summary.timings[0].ns, u64::MAX);
    }

    #[test]
    #[should_panic(expected = "duplicate timing path")]
    fn timing_summary_v3_rejects_duplicate_paths() {
        TimingSummaryV3::new([
            (vec!["commands".into(), "check".into()], Duration::ZERO),
            (vec!["commands".into(), "check".into()], Duration::ZERO),
        ]);
    }

    #[test]
    fn combined_iteration_degrades_aggregated_pre_merge_timing() {
        let mut report = RunReport::default();
        report.add_iteration(
            "mixed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    pre_merge: split(1, 2, 3),
                    merge_time: Duration::from_nanos(7),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(11),
                assembly_time: Duration::from_nanos(2),
            },
        );
        report.add_iteration(
            "mixed",
            IterationReport {
                rule_set_report: RuleSetReport {
                    pre_merge: PreMergeTiming::Combined {
                        elapsed: Duration::from_nanos(5),
                    },
                    merge_time: Duration::from_nanos(13),
                    ..RuleSetReport::default()
                },
                rebuild_time: Duration::from_nanos(17),
                assembly_time: Duration::from_nanos(3),
            },
        );

        assert_eq!(
            report.ruleset_timings["mixed"],
            RulesetTiming {
                assembly: Duration::from_nanos(5),
                pre_merge: PreMergeTiming::Combined {
                    elapsed: Duration::from_nanos(11),
                },
                merge: Duration::from_nanos(20),
                rebuild: Duration::from_nanos(28),
            }
        );
        assert_eq!(
            report.ruleset_timings["mixed"].total(),
            Duration::from_nanos(64)
        );
    }
}
