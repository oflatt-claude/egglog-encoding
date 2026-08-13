//! Exclusive wall-clock accounting outside ruleset execution.
//!
//! Static slices make paths the recording structure without allocating at
//! timer sites. The persisted summary converts them to owned path segments.

use std::time::Duration;

use indexmap::IndexMap;

pub(crate) type TimingPath = &'static [&'static str];

pub(crate) const TYPECHECK: TimingPath = &["typecheck", "total"];
pub(crate) const FRONTEND_PARSE: TimingPath = &["frontend", "parse"];
pub(crate) const FRONTEND_OTHER: TimingPath = &["frontend", "other"];
pub(crate) const FRONTEND_INSTALL: TimingPath = &["frontend", "install"];
pub(crate) const COMMANDS_ACTIONS: TimingPath = &["commands", "actions"];
pub(crate) const COMMANDS_CHECK: TimingPath = &["commands", "check"];
pub(crate) const COMMANDS_OTHER: TimingPath = &["commands", "other"];

const STABLE_PROCESS_PATHS: [TimingPath; 7] = [
    TYPECHECK,
    FRONTEND_PARSE,
    FRONTEND_OTHER,
    FRONTEND_INSTALL,
    COMMANDS_ACTIONS,
    COMMANDS_CHECK,
    COMMANDS_OTHER,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RulesetTimingRole {
    Program,
    EqualityMaintenance,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PhaseTimings {
    pub(crate) leaves: IndexMap<TimingPath, Duration>,
}

impl Default for PhaseTimings {
    fn default() -> Self {
        Self {
            leaves: STABLE_PROCESS_PATHS
                .into_iter()
                .map(|path| (path, Duration::ZERO))
                .collect(),
        }
    }
}

impl PhaseTimings {
    /// Accumulate one exclusive interval under exactly one path.
    pub(crate) fn add(&mut self, path: TimingPath, duration: Duration) {
        assert!(!path.is_empty(), "timing paths must not be empty");
        *self.leaves.entry(path).or_default() += duration;
    }

    pub(crate) fn total(&self) -> Duration {
        self.leaves.values().copied().sum()
    }

    pub(crate) fn timing_leaves(&self) -> Vec<(Vec<String>, Duration)> {
        self.leaves
            .iter()
            .map(|(path, duration)| {
                (
                    path.iter().map(|segment| (*segment).to_owned()).collect(),
                    *duration,
                )
            })
            .collect()
    }
}
