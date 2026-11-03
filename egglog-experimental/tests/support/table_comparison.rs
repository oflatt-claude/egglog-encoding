//! Exact source-table parity, including narrowly recorded expected failures.
use std::collections::{BTreeMap, BTreeSet};

pub fn compare(
    actual: &BTreeMap<String, usize>,
    baseline: &BTreeMap<String, usize>,
    expected_failure: Option<&BTreeMap<String, (usize, usize)>>,
) -> Result<bool, String> {
    let names: BTreeSet<_> = baseline.keys().chain(actual.keys()).collect();
    let differences: BTreeMap<_, _> = names
        .into_iter()
        .filter_map(|name| {
            let counts = (baseline.get(name).copied(), actual.get(name).copied());
            (counts.0 != counts.1).then(|| (name.clone(), counts))
        })
        .collect();
    if let Some(expected) = expected_failure {
        if differences.is_empty() {
            return Err("XPASS: the recorded table-size failure no longer reproduces; remove its annotation".into());
        }
        let expected: BTreeMap<_, _> = expected
            .iter()
            .map(|(name, &(baseline, actual))| (name.clone(), (Some(baseline), Some(actual))))
            .collect();
        if differences != expected {
            return Err(format!(
                "unexpected table-size failure: {differences:?}; recorded failure: {expected:?}"
            ));
        }
        Ok(true)
    } else if differences.is_empty() {
        Ok(false)
    } else {
        Err(format!(
            "source-visible table sizes differ: {differences:?}"
        ))
    }
}
