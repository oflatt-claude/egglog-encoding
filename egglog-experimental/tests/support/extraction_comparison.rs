//! Shared comparison policy for equal-cost extraction ties and exact variants.
use egglog::CommandOutput;
pub type Extraction = (Option<String>, Vec<String>);

/// Preserve best-term costs and exact ordered variant lists from command outputs.
pub fn observe(outputs: &[CommandOutput]) -> Vec<Extraction> {
    outputs
        .iter()
        .filter_map(|output| match output {
            CommandOutput::ExtractBest(dag, cost, term) => {
                Some((Some(cost.to_string()), vec![dag.to_string(*term)]))
            }
            CommandOutput::ExtractVariants(dag, terms) => Some((
                None,
                terms.iter().map(|&term| dag.to_string(term)).collect(),
            )),
            _ => None,
        })
        .collect()
}

pub fn compare(
    actual: &mut [Extraction],
    expected: &[Extraction],
    root_equality: &[Option<bool>],
    context: &str,
) -> Result<usize, String> {
    if actual.len() != expected.len() || actual.len() != root_equality.len() {
        return Err(format!(
            "{context}: extraction counts differ or an extraction was not intercepted; comparison evidence must match the extraction outputs"
        ));
    }
    let mut ties = 0;
    for (index, ((actual, expected), &equivalent)) in actual
        .iter_mut()
        .zip(expected)
        .zip(root_equality)
        .enumerate()
    {
        if actual == expected {
            continue;
        }
        if actual.0.is_some()
            && actual.0 == expected.0
            && actual.1.len() == 1
            && expected.1.len() == 1
            && equivalent == Some(true)
        {
            eprintln!(
                "Extraction tie: {context}, request {index}, cost {}; verified equal-cost terms at the requested extraction root",
                actual.0.as_ref().unwrap()
            );
            // Normalize only the comparison value. Raw outputs and their exact
            // returned-term certificates remain untouched.
            actual.1.clone_from(&expected.1);
            ties += 1;
        } else {
            return Err(format!(
                "{context}: extraction {index} differs; costs {:?}/{:?}, variant counts {}/{}, verified root equality {equivalent:?}",
                actual.0,
                expected.0,
                actual.1.len(),
                expected.1.len()
            ));
        }
    }
    Ok(ties)
}
