//! The paper's explicit normalization policy for verified extraction ties.
pub type Extraction = (Option<String>, Vec<String>);

pub fn compare(
    actual: &mut [Extraction],
    expected: &[Extraction],
    root_equality: &[Option<bool>],
    context: &str,
) -> Result<usize, String> {
    if actual.len() != expected.len() || actual.len() != root_equality.len() {
        return Err(format!(
            "{context}: extraction counts differ or an extraction was not intercepted; paper inputs must expose each extraction at top level"
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
