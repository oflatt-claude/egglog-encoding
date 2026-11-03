//! Small guards for the instrumentation used on the full paper inputs.
use egglog::CommandOutput;
use egglog_experimental::*;
#[path = "support/extraction.rs"]
mod extraction;
#[path = "support/extraction_comparison.rs"]
mod extraction_comparison;
#[path = "support/paper_oracles.rs"]
mod paper_oracles;
#[path = "support/table_comparison.rs"]
mod table_comparison;

#[test]
fn paper_registration_rejects_unmapped_oracles_and_missing_companions() {
    use std::path::Path;
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let slotted = root.join("benchmarks/slotted/inputs/sdql/batax_1st-44rules.egg");
    for (file, mode, valid) in [
        (&slotted, "slotted", true),
        (&slotted, "off", false),
        (
            &root.join("benchmarks/corpus/math/math-iteration-12.egg"),
            "egg-proof-testing",
            true,
        ),
        (
            &root.join("benchmarks/corpus/math/math-iteration-12.egg"),
            "slotted",
            false,
        ),
        (
            &root.join("benchmarks/disequality/parameter-analysis.egg"),
            "egg-nee",
            true,
        ),
        (&slotted, "unknown", false),
    ] {
        let modes = [mode.to_owned()].into_iter().collect();
        let result = paper_oracles::validate(root, file, &modes);
        if valid {
            result.unwrap();
        } else {
            assert!(result.unwrap_err().contains("unmapped paper oracle"));
        }
    }
    let mixed = ["slotted", "off"].map(str::to_owned).into_iter().collect();
    assert!(
        paper_oracles::validate(root, &slotted, &mixed)
            .unwrap_err()
            .contains("unmapped paper oracle")
    );
    let temporary = tempfile::tempdir().unwrap();
    for (relative, mode, extension) in [
        ("benchmarks/slotted/inputs/case.egg", "slotted", "ref"),
        (
            "benchmarks/disequality/parameter-analysis.egg",
            "egg-nee",
            "in",
        ),
    ] {
        let file = temporary.path().join(relative);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(&file, "").unwrap();
        let modes = [mode.to_owned()].into_iter().collect();
        let error = paper_oracles::validate(temporary.path(), &file, &modes).unwrap_err();
        assert!(error.contains("missing physical paper input"));
        assert!(error.ends_with(extension));
        std::fs::write(file.with_extension(extension), "").unwrap();
        paper_oracles::validate(temporary.path(), &file, &modes).unwrap();
    }
}

#[test]
fn table_xfail_accepts_only_the_recorded_bug_and_rejects_xpass() {
    use std::collections::BTreeMap;
    let baseline = BTreeMap::from([("Smaller".into(), 777), ("Other".into(), 1)]);
    let expected = BTreeMap::from([("Smaller".into(), (777, 785))]);
    let mut actual = baseline.clone();
    assert_eq!(
        table_comparison::compare(&actual, &baseline, None),
        Ok(false)
    );
    assert!(
        table_comparison::compare(&actual, &baseline, Some(&expected))
            .unwrap_err()
            .contains("XPASS")
    );
    actual.insert("Smaller".into(), 785);
    assert!(table_comparison::compare(&actual, &baseline, None).is_err());
    assert_eq!(
        table_comparison::compare(&actual, &baseline, Some(&expected)),
        Ok(true)
    );
    actual.insert("Other".into(), 2);
    assert!(table_comparison::compare(&actual, &baseline, Some(&expected)).is_err());
    actual.remove("Other");
    assert!(table_comparison::compare(&actual, &baseline, Some(&expected)).is_err());
    actual = baseline.clone();
    actual.insert("Smaller".into(), 786);
    assert!(table_comparison::compare(&actual, &baseline, Some(&expected)).is_err());
}

#[test]
fn literal_terms_variants_and_source_root_certificates_survive_encoding() {
    let source = r#"
        (datatype T (I i64) (S String) (F f64) (B bool))
        (let integer (I -3))
        (let text (S "quote \" and λ"))
        (let floating (F 3.5))
        (let boolean (B true))
        (extract integer)
        (extract text)
        (extract floating)
        (extract boolean)
        (extract integer 3)
    "#;
    let mut expected = None;
    for (mut graph, strict) in [
        (new_experimental_egraph(), false),
        (new_experimental_egraph_with_term_encoding(), false),
        (new_experimental_egraph_with_proof_testing(), true),
    ] {
        let program = graph.parse_program(None, source).unwrap();
        let checked =
            extraction::run_program_with_extract_checks(&mut graph, program, strict, &[]).unwrap();
        assert_eq!(checked.comparison_in_root_class.len(), 5);
        let outputs = checked.outputs;
        let terms: Vec<_> = outputs
            .iter()
            .filter_map(|output| match output {
                CommandOutput::ExtractBest(_, cost, _) => {
                    Some((output.to_string(), Some(cost.to_string())))
                }
                CommandOutput::ExtractVariants(..) => Some((output.to_string(), None)),
                _ => None,
            })
            .collect();
        if let Some(expected) = &expected {
            assert_eq!(&terms, expected);
        } else {
            expected = Some(terms);
        }
    }
}

#[test]
fn container_children_keep_their_contextual_sorts_during_extraction_checks() {
    let source = r#"
        (sort Ints (Vec i64))
        (sort Strings (Vec String))
        (datatype T (I Ints) (S Strings) (Pair T T))
        (let root (Pair (I (vec-empty)) (S (vec-empty))))
        (extract root)
        (extract root 3)
    "#;
    let mut expected = None;
    for (mut graph, strict) in [
        (new_experimental_egraph(), false),
        (new_experimental_egraph_with_term_encoding(), false),
        (new_experimental_egraph_with_proof_testing(), true),
    ] {
        let program = graph.parse_program(None, source).unwrap();
        let checked =
            extraction::run_program_with_extract_checks(&mut graph, program, strict, &[]).unwrap();
        assert_eq!(checked.comparison_in_root_class.len(), 2);
        let actual: Vec<_> = checked
            .outputs
            .iter()
            .filter_map(|output| match output {
                CommandOutput::ExtractBest(_, cost, _) => {
                    Some((output.to_string(), Some(cost.to_string())))
                }
                CommandOutput::ExtractVariants(..) => Some((output.to_string(), None)),
                _ => None,
            })
            .collect();
        if let Some(expected) = &expected {
            assert_eq!(&actual, expected);
        } else {
            expected = Some(actual);
        }
        assert!(
            !graph
                .print_size(None)
                .unwrap()
                .to_string()
                .contains("extract-validation")
        );
    }
}

#[test]
fn alternate_best_term_is_checked_at_the_original_extraction_boundary() {
    for (mut graph, strict) in [
        (new_experimental_egraph(), false),
        (new_experimental_egraph_with_term_encoding(), false),
        (new_experimental_egraph_with_proof_testing(), true),
    ] {
        let mut program = graph
            .parse_program(
                None,
                "(datatype T (A) (B) (C)) (union (A) (B)) (push) (extract (A)) (pop)",
            )
            .unwrap();
        let pop = program.pop().unwrap();
        let extract = program.pop().unwrap();
        graph.run_program(program).unwrap();
        let raw = graph.clone().run_program(vec![extract.clone()]).unwrap();
        let (cost, actual) = raw
            .iter()
            .find_map(|output| match output {
                CommandOutput::ExtractBest(dag, cost, term) => {
                    Some((cost.to_string(), dag.to_string(*term)))
                }
                _ => None,
            })
            .unwrap();
        let baseline = if actual == "(A)" { "(B)" } else { "(A)" };
        let checked = extraction::run_program_with_extract_checks(
            &mut graph,
            vec![extract.clone()],
            strict,
            &[Some(baseline)],
        )
        .unwrap();
        assert_eq!(
            checked.comparison_in_root_class,
            [Some(true)],
            "strict={strict}, extraction command {extract:?}"
        );
        let mut compared = vec![(Some(cost.clone()), vec![actual.clone()])];
        assert_eq!(
            extraction_comparison::compare(
                &mut compared,
                &[(Some(cost), vec![baseline.into()])],
                &checked.comparison_in_root_class,
                "boundary",
            ),
            Ok(1)
        );
        // The proof validator saw the exact actual RHS, not normalized text.
        assert!(checked.outputs.iter().any(|output| {
            matches!(output, CommandOutput::ExtractBest(dag, _, term) if dag.to_string(*term) == actual)
        }));
        let unequal = extraction::run_program_with_extract_checks(
            &mut graph,
            vec![extract, pop],
            strict,
            &[Some("(C)")],
        )
        .unwrap();
        assert_eq!(unequal.comparison_in_root_class, [Some(false)]);
    }
}

#[test]
fn ordinary_root_check_rejects_a_candidate_only_extraction_tie() {
    let mut candidate = new_experimental_egraph_with_term_encoding();
    candidate
        .parse_and_run_program(None, "(datatype T (A) (B)) (union (A) (B))")
        .unwrap();
    let raw = candidate
        .parse_and_run_program(None, "(extract (A))")
        .unwrap();
    let (cost, alternate) = raw
        .iter()
        .find_map(|output| match output {
            CommandOutput::ExtractBest(dag, cost, term) => {
                Some((cost.to_string(), dag.to_string(*term)))
            }
            _ => None,
        })
        .unwrap();
    let root = if alternate == "(A)" { "(B)" } else { "(A)" };
    let source = format!("(extract {root})");
    let program = candidate.parse_program(None, &source).unwrap();
    let checked =
        extraction::run_program_with_extract_checks(&mut candidate, program, false, &[Some(root)])
            .unwrap();
    assert_eq!(checked.comparison_in_root_class, [Some(true)]);
    assert!(checked.outputs.iter().any(|output| {
        matches!(output, CommandOutput::ExtractBest(dag, _, term) if dag.to_string(*term) == alternate)
    }));

    let mut ordinary = new_experimental_egraph();
    ordinary
        .parse_and_run_program(None, "(datatype T (A) (B))")
        .unwrap();
    let program = ordinary.parse_program(None, &source).unwrap();
    let checked = extraction::run_program_with_extract_checks(
        &mut ordinary,
        program,
        false,
        &[Some(&alternate)],
    )
    .unwrap();
    assert_eq!(checked.comparison_in_root_class, [Some(false)]);
    let mut actual: Vec<_> = checked
        .outputs
        .iter()
        .filter_map(|output| match output {
            CommandOutput::ExtractBest(dag, cost, term) => {
                Some((Some(cost.to_string()), vec![dag.to_string(*term)]))
            }
            _ => None,
        })
        .collect();
    assert_eq!(actual, [(Some(cost.clone()), vec![root.into()])]);
    assert!(
        extraction_comparison::compare(
            &mut actual,
            &[(Some(cost), vec![alternate])],
            &checked.comparison_in_root_class,
            "ordinary root check of a candidate-only merge",
        )
        .is_err()
    );
}

#[test]
fn source_constructor_root_can_be_materialized_without_leaking_validation_bindings() {
    for mut graph in [
        new_experimental_egraph(),
        new_experimental_egraph_with_term_encoding(),
    ] {
        let program = graph
            .parse_program(None, "(datatype T (A) (F T)) (extract (F (A)))")
            .unwrap();
        let checked =
            extraction::run_program_with_extract_checks(&mut graph, program, false, &[]).unwrap();
        assert_eq!(checked.comparison_in_root_class.len(), 1);
        let source_tables = graph.print_size(None).unwrap().to_string();
        assert!(!source_tables.contains("extract-validation"));
    }
}

#[test]
fn only_verified_equal_cost_best_term_ties_are_normalized() {
    let expected = vec![(Some("1".into()), vec!["(A)".into()])];
    let actual = vec![(Some("1".into()), vec!["(B)".into()])];
    let mut tied = actual.clone();
    assert_eq!(
        extraction_comparison::compare(&mut tied, &expected, &[Some(true)], "tie"),
        Ok(1)
    );
    assert_eq!(tied, expected);
    assert!(
        extraction_comparison::compare(&mut actual.clone(), &expected, &[Some(false)], "unequal")
            .is_err()
    );
    assert!(
        extraction_comparison::compare(&mut actual.clone(), &expected, &[None], "unverified")
            .is_err()
    );
    assert!(
        extraction_comparison::compare(
            &mut [(Some("2".into()), actual[0].1.clone())],
            &expected,
            &[Some(true)],
            "cost"
        )
        .is_err()
    );
    let variants = (None, vec!["(A)".into(), "(B)".into()]);
    let swapped = (None, vec!["(B)".into(), "(A)".into()]);
    assert!(
        extraction_comparison::compare(&mut [swapped], &[variants], &[Some(true)], "order")
            .is_err()
    );
}
