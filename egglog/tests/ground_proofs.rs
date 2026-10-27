use egglog::{CommandOutput, EGraph, TermDag};

fn graph(program: &str) -> EGraph {
    let mut graph = EGraph::new_with_proofs();
    graph.parse_and_run_program(None, program).unwrap();
    graph
}

fn prove(graph: &mut EGraph, terms: &TermDag, left: usize, right: usize, sort: &str) -> String {
    let sort = graph.type_info().get_sort_by_name(sort).unwrap().clone();
    let before = graph.num_nodes();
    let (store, proof) = graph.prove_equal_terms(terms, left, right, sort).unwrap();
    assert_eq!(graph.num_nodes(), before, "certification must not add rows");
    assert_eq!(
        store.term_dag().to_string(store.get(proof).lhs()),
        terms.to_string(left)
    );
    assert_eq!(
        store.term_dag().to_string(store.get(proof).rhs()),
        terms.to_string(right)
    );
    store.proof_to_string(proof)
}

#[test]
fn both_endpoints_can_be_rule_derived() {
    let mut graph = graph(
        "(datatype E (A) (B) (C)) (A)
        (rule ((= a (A))) ((B) (C) (union (B) (C))) :name \"derive\")
        (run 1)",
    );
    let mut terms = TermDag::default();
    let b = terms.app("B".into(), vec![]);
    let c = terms.app("C".into(), vec![]);
    assert!(prove(&mut graph, &terms, b, c, "E").contains("derive"));
}

#[test]
fn certification_preserves_requested_order_and_duplicate_outputs() {
    let mut graph = graph(
        "(datatype E (A) (B) (C) (Missing)) (A)
        (rule ((= a (A))) ((B) (C) (union a (B)) (union a (C)))) (run 1)",
    );
    let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    let mut terms = TermDag::default();
    let c = terms.app("C".into(), vec![]);
    let a = terms.app("A".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let missing = terms.app("Missing".into(), vec![]);
    let before = graph.num_nodes();
    let (store, proofs) = graph
        .prove_extracted_terms(&terms, b, &[c, a, c, b], sort.clone())
        .unwrap();
    let endpoints = proofs
        .into_iter()
        .map(|id| {
            let proof = store.get(id);
            assert_eq!(store.term_dag().to_string(proof.lhs()), "(B)");
            store.term_dag().to_string(proof.rhs())
        })
        .collect::<Vec<_>>();
    assert_eq!(endpoints, ["(C)", "(A)", "(C)", "(B)"]);

    let (_, proofs) = graph
        .prove_extracted_terms(&terms, b, &[], sort.clone())
        .unwrap();
    assert!(proofs.is_empty());
    let error = graph
        .prove_extracted_terms(&terms, missing, &[], sort)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (Missing) in the e-graph")
    );
    assert_eq!(graph.num_nodes(), before);
}

#[test]
fn congruence_certifies_syntax_that_was_never_inserted() {
    let mut graph = graph(
        "(datatype E (A) (B) (F E)) (F (A))
        (rule ((= a (A))) ((B) (union a (B))) :name \"derive\")
        (run 1)",
    );
    let mut terms = TermDag::default();
    let a = terms.app("A".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let fa = terms.app("F".into(), vec![a]);
    let fb = terms.app("F".into(), vec![b]);
    prove(&mut graph, &terms, fb, fa, "E");
}

#[test]
fn missing_evidence_and_unequal_terms_fail_without_insertion() {
    let mut graph = graph("(datatype E (A) (B) (Missing)) (A) (B)");
    let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    let mut terms = TermDag::default();
    let a = terms.app("A".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let missing = terms.app("Missing".into(), vec![]);
    let before = graph.num_nodes();
    for (left, right) in [(a, b), (missing, a), (a, missing), (missing, missing)] {
        assert!(
            graph
                .prove_equal_terms(&terms, left, right, sort.clone())
                .is_err()
        );
        assert_eq!(graph.num_nodes(), before);
    }
}

#[test]
fn containers_reuse_existing_row_projections() {
    let mut graph = graph(
        "(datatype E (A) (B)) (sort V (Vec E)) (datatype Box (Wrap V))
        (Wrap (vec-of (A)))
        (rule ((= a (A))) ((B) (union a (B))) :name \"derive\")
        (run 1)",
    );
    let mut terms = TermDag::default();
    let a = terms.app("A".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let va = terms.app("vec-of".into(), vec![a]);
    let vb = terms.app("vec-of".into(), vec![b]);
    let wa = terms.app("Wrap".into(), vec![va]);
    let wb = terms.app("Wrap".into(), vec![vb]);
    prove(&mut graph, &terms, wb, wa, "Box");
    // Container roots obtain their anchor from the existing Wrap row too.
    prove(&mut graph, &terms, vb, va, "V");
}

#[test]
fn an_unwitnessed_container_is_not_assumed_by_fiat() {
    let mut graph = graph("(datatype E (A)) (sort V (Vec E)) (A)");
    let sort = graph.type_info().get_sort_by_name("V").unwrap().clone();
    let mut terms = TermDag::default();
    let a = terms.app("A".into(), vec![]);
    let value = terms.app("vec-of".into(), vec![a]);
    let before = graph.num_nodes();
    let error = graph
        .prove_equal_terms(&terms, value, value, sort)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (vec-of (A)) in the e-graph")
    );
    assert_eq!(graph.num_nodes(), before);
}

#[test]
fn function_roots_project_their_existing_output_evidence() {
    let mut graph = graph(
        "(datatype E (A) (B)) (function root () E :merge old)
        (set (root) (A)) (rewrite (A) (B)) (run 1)",
    );
    let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    let mut terms = TermDag::default();
    let root = terms.app("root".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let before = graph.num_nodes();
    let (store, proof) = graph.prove_equal_terms(&terms, root, b, sort).unwrap();
    assert_eq!(store.term_dag().to_string(store.get(proof).lhs()), "(A)");
    assert_eq!(store.term_dag().to_string(store.get(proof).rhs()), "(B)");
    assert_eq!(graph.num_nodes(), before);
}

fn extracted(graph: &mut EGraph, command: &str) -> Vec<(String, String)> {
    let before = graph.num_nodes();
    let outputs = graph.parse_and_run_program(None, command).unwrap();
    assert_eq!(
        graph.num_nodes(),
        before,
        "prove-extract must not insert rows"
    );
    let CommandOutput::ProveExtract {
        proof_store,
        proof_ids,
    } = outputs
        .iter()
        .find(|output| matches!(output, CommandOutput::ProveExtract { .. }))
        .unwrap()
    else {
        panic!("expected extraction proofs");
    };
    proof_ids
        .iter()
        .map(|id| {
            let proof = proof_store.get(*id);
            (
                proof_store.term_dag().to_string(proof.lhs()),
                proof_store.term_dag().to_string(proof.rhs()),
            )
        })
        .collect()
}

#[test]
fn command_proves_all_variants_without_inserting_the_input() {
    let mut graph = graph(
        r#"(datatype E (A) (B) (F E)) (F (A))
        (rule ((= a (A))) ((B) (union a (B))) :name "derive") (run 1)"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract (F (B)) 3)");
    assert!(!proofs.is_empty());
    assert!(proofs.iter().all(|(left, _)| left == "(F (B))"));
    let before = graph.num_nodes();
    let error = graph
        .parse_and_run_program(None, "(prove-extract (F (F (A))))")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (F (F (A))) in the e-graph"),
        "{error}"
    );
    assert_eq!(graph.num_nodes(), before);
}

#[test]
fn command_preserves_a_globals_original_term() {
    let mut graph = graph(
        r#"(datatype E (A) (B) (F E)) (let input (F (A)))
        (rewrite (A) (B)) (run 1)"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract input)");
    assert_eq!(proofs[0].0, "(F (A))");
}

#[test]
fn container_normalization_and_nesting() {
    let mut graph = graph(
        r#"(datatype E (A) (B))
        (sort S (Set E)) (sort VV (Vec S)) (datatype Box (Wrap VV))
        (Wrap (vec-of (set-of (A) (B))))
        (union (A) (B)) (run 1)"#,
    );
    let proofs = extracted(
        &mut graph,
        "(prove-extract (Wrap (vec-of (set-of (A) (B)))))",
    );
    assert_eq!(proofs[0].0, "(Wrap (vec-of (set-of (A) (B))))");
}

#[test]
fn contextual_empty_containers_and_base_containers() {
    let mut graph = graph(
        r#"(datatype E (A)) (sort V (Vec E)) (sort VI (Vec i64))
        (datatype Box (Wrap V VI)) (Wrap (vec-empty) (vec-of 1 2))"#,
    );
    let proofs = extracted(
        &mut graph,
        "(prove-extract (Wrap (vec-empty) (vec-of 1 2)))",
    );
    assert_eq!(proofs[0].0, "(Wrap (vec-empty) (vec-of 1 2))");
}

#[test]
fn custom_function_container_arguments() {
    let mut graph = graph(
        r#"(datatype E (A)) (sort V (Vec E))
        (function get (V) E :merge old) (set (get (vec-of (A))) (A))"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract (get (vec-of (A))))");
    assert_eq!(proofs[0], ("(A)".into(), "(A)".into()));
}

#[test]
fn root_containers_can_be_nested_or_source_actions() {
    let mut graph = graph(
        r#"(datatype E (A)) (sort V (Vec E)) (sort VV (Vec V))
        (datatype Box (Wrap VV)) (Wrap (vec-of (vec-of (A))))"#,
    );
    assert_eq!(
        extracted(&mut graph, "(prove-extract (vec-of (A)))")[0].0,
        "(vec-of (A))"
    );
    let mut bare = EGraph::new_with_proofs();
    bare.parse_and_run_program(None, "(datatype E (A)) (sort V (Vec E)) (vec-of (A))")
        .unwrap();
    assert_eq!(
        extracted(&mut bare, "(prove-extract (vec-of (A)))")[0].0,
        "(vec-of (A))"
    );
}

#[test]
fn container_selectors_project_elements_from_existing_functions() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (sort V (Vec E)) (sort VV (Vec V))
        (function root () VV :merge old) (set (root) (vec-of (vec-of (A))))
        (rewrite (A) (B)) (run 1)"#,
    );
    extracted(&mut graph, "(prove-extract (vec-get (vec-get (root) 0) 0))");
    extracted(&mut graph, "(prove-extract (vec-get (root) 0))");
}

#[test]
fn maps_reorder_keys_without_changing_proof_format() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (sort M (Map i64 E))
        (datatype Box (Wrap M)) (Wrap (map-of 2 (A) 1 (B)))
        (union (A) (B)) (run 1)"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract (Wrap (map-of 2 (A) 1 (B))))");
    assert_eq!(proofs[0].0, "(Wrap (map-of 1 (B) 2 (A)))");
}

#[test]
fn encoded_replay_preserves_prove_extract() {
    let source = r#"(datatype E (A) (B) (F E)) (let input (F (A)))
        (rewrite (A) (B)) (run 1) (prove-extract input)"#;
    let encoded = EGraph::new_with_proofs()
        .resolve_program(None, source)
        .unwrap()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    let mut replay = EGraph::default();
    let program = replay.parse_program(None, source).unwrap();
    replay.set_proof_checking_program(program, false).unwrap();
    replay.ensure_no_reserved_symbols(false);
    let outputs = replay.parse_and_run_program(None, &encoded).unwrap();
    assert!(!CommandOutput::snapshot_proofs_only(&outputs).is_empty());
}

#[test]
fn scalar_evaluation_does_not_claim_temporary_container_existence() {
    let mut graph = graph("(datatype E (A)) (sort V (Vec E)) (A)");
    assert_eq!(
        extracted(&mut graph, "(prove-extract (vec-length (vec-of (A))))")[0],
        ("1".into(), "1".into())
    );
    assert_eq!(
        extracted(&mut graph, "(prove-extract (vec-get (vec-of (A)) 0))")[0],
        ("(A)".into(), "(A)".into())
    );
}

#[test]
fn late_globals_preserve_source_even_after_deletion() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (A) (B) (union (A) (B)) (run 1)
        (let input (B)) (delete (B))"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract input)");
    assert_eq!(proofs[0].0, "(B)");
}

#[test]
fn failures_and_scope_restore_are_read_only() {
    let mut graph = graph("(datatype E (A)) (A)");
    let before = graph.num_nodes();
    for command in ["(prove-extract (A) -1)", "(prove-extract (A) true)"] {
        assert!(graph.parse_and_run_program(None, command).is_err());
        assert_eq!(graph.num_nodes(), before);
    }
    graph
        .parse_and_run_program(
            None,
            "(push) (sort V (Vec E)) (datatype Box (Wrap V)) (Wrap (vec-of (A)))",
        )
        .unwrap();
    extracted(&mut graph, "(prove-extract (Wrap (vec-of (A))))");
    graph.parse_and_run_program(None, "(pop)").unwrap();
    extracted(&mut graph, "(prove-extract (A))");
    assert!(
        graph
            .parse_and_run_program(None, "(prove-extract (Wrap (vec-of (A))))")
            .is_err()
    );
}

#[test]
fn global_aliases_keep_their_provenance() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (A) (B)
        (rewrite (B) (A)) (run 1) (let first (B)) (let second first) (delete (B))"#,
    );
    assert_eq!(extracted(&mut graph, "(prove-extract second)")[0].0, "(B)");
}

#[test]
fn selector_can_return_a_nonleader() {
    let mut graph = graph("(datatype E (A) (B)) (sort V (Vec E)) (A) (B) (union (A) (B)) (run 1)");
    assert_eq!(
        extracted(&mut graph, "(prove-extract (vec-get (vec-of (B)) 0))")[0].0,
        "(B)"
    );
}

#[test]
fn repeated_equal_elements_keep_the_requested_representative_at_each_position() {
    let mut graph = graph(
        "(datatype E (A) (B)) (sort V (Vec E)) (datatype Box (Wrap V)) (Wrap (vec-of (A) (A))) (B) (union (A) (B)) (run 1)",
    );
    let proofs = extracted(&mut graph, "(prove-extract (Wrap (vec-of (A) (B))))");
    assert_eq!(proofs[0].0, "(Wrap (vec-of (A) (B)))");
}

#[test]
fn empty_container_existence_is_specific_to_its_sort() {
    let mut graph = graph(
        "(datatype A (MakeA)) (datatype B (MakeB)) (sort As (Vec A)) (sort Bs (Vec B)) (datatype Box (Wrap Bs)) (Wrap (vec-empty))",
    );
    let mut terms = TermDag::default();
    let empty = terms.app("vec-empty".into(), vec![]);
    let as_sort = graph.type_info().get_sort_by_name("As").unwrap().clone();
    let bs_sort = graph.type_info().get_sort_by_name("Bs").unwrap().clone();
    let error = graph
        .prove_equal_terms(&terms, empty, empty, as_sort)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (vec-empty) in the e-graph")
    );
    graph
        .prove_equal_terms(&terms, empty, empty, bs_sort)
        .unwrap();
}

#[test]
fn bare_container_source_certifies_a_different_extraction() {
    let mut graph =
        graph("(datatype E (A) (B)) (sort V (Vec E)) (A) (B) (union (A) (B)) (run 1) (vec-of (B))");
    let proofs = extracted(&mut graph, "(prove-extract (vec-of (B)))");
    assert_eq!(proofs[0], ("(vec-of (B))".into(), "(vec-of (A))".into()));
}

#[test]
fn container_primitives_use_the_types_of_their_result_elements() {
    let mut graph = graph(
        "(datatype E (A) (B)) (sort S (Set E)) (datatype Box (Wrap S)) (A) (Wrap (set-of (B))) (union (A) (B)) (run 1)",
    );
    let proofs = extracted(
        &mut graph,
        "(prove-extract (Wrap (set-intersect (set-of (B)) (set-of (B)))))",
    );
    assert_eq!(proofs[0].0, "(Wrap (set-of (B)))");
}

#[test]
fn proof_testing_certifies_plain_extracts_and_delimits_each_proof() {
    use egglog::ast::parse_sexps;

    let mut graph = EGraph::new_with_proofs().with_proof_testing();
    graph
        .parse_and_run_program(
            None,
            r#"
        (datatype E (A) (B) (C) (Missing)) (A)
        (rule ((= a (A))) ((B) (C) (union a (B)) (union a (C))) :name "derive")
        (run 1)
    "#,
        )
        .unwrap();
    let before = graph.num_nodes();
    let outputs = graph
        .parse_and_run_program(None, "(extract (C) 3) (extract (B))")
        .unwrap();
    let counts = outputs
        .iter()
        .filter_map(|output| match output {
            CommandOutput::ProveExtract { proof_ids, .. } => Some(proof_ids.len()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(counts, vec![3, 1]);
    let printed = CommandOutput::snapshot_proofs_only(&outputs);
    // Local let bindings must stay inside their proof's block. Parsing the
    // whole stream must recover exactly one top-level expression per proof.
    assert!(printed.contains("(let "));
    assert_eq!(parse_sexps(None, &printed).unwrap().len(), 4);
    assert_eq!(graph.num_nodes(), before);
    let error = graph
        .parse_and_run_program(None, "(extract (Missing))")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (Missing) in the e-graph")
    );
    assert_eq!(graph.num_nodes(), before);
}
