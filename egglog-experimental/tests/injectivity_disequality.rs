//! Positive disequality patterns and closure at user computation boundaries.
use egglog::EGraph;
use egglog_experimental::{
    new_experimental_egraph_for_proofs, new_experimental_egraph_with_options,
    new_experimental_egraph_with_proof_testing, new_experimental_egraph_with_term_encoding,
};

const MODES: [fn() -> EGraph; 3] = [
    new_experimental_egraph_for_proofs,
    new_experimental_egraph_with_term_encoding,
    new_experimental_egraph_with_proof_testing,
];

#[test]
fn disequalities_propagate_upward_with_fixed_other_inputs_only() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (C) (D) (Pair T T) (Wrap T) (Plain T))
            (separately-injective Pair) (separately-injective Wrap)
            (Pair (A) (C)) (Pair (B) (C)) (Pair (C) (A)) (Pair (C) (B))
            (Pair (A) (A)) (Pair (B) (B)) (Plain (A)) (Plain (B))
            (Wrap (Pair (A) (C))) (Wrap (Pair (B) (C)))
            (disequal (A) (B))
            (check (known-disequal (Pair (A) (C)) (Pair (B) (C))))
            (check (known-disequal (Pair (C) (A)) (Pair (C) (B))))
            (check (known-disequal (Wrap (Pair (A) (C))) (Wrap (Pair (B) (C)))))
            (fail (check (known-disequal (Pair (A) (A)) (Pair (B) (B)))))
            (fail (check (known-disequal (Plain (A)) (Plain (B)))))
            (disequal (Wrap (C)) (Wrap (D)))
            (fail (check (known-disequal (C) (D))))
            (union (A) (C))
            (check (known-disequal (C) (B)))
            (fail (check (known-disequal (C) (D))))
        ",
            )
            .unwrap();
    }
}

#[test]
fn one_user_run_consumes_closure_from_the_previous_initialization_run() {
    for mode in MODES {
        mode().parse_and_run_program(None, "
            (datatype T (X) (One) (Two) (Add T T) (Exp T))
            (separately-injective Add) (separately-injective Exp)
            (relation Found ()) (ruleset init) (ruleset consume)
            (rule () ((disequal (One) (Two)) (Exp (Add (X) (One))) (Exp (Add (X) (Two)))) :ruleset init)
            (rule ((known-disequal (Exp (Add (X) (One))) (Exp (Add (X) (Two))))) ((Found)) :ruleset consume)
            (run init 1) (run consume 1) (check (Found))
        ").unwrap();
    }
}

#[test]
fn cancellation_and_disequality_share_a_fixed_point() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (C) (D) (F T) (Pair T T))
            (separately-injective F) (separately-injective Pair)
            (union (F (A)) (F (B)))
            (Pair (A) (C)) (Pair (B) (D))
            (disequal (C) (D))
            (check (known-disequal (Pair (A) (C)) (Pair (B) (D))))
        ",
            )
            .unwrap();
    }
}

#[test]
fn core_nested_schedules_preserve_budgets_and_pre_step_until() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (F T)) (separately-injective F)
            (disequal (A) (B)) (F (A)) (F (B))
            (function count () i64 :merge new) (set (count) 0)
            (ruleset tick) (rule ((= n (count))) ((set (count) (+ n 1))) :ruleset tick)
            (run tick 4 :until (known-disequal (F (A)) (F (B))))
            (check (= (count) 0))
            (run-schedule (seq (repeat 2 (run tick)) (repeat 3 (run tick))))
            (check (= (count) 5))
            (ruleset finite)
            (rule ((= n (count)) (< n 8)) ((set (count) (+ n 1))) :ruleset finite)
            (run-schedule (saturate (seq (repeat 2 (run finite)))))
            (check (= (count) 8))
        ",
            )
            .unwrap();
    }
}

#[test]
fn extended_bare_run_and_scheduled_runs_close_after_each_step_and_before_until() {
    let mut graph = new_experimental_egraph_with_options(true);
    graph
        .parse_and_run_program(
            None,
            "
        (datatype T (A) (B) (F T)) (separately-injective F)
        (disequal (A) (B))
        (function count () i64 :merge new) (set (count) 0)
        (ruleset tick) (rule ((= n (count))) ((set (count) (+ n 1))) :ruleset tick)
        (relation Seen ()) (ruleset consume)
        (rule ((known-disequal (F (A)) (F (B)))) ((Seen)) :ruleset consume)
        (run-schedule (eval (F (A)) (F (B))) (run tick :until (known-disequal (F (A)) (F (B)))))
        (check (= (count) 0))
        (let-scheduler s (back-off))
        (run-schedule (run-with s tick :until (known-disequal (F (A)) (F (B)))))
        (check (= (count) 0))
        (run-schedule consume (repeat 2 (run tick)) (run-with s tick))
        (check (Seen)) (check (= (count) 3))
    ",
        )
        .unwrap();
}

#[test]
fn query_patterns_are_positive_read_only_and_root_only() {
    for mode in MODES {
        let mut graph = mode();
        graph
            .parse_and_run_program(
                None,
                "(datatype T (A) (B) (F T)) (fail (check (contradiction)))
            (fail (check (known-disequal (A) (B))))",
            )
            .unwrap();
        let rows = graph.num_tuples();
        graph
            .parse_and_run_program(
                None,
                "(fail (check (known-disequal (A) (B)))) (fail (check (contradiction)))",
            )
            .unwrap();
        assert_eq!(graph.num_tuples(), rows);
        for source in [
            "(known-disequal (A) (B))",
            "(contradiction)",
            "(check (= () (known-disequal (A) (B))))",
            "(check (= () (contradiction)))",
            "(rule () ((known-disequal (A) (B))))",
            "(rule () ((contradiction)))",
            "(check (known-disequal 1 2))",
            "(check (known-disequal (A)))",
            "(check (contradiction (A)))",
            "(check (known-disequal? (A) (B)))",
            "(check-contradiction)",
        ] {
            assert!(
                graph.parse_and_run_program(None, source).is_err(),
                "{source}"
            );
        }
        graph
            .parse_and_run_program(
                None,
                "(disequal (A) (B)) (check (known-disequal (B) (A)))
            (union (A) (B)) (check (contradiction))",
            )
            .unwrap();
    }
}

#[test]
fn query_operand_sorts_are_inferred_from_the_rule_head() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B)) (datatype Other (OtherValue)) (relation P (T T))
            (disequal (A) (B))
            (rule ((known-disequal x y)) ((P x y)))
            (run 1) (check (P (A) (B)))
        ",
            )
            .unwrap();
    }
}

#[test]
fn fresh_assertion_actions_share_typed_signatures() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B)) (relation P (T T))
            (disequal (A) (B))
            (rule ((known-disequal x y)) ((let z (unstable-fresh! T)) (disequal z x) (P z x)))
            (run 1) (check (P z (A)) (known-disequal z (A)))
        ",
            )
            .unwrap();
    }
}

#[test]
fn extended_steps_restore_closure_before_the_next_consumer() {
    for step in ["init", "(run init)", "(run-with s init)"] {
        let mut graph = new_experimental_egraph_with_options(true);
        graph
            .parse_and_run_program(
                None,
                &format!(
                    "
            (datatype T (A) (B) (F T)) (separately-injective F)
            (ruleset init) (ruleset consume) (relation Seen ())
            (let-scheduler s (back-off))
            (rule () ((disequal (A) (B)) (F (A)) (F (B))) :ruleset init)
            (rule ((known-disequal (F (A)) (F (B)))) ((Seen)) :ruleset consume)
            (run-schedule {step} (run consume)) (check (Seen))
        "
                ),
            )
            .unwrap();
    }
}

#[test]
fn fail_sequences_close_each_internal_boundary_and_roll_back() {
    for mode in MODES {
        let mut graph = mode();
        graph
            .parse_and_run_program(
                None,
                "(datatype T (A) (B) (F T)) (separately-injective F)
            (ruleset init) (ruleset consume) (relation Seen ())
            (rule () ((disequal (A) (B)) (F (A)) (F (B))) :ruleset init)
            (rule ((known-disequal (F (A)) (F (B)))) ((Seen)) :ruleset consume)",
            )
            .unwrap();
        for source in [
            "(fail (disequal (A) (B)) (union (A) (B)) (check (contradiction)))",
            "(fail (run init 1) (run consume 1) (check (Seen)))",
        ] {
            let error = graph.parse_and_run_program(None, source).unwrap_err();
            assert!(
                matches!(error, egglog::Error::ExpectFail(_)),
                "{source}: {error}"
            );
            graph.parse_and_run_program(None, "(fail (check (contradiction))) (fail (check (Seen))) (fail (check (known-disequal (A) (B))))").unwrap();
        }
    }
}

#[test]
fn extended_until_rejects_invalid_patterns_without_executing_the_run() {
    let mut graph = new_experimental_egraph_with_options(true);
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B)) (datatype U (Other))
        (relation Ticked ()) (ruleset tick) (rule () ((Ticked)) :ruleset tick)
        (let-scheduler s (back-off))",
        )
        .unwrap();
    for step in ["run tick", "run-with s tick"] {
        for condition in [
            "(= () (known-disequal (A) (B)))",
            "(known-disequal (A))",
            "(known-disequal (A) (Other))",
            "(contradiction (A))",
            "(= () (contradiction))",
        ] {
            let source = format!("(run-schedule ({step} :until {condition}))");
            assert!(
                graph.parse_and_run_program(None, &source).is_err(),
                "{source}"
            );
            graph
                .parse_and_run_program(None, "(fail (check (Ticked)))")
                .unwrap();
        }
    }
    graph
        .parse_and_run_program(
            None,
            "(run-schedule (run tick :until (known-disequal (A) (B)))) (check (Ticked))",
        )
        .unwrap();
}

#[test]
fn root_patterns_work_in_rewrite_conditions_and_nested_ordinary_facts_remain_valid() {
    for mode in MODES {
        let mut graph = mode();
        graph
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (Wrap T)) (disequal (A) (B))
            (rewrite (Wrap x) x :when ((known-disequal x (B)) (= (+ 1 2) 3)))
            (Wrap (A)) (run 1) (check (= (Wrap (A)) (A)))",
            )
            .unwrap();
        assert!(
            graph
                .parse_and_run_program(
                    None,
                    "(rewrite (Wrap x) x :when ((= () (known-disequal x (B)))))"
                )
                .is_err()
        );
    }
}

#[test]
fn keep_best_recomputes_derived_evidence_before_the_next_observation() {
    let mut graph = new_experimental_egraph_for_proofs();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (Num i64)) (separately-injective Num)
        (Num 1) (Num 2) (check (known-disequal (Num 1) (Num 2)))",
        )
        .unwrap();
    let table = graph
        .get_function_names()
        .into_iter()
        .find(|name| name.contains("disequality-ne"))
        .unwrap();
    assert_eq!(graph.get_size(&table), 2);
    graph
        .parse_and_run_program(None, "(keep-best \"Num\")")
        .unwrap();
    assert_eq!(graph.get_size(&table), 0);
    graph
        .parse_and_run_program(None, "(check (known-disequal (Num 1) (Num 2)))")
        .unwrap();
    assert_eq!(graph.get_size(&table), 2);
    assert_eq!(graph.get_size("Num"), 2);
}

#[test]
fn extended_schedule_returns_one_combined_report_with_maintenance() {
    let mut graph = new_experimental_egraph_with_options(true);
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B)) (disequal (A) (B)) (ruleset tick)",
        )
        .unwrap();
    let outputs = graph
        .parse_and_run_program(None, "(run-schedule (run tick))")
        .unwrap();
    assert_eq!(outputs.len(), 1);
    assert!(matches!(outputs[0], egglog::CommandOutput::RunSchedule(_)));
}

#[test]
fn input_inside_fail_restores_closure_and_rolls_back_loaded_rows() {
    let path = std::env::temp_dir().join(format!(
        "egglog-disequality-input-{}.tsv",
        std::process::id()
    ));
    std::fs::write(&path, "1\n2\n").unwrap();
    for mode in MODES {
        let mut graph = mode();
        graph
            .parse_and_run_program(None, "(datatype T (Num i64)) (separately-injective Num)")
            .unwrap();
        let result = graph.parse_and_run_program(
            None,
            &format!(
                "(fail (input Num \"{}\") (check (known-disequal (Num 1) (Num 2))))",
                path.display()
            ),
        );
        assert!(
            matches!(result, Err(egglog::Error::ExpectFail(_))),
            "{result:?}"
        );
        assert_eq!(graph.get_size("Num"), 0);
    }
    std::fs::remove_file(path).unwrap();
}

#[test]
fn contradiction_only_support_is_scoped_and_can_be_reinstalled() {
    for mode in MODES {
        let mut graph = mode();
        graph
            .parse_and_run_program(None, "(push) (fail (check (contradiction))) (pop)")
            .unwrap();
        assert!(
            graph
                .get_function_names()
                .iter()
                .all(|name| !name.contains("disequality"))
        );
        graph
            .parse_and_run_program(
                None,
                "(fail (check (contradiction)))
            (datatype T (A)) (disequal (A) (A)) (check (contradiction))",
            )
            .unwrap();
    }
}
