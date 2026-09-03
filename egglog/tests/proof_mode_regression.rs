use egglog::ast::Command;
use egglog::util::SymbolGen;
use egglog::*;
use std::sync::{Arc, Mutex};

struct RecordFunctionInputArity {
    name: String,
    seen: Arc<Mutex<Vec<usize>>>,
}

impl CommandMacro for RecordFunctionInputArity {
    fn transform(
        &self,
        command: Command,
        _symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        if let Some(func) = type_info.get_func_type(&self.name) {
            self.seen.lock().unwrap().push(func.input.len());
        }
        Ok(vec![command])
    }
}

#[test]
fn proof_mode_command_macros_see_original_function_arities() {
    let seen = Arc::new(Mutex::new(vec![]));
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .command_macros_mut()
        .register(Arc::new(RecordFunctionInputArity {
            name: "score".to_string(),
            seen: seen.clone(),
        }));

    egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype Math (Num i64))
            (function score (Math) i64 :merge old)
            (let x (Num 1))
            "#,
        )
        .unwrap();

    assert_eq!(*seen.lock().unwrap(), vec![1]);
}

#[test]
fn term_and_proof_modes_lower_input_rows_as_fiat_actions() {
    let directory = std::env::temp_dir().join(format!("egglog_proof_input_{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("edges.tsv"), "a\tb\nb\tc\n").unwrap();
    std::fs::write(directory.join("scores.tsv"), "a\t7\n").unwrap();
    std::fs::write(directory.join("seen.tsv"), "a\n").unwrap();

    for mut egraph in [
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph.fact_directory = Some(directory.clone());
        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation Edge (String String))
                (function score (String) i64 :no-merge)
                (function seen (String) Unit :no-merge)
                (input Edge "edges.tsv")
                (input score "scores.tsv")
                (input seen "seen.tsv")
                (check (Edge "a" "b"))
                (check (= (score "a") 7))
                (check (= (seen "a") ()))
                "#,
            )
            .unwrap();
    }

    std::fs::remove_dir_all(directory).ok();
}

#[test]
fn term_and_proof_modes_reject_eq_sort_no_merge_functions() {
    // Eq-sort-output `:no-merge` is not modeled by the encoding (its conflict check
    // needs union-find leaders); such a program is unsupported and runs plain only.
    // Primitive/Unit-output `:no-merge` is supported (see the input test above).
    for mut egraph in [
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        let error = egraph
            .parse_and_run_program(None, "(sort Foo) (function bar () Foo :no-merge)")
            .unwrap_err();
        assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
        assert!(error.to_string().contains("`:no-merge`"));
    }
}

#[test]
fn proof_mode_rejects_fail_wrapped_input() {
    let error = EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (relation Edge (String String))
            (fail (input Edge "edges.tsv"))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    assert!(
        error
            .to_string()
            .contains("`fail` wrapping an `input` command")
    );
}

#[test]
fn proof_mode_rejects_fail_wrapped_set_before_mutation() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
            (function score () i64 :merge old)
            (fail (set (score) 1))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    assert!(
        error
            .to_string()
            .contains("`fail` wrapping a proof-producing operation")
    );
    egraph
        .parse_and_run_program(None, "(fail (check (= (score) 1)))")
        .unwrap();
    egraph
        .parse_and_run_program(None, "(set (score) 1) (prove (= (score) 1))")
        .unwrap();
}

#[test]
fn term_mode_preserves_fail_wrapped_mutation_and_merge_declaration() {
    let mut egraph = EGraph::new_with_term_encoding();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (function score () i64 :merge old)
            (fail (set (score) 1) (check (= (score) 2)))
            (check (= (score) 1))
            "#,
        )
        .unwrap();

    let error = egraph
        .parse_and_run_program(None, "(fail (function other () i64 :merge old))")
        .unwrap_err();
    assert!(matches!(error, Error::ExpectFail(..)));
    egraph
        .parse_and_run_program(None, "(set (other) 2) (check (= (other) 2))")
        .unwrap();
}

#[test]
fn term_mode_preserves_fail_wrapped_rule_errors() {
    let mut egraph = EGraph::new_with_term_encoding();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (relation number (i64))
            (ruleset base)
            (unstable-combined-ruleset combo base)
            (fail
              (rule () ((number 1)) :ruleset combo :name "bad-combined"))
            (fail
              (rule () ((number 2)) :ruleset missing :name "bad-missing"))
            (rule () ((number 3)) :ruleset base :name "good")
            (run-schedule (run base))
            (check (number 3))
            "#,
        )
        .unwrap();
}

#[test]
fn term_mode_rejects_skipped_fail_wrapped_definition_without_leaking_type_state() {
    let mut egraph = EGraph::new_with_term_encoding();
    let error = egraph
        .parse_and_run_program(
            None,
            "(fail (check (= 1 2)) (function score () i64 :no-merge))",
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(
            None,
            "(function score () i64 :no-merge) (set (score) 1) (check (= (score) 1))",
        )
        .unwrap();
}

#[test]
fn term_mode_rejects_skipped_fail_wrapped_global_without_leaking_type_state() {
    let mut egraph = EGraph::new_with_term_encoding();
    egraph
        .parse_and_run_program(None, "(datatype N (A))")
        .unwrap();
    let error = egraph
        .parse_and_run_program(None, "(fail (let $leading (A)))")
        .unwrap_err();
    assert!(matches!(error, Error::ExpectFail(..)));
    egraph
        .parse_and_run_program(None, "(check (= $leading (A)))")
        .unwrap();

    let error = egraph
        .parse_and_run_program(None, "(fail (check (= 1 2)) (let $n (A)))")
        .unwrap_err();
    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));

    egraph
        .parse_and_run_program(None, "(let $n (A)) (check (= $n (A)))")
        .unwrap();
}

#[test]
fn proof_mode_rejects_fail_wrapped_union_before_mutation() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype N (A) (B))
            (let a (A))
            (let b (B))
            (fail (union a b))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(None, "(fail (check (= a b)))")
        .unwrap();
    egraph
        .parse_and_run_program(None, "(union a b) (prove (= a b))")
        .unwrap();
}

#[test]
fn proof_mode_rejects_fail_wrapped_extract_before_term_interning() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype N (A))
            (fail (extract (A) -1))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(None, "(A) (prove (= (A) (A)))")
        .unwrap();
}

#[test]
fn proof_mode_allows_fail_wrapped_extract_of_existing_global() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(None, "(datatype N (A)) (let a (A))")
        .unwrap();
    egraph
        .parse_and_run_program(None, "(fail (extract a -1))")
        .unwrap();
    egraph
        .parse_and_run_program(None, "(prove (= a (A)))")
        .unwrap();
}

#[test]
fn proof_mode_rejects_fail_wrapped_output_before_term_interning() {
    let directory = std::env::temp_dir().join(format!("egglog_fail_output_{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let output = directory.join("term.txt");
    let mut egraph = EGraph::new_with_proofs();
    egraph.fact_directory = Some(directory.clone());
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype N (A))
            (fail (output "term.txt" (A)) (panic "stop"))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    assert!(!output.exists());
    egraph
        .parse_and_run_program(None, "(A) (prove (= (A) (A)))")
        .unwrap();
    std::fs::remove_dir_all(directory).ok();
}

#[test]
fn proof_mode_rejects_fail_wrapped_output_of_existing_global() {
    let directory =
        std::env::temp_dir().join(format!("egglog_fail_global_output_{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let output = directory.join("term.txt");
    let mut egraph = EGraph::new_with_proofs();
    egraph.fact_directory = Some(directory.clone());
    egraph
        .parse_and_run_program(None, "(datatype N (A)) (let $a (A))")
        .unwrap();
    let error = egraph
        .parse_and_run_program(None, "(fail (output \"term.txt\" $a) (panic \"stop\"))")
        .unwrap_err();

    assert!(matches!(error, Error::TypeError(..)));
    assert!(error.to_string().contains("Arity mismatch"));
    assert!(!output.exists());
    egraph
        .parse_and_run_program(None, "(prove (= $a (A)))")
        .unwrap();
    std::fs::remove_dir_all(directory).ok();
}

#[test]
fn proof_mode_rejects_fail_wrapped_scope_changes_before_execution() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(None, "(datatype N (A)) (A)")
        .unwrap();
    let error = egraph
        .parse_and_run_program(None, "(fail (push) (panic \"stop\"))")
        .unwrap_err();
    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(None, "(prove (= (A) (A)))")
        .unwrap();

    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(None, "(datatype N (A)) (A) (push)")
        .unwrap();
    let error = egraph
        .parse_and_run_program(None, "(fail (pop) (panic \"stop\"))")
        .unwrap_err();
    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(None, "(pop) (A) (prove (= (A) (A)))")
        .unwrap();
}

#[test]
fn proof_mode_rejects_fail_wrapped_merge_function_before_declaration() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype N (A) (B) (C N N))
            (fail (function score () N :merge (C old new)))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    assert!(error.to_string().contains("wrapping this definition"));
    egraph
        .parse_and_run_program(
            None,
            r#"
            (function score () N :merge (C old new))
            (set (score) (A))
            (set (score) (B))
            (prove (= (score) (C (A) (B))))
            "#,
        )
        .unwrap();
}

#[test]
fn proof_mode_allows_leading_fail_wrapped_proof_inert_definitions() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
            (fail
              (datatype N (A) (B))
              (ruleset prefix)
              (function score () i64 :no-merge))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::ExpectFail(..)));
    let error = egraph
        .parse_and_run_program(None, "(ruleset prefix)")
        .unwrap_err();
    assert!(matches!(error, Error::Shadowing(..)));
    egraph
        .parse_and_run_program(
            None,
            r#"
            (A)
            (rule ((= x (A))) ((union x (B))) :ruleset prefix :name "prefix-rule")
            (run-schedule (run prefix))
            (set (score) 1)
            (prove (= (A) (B)))
            (prove (= (score) 1))
            "#,
        )
        .unwrap();
}

#[test]
fn proof_mode_rejects_skipped_fail_wrapped_no_merge_function() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(
            None,
            "(fail (check (= 1 2)) (function score () i64 :no-merge))",
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    assert!(error.to_string().contains("wrapping this definition"));
    egraph
        .parse_and_run_program(
            None,
            "(function score () i64 :no-merge) (set (score) 1) (prove (= (score) 1))",
        )
        .unwrap();
}

#[test]
fn proof_mode_rejects_skipped_fail_wrapped_datatype() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(None, "(fail (check (= 1 2)) (datatype N (A)))")
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(None, "(datatype N (A)) (A) (prove (= (A) (A)))")
        .unwrap();
}

#[test]
fn encoded_modes_roll_back_definitions_when_fail_resolution_fails_late() {
    for mut egraph in [EGraph::new_with_term_encoding(), EGraph::new_with_proofs()] {
        let error = egraph
            .parse_and_run_program(None, "(fail (datatype N (A)) (check (= A (A))))")
            .unwrap_err();
        assert!(matches!(error, Error::Shadowing(..)));

        egraph
            .parse_and_run_program(None, "(datatype N (A)) (A)")
            .unwrap();
    }

    let directory =
        std::env::temp_dir().join(format!("egglog_fail_resolution_{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    for mut egraph in [EGraph::new_with_term_encoding(), EGraph::new_with_proofs()] {
        egraph.fact_directory = Some(directory.clone());
        egraph
            .parse_and_run_program(None, "(datatype N (A)) (let $a (A))")
            .unwrap();
        let error = egraph
            .parse_and_run_program(None, "(fail (datatype M (B)) (output \"term.txt\" $a))")
            .unwrap_err();
        assert!(matches!(error, Error::TypeError(..)));

        egraph
            .parse_and_run_program(None, "(datatype M (B)) (B)")
            .unwrap();
    }
    assert!(!directory.join("term.txt").exists());
    std::fs::remove_dir_all(directory).ok();
}

#[test]
fn proof_mode_rejects_skipped_fail_wrapped_ruleset_definitions() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(None, "(fail (check (= 1 2)) (ruleset hidden))")
        .unwrap_err();
    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(None, "(ruleset hidden)")
        .unwrap();

    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(None, "(ruleset base)")
        .unwrap();
    let error = egraph
        .parse_and_run_program(
            None,
            "(fail (check (= 1 2)) (unstable-combined-ruleset combo base))",
        )
        .unwrap_err();
    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(None, "(unstable-combined-ruleset combo base)")
        .unwrap();
}

#[test]
fn proof_mode_rejects_fail_wrapped_rule_before_declaration() {
    let mut egraph = EGraph::new_with_proofs();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype N (A) (B))
            (ruleset hidden)
            (A)
            (fail
              (rule ((= x (A)))
                    ((union x (B)))
                    :ruleset hidden
                    :name "hidden-rule"))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    egraph
        .parse_and_run_program(
            None,
            r#"
            (rule ((= x (A)))
                  ((union x (B)))
                  :ruleset hidden
                  :name "hidden-rule")
            (run-schedule (run hidden))
            (prove (= (A) (B)))
            "#,
        )
        .unwrap();
}

#[test]
fn proof_mode_rejects_fail_wrapped_eq_globals_without_leaking_type_state() {
    for fail_command in ["(fail (let b a))", "(fail (let b (begin (A))))"] {
        let mut egraph = EGraph::new_with_proofs();
        let program = format!("(datatype N (A)) (let a (A)) {fail_command}");
        let error = egraph.parse_and_run_program(None, &program).unwrap_err();

        assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
        // An unregistered `b` is a local query variable here. A leaked global instead makes proof
        // conversion treat it as a missing nullary function and panic.
        egraph
            .parse_and_run_program(None, "(prove (= b a))")
            .unwrap();
        egraph
            .parse_and_run_program(None, "(prove (= a a))")
            .unwrap();
    }
}

#[test]
fn proof_mode_fail_catches_failure_among_wrapped_commands() {
    // `fail` runs the wrapped commands in order and succeeds at the first failure:
    // the first check succeeds and the second fails, so the `fail` passes.
    for mut egraph in [
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(
                None,
                r#"
            (datatype N (A) (B))
            (A)
            (fail (check (A)) (check (B)))
            "#,
            )
            .unwrap();
    }
}

/// A set element is reshaped (`(Id (N 1))` → `(N 1)`) and then collapses into
/// another element (`(N 1)` = `(N 3)`), in a set whose value-order element
/// list disagrees with its term form's AST order. Guards against container
/// rebuild proofs identifying changed elements by position instead of by term.
#[test]
fn unordered_container_reshaped_element_collapse_proof() {
    let program = "
(datatype Math (N i64) (Id Math))
(sort MSet (Set Math))
(relation Holds (MSet))
(relation Go ())
(Go)
(rewrite (Id x) x)
(rule ((Go)) ((Holds (set-of (Id (N 1)) (Id (N 2)) (N 3)))))
(rule ((Go)) ((union (N 1) (N 3))))
(run 8)
(check (Holds (set-of (N 1) (N 2))))
";
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(None, program)
        .unwrap();
}
