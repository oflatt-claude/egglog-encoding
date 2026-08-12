use std::path::{Path, PathBuf};

const CHECK_LEFT: &str = r#"(Add (Cos (Var "x")) (Cos (Var "x")))"#;
const CHECK_RIGHT: &str = r#"(Diff (Var "x") (Add (Sin (Var "x")) (Sin (Var "x"))))"#;

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("egglog-experimental crate should be inside the workspace")
        .to_path_buf()
}

fn math_program(repository: &Path, iterations: usize, check: &str) -> String {
    let base = std::fs::read_to_string(repository.join("benchmarks/math-microbenchmark/base.egg"))
        .unwrap();
    let runs = std::iter::repeat_n("  (run)", iterations)
        .collect::<Vec<_>>()
        .join("\n");
    format!("{base}\n(run-schedule (seq\n{runs}))\n{check}\n")
}

#[test]
fn pointer_analysis_initdb_passes_proof_checking() {
    let repository = repository();
    let mut egraph = egglog_experimental::new_experimental_egraph_with_proof_testing();
    egraph.fact_directory = Some(repository.join("benchmarks/data/pointer-analysis-initdb"));
    let program =
        std::fs::read_to_string(repository.join("benchmarks/pointer-analysis-initdb.egg")).unwrap();

    egraph.parse_and_run_program(None, &program).unwrap();
}

#[test]
fn short_math_runs_pass_proof_checking() {
    let repository = repository();
    let check = r#"(check (= (Add (Var "x") (Cos (Var "x"))) (Add (Cos (Var "x")) (Var "x"))))"#;

    for iterations in [1, 6] {
        egglog_experimental::new_experimental_egraph_with_proof_testing()
            .parse_and_run_program(None, &math_program(&repository, iterations, check))
            .unwrap();
    }
}

#[test]
fn terminal_math_equality_requires_iteration_eleven() {
    let repository = repository();
    let check = format!("(check (= {CHECK_LEFT} {CHECK_RIGHT}))");

    let error = egglog_experimental::new_experimental_egraph()
        .parse_and_run_program(None, &math_program(&repository, 10, &check))
        .unwrap_err();
    assert!(error.to_string().contains("Check failed"));

    egglog_experimental::new_experimental_egraph()
        .parse_and_run_program(None, &math_program(&repository, 11, &check))
        .unwrap();
}
