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
    let fixture = std::fs::read_to_string(
        repository.join("egglog-experimental/tests/math-microbenchmark-rational.egg"),
    )
    .unwrap();
    let (base, _) = fixture
        .split_once("(run 11)")
        .expect("Math fixture should run eleven iterations");
    format!("{base}\n(run {iterations})\n{check}\n")
}

#[test]
fn terminal_math_equality_requires_iteration_eleven() {
    let repository = repository();
    let check = format!("(check (= {CHECK_LEFT} {CHECK_RIGHT}))");

    let fixture = std::fs::read_to_string(
        repository.join("egglog-experimental/tests/math-microbenchmark-rational.egg"),
    )
    .unwrap();
    assert!(fixture.contains("(run 11)"));

    let error = egglog_experimental::new_experimental_egraph()
        .parse_and_run_program(None, &math_program(&repository, 10, &check))
        .unwrap_err();
    assert!(error.to_string().contains("Check failed"));

    egglog_experimental::new_experimental_egraph_with_proof_testing()
        .parse_and_run_program(None, &fixture)
        .unwrap();
}
