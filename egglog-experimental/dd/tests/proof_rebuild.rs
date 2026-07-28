//! DD proof-mode rebuild, which the corpus in `files.rs` does not reach (it
//! runs the term-encoding treatment only).
//!
//! The rebuild rules canonicalize a row's eq-sort columns through the guarded
//! congruence-step ops, which DD services against its own mirror rather than
//! the embedded db. These tests pin that path by requiring DD to agree with the
//! reference backend, row for row.

use egglog::{CommandOutput, EGraph};

/// Run `program` in proof mode on both backends and return `(dd, reference)`
/// outputs, normalized the same way so they are directly comparable.
fn run_both(program: &str) -> (String, String) {
    let render = |eg: &mut EGraph| {
        CommandOutput::snapshot_stable_under_proof_encoding(
            &eg.parse_and_run_program(None, program)
                .expect("program should run in proof mode"),
        )
        .trim_end()
        .to_string()
    };
    let mut dd = EGraph::with_backend(Box::new(egglog_experimental_dd::EGraph::new()))
        .with_proofs_enabled()
        .with_proof_testing();
    let mut reference = EGraph::default().with_proofs_enabled().with_proof_testing();
    (render(&mut dd), render(&mut reference))
}

/// A union under a constructor: both children of `(Add a a)` move, so the
/// rebuild folds two congruence steps onto the row proof.
#[test]
fn moved_children_rebuild_to_the_same_rows_as_the_reference() {
    let (dd, reference) = run_both(
        r#"
(datatype Math (Num i64) (Add Math Math))
(let a (Num 1))
(let b (Num 2))
(Add a a)
(Add b b)
(union a b)
(run-schedule (saturate (run)))
(check (= (Add a a) (Add b b)))
(print-size Add)
(print-size Num)
"#,
    );
    assert_eq!(dd, reference);
}

/// A union of two whole terms: the e-class column moves while the children stay
/// put, so the rebuild takes the `Sym`/`Trans` step and skips the child steps.
#[test]
fn moved_eclass_rebuilds_to_the_same_rows_as_the_reference() {
    let (dd, reference) = run_both(
        r#"
(datatype Math (Num i64) (Add Math Math))
(let a (Num 1))
(let b (Num 2))
(let x (Add a b))
(let y (Num 3))
(union x y)
(run-schedule (saturate (run)))
(check (= (Add a b) y))
(print-size Add)
(print-size Num)
"#,
    );
    assert_eq!(dd, reference);
}

/// A rule-driven union under an enclosing term, so the checked equality holds
/// only through the enclosing row's rebuild rather than through the rule alone.
#[test]
fn rule_driven_unions_rebuild_to_the_same_rows_as_the_reference() {
    let (dd, reference) = run_both(
        r#"
(datatype Math (Num i64) (Add Math Math) (Mul Math Math))
(let base (Num 0))
(Mul (Add (Num 1) (Num 2)) (Num 3))
(rule ((= e (Add x y))) ((union e base)))
(run-schedule (saturate (run)))
(check (= (Mul (Add (Num 1) (Num 2)) (Num 3)) (Mul (Num 0) (Num 3))))
(print-size Add)
(print-size Mul)
"#,
    );
    assert_eq!(dd, reference);
}
