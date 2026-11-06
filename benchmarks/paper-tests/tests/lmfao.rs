//! Live binder-sensitive batching rules on small frozen query programs.
use egglog_experimental::slotted::{Compiler, Options, export, new_egraph};
use serde::Deserialize;
use slotted_reference::{Substitution, run_spec};
use std::path::Path;

#[derive(Deserialize)]
struct Fixture {
    multi: String,
    expected_goal: bool,
}

#[test]
fn aggregate_batch_rules_preserve_native_goals_and_counts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    for name in [
        "independent",
        "pack",
        "fuse",
        "grouping",
        "nonlinear",
        "different-sources",
    ] {
        let path = root.join(format!("benchmarks/lmfao/correctness/{name}.egg"));
        let fixture: Fixture =
            serde_json::from_str(&std::fs::read_to_string(path.with_extension("ref")).unwrap())
                .unwrap();
        let source = std::fs::read_to_string(&path).unwrap();
        let mut compiler = Compiler::new(Options::default());
        let mut graph = new_egraph();
        graph.set_num_threads(1);
        let lowered = compiler
            .compile(Some(path.display().to_string()), &source)
            .unwrap();
        graph
            .parse_and_run_program(None, &lowered)
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        let exported = export::export(&graph).unwrap();
        let native = run_spec(&fixture.multi, Substitution::Snapshot).unwrap();
        assert_eq!(
            native.goals,
            vec![fixture.expected_goal],
            "{name}: rule goal"
        );
        assert_eq!(
            (exported.counts.classes, exported.counts.nodes),
            (native.classes, native.nodes),
            "{name}: validated counts"
        );
    }
}
