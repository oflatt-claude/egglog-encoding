//! Frozen source-reachability checks for the vertical-fusion comparison.
use egglog::EGraph;
use egglog_experimental::slotted::{Compiler, new_egraph};

#[test]
fn slotted_vertical_fusion_preserves_scopes() {
    let source = concat!(
        include_str!("slotted/languages/sdql.egg"),
        "\n",
        include_str!("../../benchmarks/slotted/vertical/rules.egg"),
        "\n",
        include_str!("../../benchmarks/slotted/vertical/checks-slotted.egg"),
    );
    let compiled = Compiler::default().compile(None, source).unwrap();
    new_egraph().parse_and_run_program(None, &compiled).unwrap();
}

#[test]
fn debruijn_vertical_fusion_revisits_updated_substitution_bodies() {
    let source = concat!(
        include_str!("../../benchmarks/slotted/vertical/debruijn.egg"),
        "\n",
        include_str!("../../benchmarks/slotted/vertical/checks-debruijn.egg"),
    );
    EGraph::default()
        .parse_and_run_program(None, source)
        .unwrap();
}
