use egglog::EGraph;

#[test]
fn flowlog_runs_basic_egg() {
    let backend = Box::new(egglog_experimental_flowlog::EGraph::new_interpret());
    let mut eg = EGraph::with_backend(backend);
    eg.parse_and_run_program(
        None,
        "(datatype Math (Num i64) (Add Math Math))\n(Add (Num 1) (Num 2))\n(run 1)\n(print-size Add)",
    )
    .unwrap();
}
