//! Differential test: run a curated subset of egglog's own `.egg` corpus on
//! BOTH the reference in-memory backend and the FlowLog backend, and assert
//! they agree — unconditionally (no env gating), as part of `cargo test`.
//!
//! Both egraphs are built identically (`EGraph::default()` vs
//! `EGraph::with_backend(FlowlogEGraph)`), so the frontend drives the exact
//! same operations into each backend. We append `(print-size)` to every file
//! and compare its output (per-function row counts) between the two backends:
//! if FlowLog's differential-dataflow engine derives a different final
//! database than the reference, the counts diverge and the test fails.
//!
//! FlowLog implements only a subset of egglog (no proofs / containers /
//! subsumption / complex merges, and every rule body must be DD-lowerable), so
//! the list below is limited to corpus files that run on it.

use egglog::EGraph;

/// egglog corpus files that run on FlowLog and agree with the reference backend.
const CORPUS: &[&str] = &[
    "bool.egg",
    "i64.egg",
    "bitwise.egg",
    "interval.egg",
    "before-proofs.egg",
    "merge-saturates.egg",
    "string.egg",
];

/// Run `program` and return the output of the trailing `(print-size)` as text.
fn print_size_of(mut eg: EGraph, file: &str, program: &str) -> String {
    let outputs = eg
        .parse_and_run_program(Some(file.to_string()), program)
        .unwrap_or_else(|e| panic!("run failed on {file}: {e}"));
    // The appended `(print-size)` is the last command; its output summarizes
    // every function's row count deterministically.
    outputs.last().map(|o| o.to_string()).unwrap_or_default()
}

#[test]
fn flowlog_matches_reference_backend() {
    for file in CORPUS {
        let path = std::path::Path::new("../../egglog/tests").join(file);
        let src = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        // Append `(print-size)` so the trailing output is a full per-function
        // row-count summary of the final database.
        let program = format!("{src}\n(print-size)");

        let reference = print_size_of(EGraph::default(), file, &program);
        let flowlog = print_size_of(
            EGraph::with_backend(Box::new(
                egglog_experimental_flowlog::EGraph::new_interpret(),
            )),
            file,
            &program,
        );

        assert_eq!(
            reference, flowlog,
            "FlowLog and the reference backend disagree on {file}:\n\
             --- reference (print-size) ---\n{reference}\n\
             --- flowlog (print-size) ---\n{flowlog}",
        );
    }
}
