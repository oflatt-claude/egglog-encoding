//! Source-to-source slotted e-graph encoding.
#![doc = include_str!("LANGUAGE.md")]

pub mod export;
mod frontend;
mod maintenance;
mod model;
pub mod proofs;
mod query;
mod rewrite;
mod slots;
mod syntax;
pub use frontend::{Compiler, Options, ProofMode};

mod runtime;

/// An e-graph with the slotted runtime and egglog's built-in schedule semantics.
/// Evaluate [`Compiler::compile`]'s output with this graph.
pub fn new_egraph() -> egglog::EGraph {
    let mut graph =
        crate::new_experimental_egraph_with_options(false, crate::DisequalityEncoding::default());
    register(&mut graph);
    graph
}

/// Register the runtime for lowered slotted programs on an experimental e-graph.
/// Generated programs require core schedules, so construct the graph with the
/// extended schedule interpreter disabled.
pub fn register(graph: &mut egglog::EGraph) {
    runtime::register(graph);
    graph
        .add_command(
            "slotted-export".into(),
            std::sync::Arc::new(export::ExportCommand),
        )
        .unwrap();
}

/// An e-graph that lifts encoded slotted proofs and checks them against the source.
pub fn new_egraph_with_proofs() -> egglog::EGraph {
    with_proofs(new_egraph())
}

/// Enable proof translation and checking on a registered slotted e-graph.
pub fn with_proofs(mut graph: egglog::EGraph) -> egglog::EGraph {
    proofs::pipeline::register(&mut graph);
    graph.with_proofs_for_translation()
}
