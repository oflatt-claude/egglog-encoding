//! Source-to-source slotted e-graph encoding.

mod frontend;
mod maintenance;
mod model;
mod query;
mod rewrite;
mod slots;
mod syntax;
pub use frontend::{Compiler, Options};

mod runtime;

/// An e-graph with the slotted runtime and egglog's built-in schedule semantics.
/// Evaluate [`Compiler::compile`]'s output with this graph.
pub fn new_egraph() -> egglog::EGraph {
    let mut graph = crate::new_experimental_egraph_with_native_schedule();
    runtime::register(&mut graph);
    graph
}
