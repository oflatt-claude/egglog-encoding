//! Witnessed isomorphism of ordinary and slotted serialized e-graphs.
//!
//! [`AnnotatedEGraph`] flattens [`egraph_serialize::EGraph`] and adds an optional
//! `slotted` object. Plain egg/egglog exports need no annotations. Slotted exports
//! describe each class's live slots and full symmetry group, and each node's
//! direct slots and child renamings. IDs are arbitrary; child order, operator
//! labels, class types, subsumption flags, and ordered roots are preserved.
//! Extraction costs and other class metadata are not part of graph equality.
//!
//! Node multiplicity is preserved, including duplicate rows and empty classes.
//! Private slots are alpha-renamed independently per node. Parent and child
//! symmetries may select different representatives of the same node.
//!
//! [`find_isomorphism`] returns an explicit [`Witness`] or distinguishes exhaustive
//! failure from bounded search. [`verify`] checks that witness directly, without
//! calling the search or node matcher. Input validation checks edge domains,
//! injectivity, and complete symmetry groups; it never repairs missing elements.
//! Callers must additionally establish that their engine's export is complete.
//!
//! A one-slot variable class, including its identity symmetry:
//!
//! ```json
//! {
//!   "nodes": {"v": {"op": "var", "eclass": "C", "children": []}},
//!   "slotted": {
//!     "classes": {"C": {"slots": ["x"], "group": [[0]]}},
//!     "nodes": {"v": {"arguments": [{"kind": "slot", "slot": "x"}]}}
//!   }
//! }
//! ```
//!
//! ```
//! use egraph_isomorphism::{AnnotatedEGraph, Graph, Limits, Outcome, find_isomorphism, verify};
//!
//! let document: AnnotatedEGraph = serde_json::from_str(r#"{
//!   "nodes": {"n": {"op": "constant", "eclass": "c", "children": []}}
//! }"#)?;
//! let graph = Graph::try_from(&document)?;
//! let Outcome::Isomorphic { witness } = find_isomorphism(&graph, &graph, Limits::default())? else {
//!     panic!("a graph must be isomorphic to itself");
//! };
//! verify(&graph, &graph, &witness)?;
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

mod graph;
mod search;
mod witness;

pub use egraph_serialize;
pub use graph::{AnnotatedEGraph, Argument, ClassSlots, Graph, NodeSlots, Slotted};
use serde::{Deserialize, Serialize};
pub use witness::{ClassMatch, NodeMatch, Witness, verify};

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct Error(pub String);

/// Search work limits. Input reading and direct witness verification do not search.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct Limits {
    pub search: usize,
    pub node_variants: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            search: 200_000,
            node_variants: 200_000,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum Outcome {
    Isomorphic { witness: Witness },
    Different { reason: String },
    Inconclusive { reason: String },
}

/// Search for a witness and check every returned witness before accepting it.
pub fn find_isomorphism(left: &Graph, right: &Graph, limits: Limits) -> Result<Outcome, Error> {
    let result = search::search(left, right, limits);
    if let Outcome::Isomorphic { witness } = &result {
        verify(left, right, witness)?;
    }
    Ok(result)
}

#[cfg(test)]
mod tests;
