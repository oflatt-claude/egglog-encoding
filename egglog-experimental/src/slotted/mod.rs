//! Source-to-source slotted e-graph encoding.

mod frontend;
mod maintenance;
mod model;
mod query;
mod rewrite;
mod syntax;
pub use frontend::{Compiler, Options};
