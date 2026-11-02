//! Surface proofs for slotted programs, their checker, and lifting from
//! encoded egglog proofs. See `egglog-experimental/src/slotted/PROOFS.md` for
//! the proof format and lifting rules.

mod bindings;
pub mod checker;
mod context;
mod coordinates;
pub mod format;
mod guards;
mod lift_slots;
mod normalize;
pub(crate) mod pipeline;
mod program;
mod resolve;
pub mod terms;
mod unflatten;

pub use checker::{SlottedCheckError, check_claim, check_proof};
pub use context::SourceError;
pub use format::{
    Claim, ClaimKind, ProofId, RulePremise, RuleProof, SlottedProof, SlottedProofStore,
};
pub use program::ResolvedSlottedProgram;
pub use resolve::resolve_program;
pub use terms::Renaming;

use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<FxHasher>>;
type HashSet<K> = hashbrown::HashSet<K, BuildHasherDefault<FxHasher>>;
