//! Surface proofs for slotted programs, their checker, and translation from
//! encoded egglog proofs. See `egglog-experimental/src/slotted/PROOFS.md` for
//! the proof format and translation rules.

pub mod checker;
pub mod format;
mod lifting;
mod normalize;
pub(crate) mod pipeline;
pub mod source;
pub mod terms;
pub(crate) mod translate;

pub use checker::{Checked, SlottedCheckError, check_claim, check_proof};
pub use format::{
    SlottedConclusion, SlottedJustification, SlottedProof, SlottedProofId, SlottedProofStore,
    SlottedProposition,
};
pub use source::{Claim, ClaimKind, Condition, Constructor, Rewrite, Rhs, SlottedProgram, Union};
pub use terms::Renaming;

type HashMap<K, V> = hashbrown::HashMap<K, V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
type HashSet<K> = hashbrown::HashSet<K, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
