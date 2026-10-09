//! Proofs for the slotted encoding: a proof format over the surface terms of
//! `slotted/LANGUAGE.md`, a checker for it against the slotted source program,
//! and the translation from egglog proofs over the encoded program. The format
//! and its rules are specified in `slotted/PROOFS.md`.

pub mod checker;
pub mod format;
pub mod pipeline;
pub mod source;
pub mod terms;
pub mod translate;

pub use checker::{SlottedCheckError, check_claim, check_proof};
pub use format::{
    SlottedJustification, SlottedProof, SlottedProofId, SlottedProofStore, SlottedProposition,
};
pub use pipeline::SlottedProofState;
pub use source::{Claim, ClaimKind, Condition, Constructor, Rewrite, Rhs, SlottedProgram};
pub use terms::Renaming;
