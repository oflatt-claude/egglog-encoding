//! Ordinary equalities over slotted surface terms and their justifications.

use super::HashMap;
use super::terms::{Renaming, all_slots, rename, slot_of};
pub use egglog::proof::ProofId;
use egglog::proof::{Justification, Proof, Proposition, proof_term_to_string};
use egglog::{Term, TermDag, TermId};
use egglog_numeric_id::NumericId;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Whether a claim fixes free slots or permits a renaming between its sides.
pub enum ClaimKind {
    /// `(= a b)`: the same invocation.
    Eq,
    /// `(renaming-= a b)`: the same class under some renaming.
    RenamingEq,
}

/// A `prove-slotted`'s claim over source terms.
#[derive(Clone, Debug)]
pub struct Claim {
    /// The requested notion of equality.
    pub kind: ClaimKind,
    /// The carrier sort the two terms belong to.
    pub sort: String,
    /// The claim's left source term.
    pub lhs: TermId,
    /// The claim's right source term.
    pub rhs: TermId,
}

/// An ordinary proof of `lhs = rename(renaming, rhs)` for a surface claim.
/// The witness belongs to the claim, not to the proof's equality propositions.
#[derive(Clone, Debug)]
pub struct SlottedConclusion {
    /// The ordinary equality proof.
    pub proof: ProofId,
    /// How the requested right-hand term is named in the proof.
    pub renaming: Renaming,
}

/// An ordinary egglog proof step, or a slotted equality extension.
/// Every premise ID refers to the same [`SlottedProofStore`].
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SlottedProof {
    /// A step in egglog's ordinary proof format.
    Ordinary(Proof),
    /// Replace the right endpoint of a checked equality by an alpha-equivalent term.
    Alpha {
        /// The equality stated by this step.
        proposition: Proposition,
        /// The equality whose right endpoint is changed.
        proof: ProofId,
    },
    /// Apply a finite slot permutation to both endpoints of a checked equality.
    Equivariance {
        /// The equality stated by this step.
        proposition: Proposition,
        /// The equality being transported.
        proof: ProofId,
        /// The permutation applied to both endpoints.
        renaming: Renaming,
    },
}

impl SlottedProof {
    /// The ordinary equality stated by this step.
    pub fn proposition(&self) -> &Proposition {
        match self {
            Self::Ordinary(proof) => proof.proposition(),
            Self::Alpha { proposition, .. } | Self::Equivariance { proposition, .. } => proposition,
        }
    }

    /// Immediate proof dependencies in the same store.
    pub fn premises(&self) -> Vec<ProofId> {
        match self {
            Self::Ordinary(proof) => proof.justification().premises(),
            Self::Alpha { proof, .. } | Self::Equivariance { proof, .. } => vec![*proof],
        }
    }
}

/// Distinct slotted proof steps over one [`TermDag`].
#[derive(Clone, Debug, Default)]
pub struct SlottedProofStore {
    /// Shared storage for source terms and instantiated terms.
    pub term_dag: TermDag,
    slot_names: BTreeMap<i64, String>,
    proofs: Vec<SlottedProof>,
    index: HashMap<SlottedProof, ProofId>,
}

/// Why a derived step could not be formed from its inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MalformedStep(pub String);

impl SlottedProofStore {
    /// Start a proof store over an existing term dag.
    pub fn new(term_dag: TermDag) -> Self {
        Self {
            slot_names: (0..term_dag.size())
                .filter_map(|t| slot_of(&term_dag, t))
                .map(|s| (s, format!("${s}")))
                .collect(),
            term_dag,
            ..Default::default()
        }
    }

    /// Use the compiler's source spellings when displaying encoded slot IDs.
    pub fn with_slot_names(mut self, names: &BTreeMap<String, i64>) -> Self {
        self.slot_names = names.iter().map(|(name, &id)| (id, name.clone())).collect();
        self
    }

    /// The number of distinct proof steps stored.
    pub fn len(&self) -> usize {
        self.proofs.len()
    }

    /// Whether the store contains no proof steps.
    pub fn is_empty(&self) -> bool {
        self.proofs.is_empty()
    }

    /// Look up a proof step by its store-local index.
    pub fn get(&self, id: ProofId) -> &SlottedProof {
        &self.proofs[id.index()]
    }

    /// The proposition stated by a stored proof step.
    pub fn proposition(&self, id: ProofId) -> &Proposition {
        self.proofs[id.index()].proposition()
    }

    /// Record a proof as stated. The checker decides whether it is valid.
    pub fn add(&mut self, proof: SlottedProof) -> ProofId {
        if let Some(&id) = self.index.get(&proof) {
            return id;
        }
        let id = ProofId::from_usize(self.proofs.len());
        self.proofs.push(proof.clone());
        self.index.insert(proof, id);
        id
    }

    /// Record an ordinary egglog step whose premises refer to this store.
    pub fn ordinary(&mut self, proposition: Proposition, justification: Justification) -> ProofId {
        self.add(SlottedProof::Ordinary(Proof::new(
            proposition,
            justification,
        )))
    }

    /// State a source union or a built term's reflexivity; the checker validates it.
    pub fn fiat(&mut self, lhs: TermId, rhs: TermId) -> ProofId {
        self.ordinary(Proposition::new(lhs, rhs), Justification::Fiat)
    }

    /// Reverse the endpoints of an equality.
    pub fn sym(&mut self, proof: ProofId) -> ProofId {
        let p = self.proposition(proof).clone();
        self.ordinary(Proposition::new(p.rhs, p.lhs), Justification::Sym(proof))
    }

    /// State an alpha-conversion of the right endpoint; the checker validates it.
    pub fn alpha(&mut self, proof: ProofId, rhs: TermId) -> ProofId {
        let lhs = self.proposition(proof).lhs;
        self.add(SlottedProof::Alpha {
            proposition: Proposition::new(lhs, rhs),
            proof,
        })
    }

    /// Compose equalities whose middle terms match exactly.
    pub fn trans(&mut self, left: ProofId, right: ProofId) -> Result<ProofId, MalformedStep> {
        let (l, r) = (
            self.proposition(left).clone(),
            self.proposition(right).clone(),
        );
        if l.rhs != r.lhs {
            return Err(MalformedStep(format!(
                "trans: middle terms differ: {} vs {}",
                self.term_dag.to_string(l.rhs),
                self.term_dag.to_string(r.lhs)
            )));
        }
        Ok(self.ordinary(
            Proposition::new(l.lhs, r.rhs),
            Justification::Trans(left, right),
        ))
    }

    /// Replace a child using an ordinary equality `c = c'`.
    pub fn congr(
        &mut self,
        proof: ProofId,
        child_index: usize,
        child_proof: ProofId,
    ) -> Result<ProofId, MalformedStep> {
        let p = self.proposition(proof).clone();
        let c = self.proposition(child_proof).clone();
        let Term::App(head, children) = self.term_dag.get(p.rhs).clone() else {
            return Err(MalformedStep(
                "congr: right-hand side is not an application".into(),
            ));
        };
        let Some(&child) = children.get(child_index) else {
            return Err(MalformedStep(format!("congr: no child {child_index}")));
        };
        if child != c.lhs {
            return Err(MalformedStep(format!(
                "congr: child {} is not the child proof's left side {}",
                self.term_dag.to_string(child),
                self.term_dag.to_string(c.lhs)
            )));
        }
        let mut children = children;
        children[child_index] = c.rhs;
        let rhs = self.term_dag.app(head, children);
        Ok(self.ordinary(
            Proposition::new(p.lhs, rhs),
            Justification::Congr {
                proof,
                child_index,
                child_proof,
            },
        ))
    }

    /// Derive `sigma(lhs) = sigma(rhs)` by equivariance of the slotted theory.
    pub fn equivariance(&mut self, proof: ProofId, sigma: Renaming) -> ProofId {
        if sigma.is_identity() {
            return proof;
        }
        let p = self.proposition(proof).clone();
        let lhs = rename(&mut self.term_dag, &sigma, p.lhs);
        let rhs = rename(&mut self.term_dag, &sigma, p.rhs);
        self.add(SlottedProof::Equivariance {
            proposition: Proposition::new(lhs, rhs),
            proof,
            renaming: sigma,
        })
    }

    /// Establish that a child of the proved right-hand term exists.
    pub fn project(
        &mut self,
        proof: ProofId,
        child_index: usize,
    ) -> Result<ProofId, MalformedStep> {
        let Term::App(_, children) = self.term_dag.get(self.proposition(proof).rhs) else {
            return Err(MalformedStep("projection needs an application".into()));
        };
        let child = *children
            .get(child_index)
            .ok_or_else(|| MalformedStep("projection index out of bounds".into()))?;
        Ok(self.ordinary(
            Proposition::new(child, child),
            Justification::Proj { proof, child_index },
        ))
    }

    /// The proofs `root` depends on, dependencies first, `root` last.
    pub fn dependencies(&self, root: ProofId) -> Vec<ProofId> {
        let mut order = vec![];
        let mut state: HashMap<ProofId, bool> = HashMap::default();
        let mut stack = vec![(root, false)];
        while let Some((id, children_done)) = stack.pop() {
            if children_done {
                order.push(id);
                state.insert(id, true);
                continue;
            }
            if state.contains_key(&id) {
                continue;
            }
            state.insert(id, false);
            stack.push((id, true));
            for dep in self.get(id).premises() {
                if !state.contains_key(&dep) {
                    stack.push((dep, false));
                }
            }
        }
        order
    }

    /// Display an ordinary equality in source slot names.
    pub fn proposition_to_string(&self, p: &Proposition) -> String {
        self.named_proposition(p, &self.display_names(None, []))
    }

    /// Name terms and permutation coordinates without colliding with source slots
    /// or rule variables.
    fn display_names(
        &self,
        root: Option<ProofId>,
        extra: impl IntoIterator<Item = i64>,
    ) -> BTreeMap<i64, String> {
        let mut names = self.slot_names.clone();
        let mut used: BTreeSet<String> = names.values().cloned().collect();
        for t in 0..self.term_dag.size() {
            if let Term::Var(v) = self.term_dag.get(t) {
                used.insert(format!("${}", v.trim_start_matches('$')));
            }
        }
        let mut slots = vec![];
        let ids = root
            .map(|p| self.dependencies(p))
            .unwrap_or_else(|| (0..self.len()).map(ProofId::from_usize).collect());
        for id in ids {
            let proof = self.get(id);
            let proposition = proof.proposition();
            let mut terms = vec![proposition.rhs, proposition.lhs];
            match proof {
                SlottedProof::Equivariance { renaming, .. } => {
                    slots.extend(renaming.entries().flat_map(|(a, b)| [a, b]));
                }
                SlottedProof::Ordinary(proof) => {
                    if let Justification::Rule { substitution, .. } = proof.justification() {
                        used.extend(
                            substitution
                                .keys()
                                .map(|v| format!("${}", v.trim_start_matches('$'))),
                        );
                        terms.extend(substitution.values().rev().copied());
                    }
                }
                SlottedProof::Alpha { .. } => {}
            }
            while let Some(term) = terms.pop() {
                if let Some(slot) = slot_of(&self.term_dag, term) {
                    slots.push(slot);
                } else if let Term::App(_, children) = self.term_dag.get(term) {
                    terms.extend(children.iter().rev().copied());
                }
            }
        }
        if root.is_none() {
            slots.extend((0..self.term_dag.size()).filter_map(|t| slot_of(&self.term_dag, t)));
        }
        let mut next = 0;
        for slot in slots.into_iter().chain(extra) {
            names.entry(slot).or_insert_with(|| {
                loop {
                    let name = format!("$v{next}");
                    next += 1;
                    if used.insert(name.clone()) {
                        break name;
                    }
                }
            });
        }
        names
    }

    fn named_term(&self, term: TermId, names: &BTreeMap<i64, String>) -> String {
        if let Some(slot) = slot_of(&self.term_dag, term) {
            return names[&slot].clone();
        }
        match self.term_dag.get(term) {
            Term::App(head, children) if !children.is_empty() => format!(
                "({head} {})",
                children
                    .iter()
                    .map(|&c| self.named_term(c, names))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            _ => self.term_dag.to_string(term),
        }
    }

    fn named_dag(&self, names: &BTreeMap<i64, String>) -> (TermDag, Vec<TermId>) {
        let mut dag = TermDag::default();
        let mut terms = Vec::with_capacity(self.term_dag.size());
        for id in 0..self.term_dag.size() {
            let term = match self.term_dag.get(id) {
                Term::Var(v) => dag.var(
                    slot_of(&self.term_dag, id)
                        .and_then(|slot| names.get(&slot))
                        .unwrap_or(v)
                        .clone(),
                ),
                Term::Lit(lit) => dag.lit(lit.clone()),
                Term::App(head, children) => dag.app(
                    head.clone(),
                    children.iter().map(|&child| terms[child]).collect(),
                ),
            };
            terms.push(term);
        }
        (dag, terms)
    }

    fn renaming_term(
        dag: &mut TermDag,
        renaming: &Renaming,
        names: &BTreeMap<i64, String>,
    ) -> TermId {
        let entries = renaming
            .entries()
            .map(|(a, b)| {
                let target = dag.var(names[&b].clone());
                dag.app(names[&a].clone(), vec![target])
            })
            .collect();
        dag.app("renaming".into(), entries)
    }

    fn named_proposition(&self, p: &Proposition, names: &BTreeMap<i64, String>) -> String {
        format!(
            "{} = {}",
            self.named_term(p.lhs, names),
            self.named_term(p.rhs, names)
        )
    }

    /// Print a proof in egglog's S-expression format, with source slot names.
    pub fn proof_to_string(&self, root: ProofId) -> String {
        let names = self.display_names(Some(root), []);
        let (mut dag, terms) = self.named_dag(&names);
        let proof = self.proof_term(root, &mut dag, &terms, &names);
        proof_term_to_string(&dag, proof)
    }

    fn proof_term(
        &self,
        root: ProofId,
        dag: &mut TermDag,
        terms: &[TermId],
        names: &BTreeMap<i64, String>,
    ) -> TermId {
        let mut proofs = HashMap::default();
        for id in self.dependencies(root) {
            let proof = self.get(id);
            let proposition = proof.proposition();
            let equality = dag.app(
                "=".into(),
                vec![terms[proposition.lhs], terms[proposition.rhs]],
            );
            let term = match proof {
                SlottedProof::Ordinary(proof) => {
                    proof.to_term(dag, |t| terms[t], |_, id| proofs[&id])
                }
                SlottedProof::Alpha { proof, .. } => {
                    dag.app("Alpha".into(), vec![equality, proofs[proof]])
                }
                SlottedProof::Equivariance {
                    proof, renaming, ..
                } => {
                    let renaming = Self::renaming_term(dag, renaming, names);
                    dag.app(
                        "Equivariance".into(),
                        vec![equality, proofs[proof], renaming],
                    )
                }
            };
            proofs.insert(id, term);
        }
        proofs[&root]
    }

    /// Print the proof, wrapped in a `Claim` when a renaming witness is needed.
    pub fn conclusion_to_string(&mut self, conclusion: &SlottedConclusion) -> String {
        let p = self.proposition(conclusion.proof).clone();
        let rhs = rename(&mut self.term_dag, &conclusion.renaming.inverse(), p.rhs);
        let witness = conclusion
            .renaming
            .restricted(&all_slots(&self.term_dag, rhs));
        let names = self.display_names(
            Some(conclusion.proof),
            witness.entries().flat_map(|(a, b)| [a, b]),
        );
        let (mut dag, terms) = self.named_dag(&names);
        let mut proof = self.proof_term(conclusion.proof, &mut dag, &terms, &names);
        if rhs != p.rhs {
            let renaming = Self::renaming_term(&mut dag, &witness, &names);
            let rhs = dag.app("rename".into(), vec![renaming, terms[rhs]]);
            let equality = dag.app("=".into(), vec![terms[p.lhs], rhs]);
            proof = dag.app("Claim".into(), vec![equality, proof]);
        }
        proof_term_to_string(&dag, proof)
    }
}

#[cfg(test)]
#[path = "format_tests.rs"]
mod tests;
