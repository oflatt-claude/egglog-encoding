//! The slotted proof format: propositions `lhs = m·rhs` over surface terms and the
//! justifications of `slotted/PROOFS.md`, in a hash-consed store.

use super::terms::{Renaming, all_slots, rename};
use crate::util::HashMap;
use crate::{Term, TermDag, TermId};
use std::fmt::Write;

/// An index into a [`SlottedProofStore`].
pub type SlottedProofId = usize;

/// `lhs = renaming·rhs`: the left term equals the right term with its slots
/// renamed.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SlottedProposition {
    pub lhs: TermId,
    pub renaming: Renaming,
    pub rhs: TermId,
}

impl SlottedProposition {
    pub fn new(lhs: TermId, renaming: Renaming, rhs: TermId) -> Self {
        Self { lhs, renaming, rhs }
    }

    pub fn equal(lhs: TermId, rhs: TermId) -> Self {
        Self::new(lhs, Renaming::identity(), rhs)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SlottedJustification {
    /// A term the program built, or a source `union`.
    Fiat,
    /// A rewrite instantiated by the substitution, given proofs of its premises:
    /// the root pattern first, then each `:when` equality pattern in order.
    Rule {
        name: String,
        substitution: Vec<(String, TermId)>,
        premises: Vec<SlottedProofId>,
    },
    Sym(SlottedProofId),
    Trans(SlottedProofId, SlottedProofId),
    Congr {
        proof: SlottedProofId,
        child_index: usize,
        child_proof: SlottedProofId,
    },
    /// The right-hand side renamed by a permutation, with the proposition's
    /// renaming adjusted to say the same thing.
    Shift {
        proof: SlottedProofId,
        renaming: Renaming,
    },
}

#[derive(Clone, Debug)]
pub struct SlottedProof {
    pub proposition: SlottedProposition,
    pub justification: SlottedJustification,
}

/// A hash-consed arena of slotted proofs over one [`TermDag`].
#[derive(Clone, Debug, Default)]
pub struct SlottedProofStore {
    pub term_dag: TermDag,
    proofs: Vec<SlottedProof>,
    index: HashMap<(SlottedProposition, SlottedJustification), SlottedProofId>,
}

/// Why a derived step could not be formed from its inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MalformedStep(pub String);

impl SlottedProofStore {
    pub fn new(term_dag: TermDag) -> Self {
        Self {
            term_dag,
            ..Default::default()
        }
    }

    pub fn len(&self) -> usize {
        self.proofs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.proofs.is_empty()
    }

    pub fn get(&self, id: SlottedProofId) -> &SlottedProof {
        &self.proofs[id]
    }

    pub fn proposition(&self, id: SlottedProofId) -> &SlottedProposition {
        &self.proofs[id].proposition
    }

    /// The proposition with its renaming restricted to the slots of its right-hand
    /// side: renamings that agree there describe the same renamed term.
    pub fn normalize(&self, p: SlottedProposition) -> SlottedProposition {
        let slots = all_slots(&self.term_dag, p.rhs);
        SlottedProposition::new(p.lhs, p.renaming.restricted(&slots), p.rhs)
    }

    /// Record a proof as stated. The checker decides whether it is valid. The
    /// renaming is kept whole, not restricted to the right-hand side's slots:
    /// a derived step composes it with others, and where their images leave
    /// the right-hand side's slots the whole permutation says what it means.
    pub fn add(
        &mut self,
        proposition: SlottedProposition,
        justification: SlottedJustification,
    ) -> SlottedProofId {
        let key = (proposition, justification);
        if let Some(&id) = self.index.get(&key) {
            return id;
        }
        let id = self.proofs.len();
        self.proofs.push(SlottedProof {
            proposition: key.0.clone(),
            justification: key.1.clone(),
        });
        self.index.insert(key, id);
        id
    }

    pub fn fiat(&mut self, lhs: TermId, rhs: TermId) -> SlottedProofId {
        self.add(
            SlottedProposition::equal(lhs, rhs),
            SlottedJustification::Fiat,
        )
    }

    /// `t2 = m⁻¹·t1` from `t1 = m·t2`.
    pub fn sym(&mut self, proof: SlottedProofId) -> SlottedProofId {
        let p = self.proposition(proof).clone();
        self.add(
            SlottedProposition::new(p.rhs, p.renaming.inverse(), p.lhs),
            SlottedJustification::Sym(proof),
        )
    }

    /// `t1 = (m∘n)·t3` from `t1 = m·t2` and `t2 = n·t3`.
    pub fn trans(
        &mut self,
        left: SlottedProofId,
        right: SlottedProofId,
    ) -> Result<SlottedProofId, MalformedStep> {
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
        Ok(self.add(
            SlottedProposition::new(l.lhs, l.renaming.compose(&r.renaming), r.rhs),
            SlottedJustification::Trans(left, right),
        ))
    }

    /// `t1 = m·F(.., n·c', ..)` from `t1 = m·F(.., c, ..)` and `c = n·c'`.
    pub fn congr(
        &mut self,
        proof: SlottedProofId,
        child_index: usize,
        child_proof: SlottedProofId,
    ) -> Result<SlottedProofId, MalformedStep> {
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
        let renamed_child = rename(&mut self.term_dag, &c.renaming, c.rhs);
        let mut children = children;
        children[child_index] = renamed_child;
        let rhs = self.term_dag.app(head, children);
        Ok(self.add(
            SlottedProposition::new(p.lhs, p.renaming, rhs),
            SlottedJustification::Congr {
                proof,
                child_index,
                child_proof,
            },
        ))
    }

    /// `t1 = (m∘σ⁻¹)·(σ·t2)` from `t1 = m·t2`.
    pub fn shift(&mut self, proof: SlottedProofId, sigma: Renaming) -> SlottedProofId {
        if sigma.is_identity() {
            return proof;
        }
        let p = self.proposition(proof).clone();
        let rhs = rename(&mut self.term_dag, &sigma, p.rhs);
        self.add(
            SlottedProposition::new(p.lhs, p.renaming.compose(&sigma.inverse()), rhs),
            SlottedJustification::Shift {
                proof,
                renaming: sigma,
            },
        )
    }

    /// The proofs `root` depends on, dependencies first, `root` last.
    pub fn dependencies(&self, root: SlottedProofId) -> Vec<SlottedProofId> {
        let mut order = vec![];
        let mut state: HashMap<SlottedProofId, bool> = HashMap::default();
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
            for dep in self.children(id) {
                if !state.contains_key(&dep) {
                    stack.push((dep, false));
                }
            }
        }
        order
    }

    pub fn children(&self, id: SlottedProofId) -> Vec<SlottedProofId> {
        match &self.proofs[id].justification {
            SlottedJustification::Fiat => vec![],
            SlottedJustification::Rule { premises, .. } => premises.clone(),
            SlottedJustification::Sym(p) | SlottedJustification::Shift { proof: p, .. } => vec![*p],
            SlottedJustification::Trans(a, b) => vec![*a, *b],
            SlottedJustification::Congr {
                proof, child_proof, ..
            } => vec![*proof, *child_proof],
        }
    }

    /// The proposition printed with its renaming restricted to the slots it
    /// acts on.
    pub fn proposition_to_string(&self, p: &SlottedProposition) -> String {
        let p = self.normalize(p.clone());
        let lhs = self.term_dag.to_string(p.lhs);
        let rhs = self.term_dag.to_string(p.rhs);
        if p.renaming.is_identity() {
            format!("{lhs} = {rhs}")
        } else {
            format!("{lhs} = {}·{rhs}", p.renaming)
        }
    }

    /// The proof and everything it depends on, one numbered line each, in
    /// dependency order.
    pub fn proof_to_string(&self, root: SlottedProofId) -> String {
        let order = self.dependencies(root);
        let number: HashMap<SlottedProofId, usize> =
            order.iter().enumerate().map(|(n, &id)| (id, n)).collect();
        let mut out = String::new();
        for &id in &order {
            let proof = &self.proofs[id];
            let _ = write!(
                out,
                "#{}: {}",
                number[&id],
                self.proposition_to_string(&proof.proposition)
            );
            let _ = match &proof.justification {
                SlottedJustification::Fiat => writeln!(out, "\n    by fiat"),
                SlottedJustification::Rule {
                    name,
                    substitution,
                    premises,
                } => {
                    let subst: Vec<String> = substitution
                        .iter()
                        .map(|(v, t)| format!("{v} := {}", self.term_dag.to_string(*t)))
                        .collect();
                    let prems: Vec<String> =
                        premises.iter().map(|p| format!("#{}", number[p])).collect();
                    writeln!(
                        out,
                        "\n    by rule {name:?} [{}] from {}",
                        subst.join(", "),
                        if prems.is_empty() {
                            "nothing".to_string()
                        } else {
                            prems.join(" ")
                        }
                    )
                }
                SlottedJustification::Sym(p) => writeln!(out, "\n    by sym #{}", number[p]),
                SlottedJustification::Trans(a, b) => {
                    writeln!(out, "\n    by trans #{} #{}", number[a], number[b])
                }
                SlottedJustification::Congr {
                    proof,
                    child_index,
                    child_proof,
                } => writeln!(
                    out,
                    "\n    by congr #{} at {child_index} with #{}",
                    number[proof], number[child_proof]
                ),
                SlottedJustification::Shift { proof, renaming } => {
                    writeln!(out, "\n    by shift #{} by {renaming}", number[proof])
                }
            };
        }
        out
    }
}
