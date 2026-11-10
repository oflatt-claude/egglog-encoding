//! Push equivariance through ordinary equality steps, sharing each transported
//! subproof, and remove reflexive scaffolding. Source steps retain their checked
//! instantiations; any remaining equivariance is immediately above a source step.

use super::HashMap;
use super::format::{ProofId, RulePremise, SlottedProof, SlottedProofStore};
use super::terms::{Renaming, all_slots, rename, slot_of};
use egglog::proof::{Justification as Step, Proposition};
use egglog::{Term, TermDag, TermId};
use std::collections::BTreeSet;

type Key = (ProofId, Renaming);

/// Shared endpoints are renamed repeatedly through different proof steps.
/// Both caches belong to this normalization pass and use immutable term IDs.
#[derive(Default)]
struct TermRenamings {
    slots: HashMap<TermId, BTreeSet<i64>>,
    renamed: HashMap<(TermId, Renaming), TermId>,
}

impl TermRenamings {
    fn slots(&mut self, dag: &TermDag, term: TermId) -> &BTreeSet<i64> {
        self.slots
            .entry(term)
            .or_insert_with(|| all_slots(dag, term))
    }

    fn restrict(&mut self, dag: &TermDag, rho: &Renaming, lhs: TermId, rhs: TermId) -> Renaming {
        if rho.is_identity() {
            return rho.clone();
        }
        self.slots(dag, lhs);
        self.slots(dag, rhs);
        Renaming::completing(
            rho.entries().filter(|(slot, _)| {
                self.slots[&lhs].contains(slot) || self.slots[&rhs].contains(slot)
            }),
        )
        .expect("restricting a permutation keeps it injective")
    }

    fn rename(&mut self, dag: &mut TermDag, rho: &Renaming, term: TermId) -> TermId {
        if rho.is_identity() {
            return term;
        }
        let rho = rho.restricted(self.slots(dag, term));
        if rho.is_identity() {
            return term;
        }
        *self
            .renamed
            .entry((term, rho.clone()))
            .or_insert_with(|| rename(dag, &rho, term))
    }
}

impl SlottedProofStore {
    /// Normalize an already checked proof. Check the resulting proof again before
    /// using it, just as for any other proof transformation.
    pub fn simplify(&mut self, root: ProofId) -> ProofId {
        let mut terms = TermRenamings::default();
        // Only the action on a step's endpoints matters. Keeping unrelated
        // coordinates in the memo key can expand a shared proof exponentially
        // when it is reached through different binder-renaming paths.
        let root = (root, Renaming::identity());
        let mut memo = HashMap::<Key, ProofId>::default();
        let mut work = vec![(root.clone(), false)];
        while let Some(((id, rho), ready)) = work.pop() {
            let key = (id, rho.clone());
            if memo.contains_key(&key) {
                continue;
            }
            let proof = self.get(id);
            let children: Vec<Key> = match proof {
                SlottedProof::Equivariance {
                    proof, renaming, ..
                } => vec![(*proof, rho.compose(renaming))],
                SlottedProof::Rule(_) => proof
                    .premises()
                    .into_iter()
                    .map(|p| (p, Renaming::identity()))
                    .collect(),
                _ => proof
                    .premises()
                    .into_iter()
                    .map(|p| (p, rho.clone()))
                    .collect(),
            }
            .into_iter()
            .map(|(id, rho)| {
                let p = self.proposition(id);
                (id, terms.restrict(&self.term_dag, &rho, p.lhs, p.rhs))
            })
            .collect();
            if !ready {
                work.push((key, true));
                work.extend(children.into_iter().rev().map(|k| (k, false)));
                continue;
            }
            let children: Vec<_> = children.iter().map(|k| memo[k]).collect();
            let result = match self.get(id).clone() {
                SlottedProof::Rule(mut proof) => {
                    let normalized = |p| memo[&(p, Renaming::identity())];
                    proof.premises = proof
                        .premises
                        .into_iter()
                        .map(|p| match p {
                            RulePremise::Equality(p) => RulePremise::Equality(normalized(p)),
                            RulePremise::RenamingEq { left, right } => RulePremise::RenamingEq {
                                left: normalized(left),
                                right: normalized(right),
                            },
                        })
                        .collect();
                    self.simplify_source(SlottedProof::Rule(proof), &rho, &mut terms)
                }
                SlottedProof::Equivariance { .. } => children[0],
                SlottedProof::Alpha { proposition, .. } => {
                    let rhs = terms.rename(&mut self.term_dag, &rho, proposition.rhs);
                    if rhs == self.proposition(children[0]).rhs {
                        children[0]
                    } else {
                        self.alpha(children[0], rhs)
                    }
                }
                SlottedProof::Ordinary(proof) => match proof.justification() {
                    Step::Sym(_) => self.simple_sym(children[0]),
                    Step::Proj { child_index, .. } => self
                        .project(children[0], *child_index)
                        .expect("normalizing preserves projected children"),
                    Step::Trans(..) => {
                        let (a, b) = (children[0], children[1]);
                        if self.reflexive(a) {
                            b
                        } else if self.reflexive(b) {
                            a
                        } else {
                            self.trans(a, b)
                                .expect("normalizing preserves middle terms")
                        }
                    }
                    Step::Congr { child_index, .. } => {
                        if self.reflexive(children[1]) {
                            children[0]
                        } else {
                            self.congr(children[0], *child_index, children[1])
                                .expect("normalizing preserves child terms")
                        }
                    }
                    Step::Fiat => {
                        self.simplify_source(SlottedProof::Ordinary(proof), &rho, &mut terms)
                    }
                    _ => unreachable!("normalization requires a checked slotted proof"),
                },
            };
            memo.insert(key, result);
            if memo.len().is_multiple_of(1_000_000) {
                log::debug!(
                    "normalized {} proof contexts into {} steps and {} terms ({} cached renamings)",
                    memo.len(),
                    self.len(),
                    self.term_dag.size(),
                    terms.renamed.len(),
                );
            }
        }
        memo[&root]
    }

    fn simplify_source(
        &mut self,
        proof: SlottedProof,
        rho: &Renaming,
        terms: &mut TermRenamings,
    ) -> ProofId {
        let p = proof.proposition();
        let lhs = terms.rename(&mut self.term_dag, rho, p.lhs);
        let rhs = terms.rename(&mut self.term_dag, rho, p.rhs);
        if lhs == rhs
            && (slot_of(&self.term_dag, lhs).is_some()
                || matches!(self.term_dag.get(lhs), Term::Lit(_)))
        {
            return self.fiat(lhs, rhs);
        }
        let unchanged = (lhs, rhs) == (p.lhs, p.rhs);
        let source = self.add(proof);
        if unchanged {
            source
        } else {
            // The work key already restricts rho to these endpoints. Reuse the
            // terms computed above instead of traversing both trees again.
            self.add(SlottedProof::Equivariance {
                proposition: Proposition::new(lhs, rhs),
                proof: source,
                renaming: rho.clone(),
            })
        }
    }

    fn reflexive(&self, p: ProofId) -> bool {
        let p = self.proposition(p);
        p.lhs == p.rhs
    }

    fn simple_sym(&mut self, p: ProofId) -> ProofId {
        if self.reflexive(p) {
            p
        } else if let SlottedProof::Ordinary(proof) = self.get(p)
            && let Step::Sym(inner) = proof.justification()
        {
            *inner
        } else {
            self.sym(p)
        }
    }
}

#[cfg(test)]
#[path = "tests/normalize.rs"]
mod tests;
