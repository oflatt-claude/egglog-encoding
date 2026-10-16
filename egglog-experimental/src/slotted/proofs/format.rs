//! The slotted proof format: propositions `lhs = m·rhs` over surface terms and the
//! justifications of `slotted/PROOFS.md`, in a hash-consed store.

use super::HashMap;
use super::terms::{Renaming, all_slots, rename, slot_of};
use egglog::{Term, TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

/// An index into a [`SlottedProofStore`].
pub type SlottedProofId = usize;

/// `lhs = renaming·rhs`: the left term equals the right term with its slots
/// renamed.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SlottedProposition {
    /// The term on the left.
    pub lhs: TermId,
    /// The permutation applied to the right-hand term.
    pub renaming: Renaming,
    /// The term on the right, before renaming.
    pub rhs: TermId,
}

impl SlottedProposition {
    /// State an equality with an explicit right-hand renaming.
    pub fn new(lhs: TermId, renaming: Renaming, rhs: TermId) -> Self {
        Self { lhs, renaming, rhs }
    }

    /// State an equality with the identity renaming.
    pub fn equal(lhs: TermId, rhs: TermId) -> Self {
        Self::new(lhs, Renaming::identity(), rhs)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// A source axiom, rewrite application, or operation on earlier proof steps.
pub enum SlottedJustification {
    /// A term the program built, or a source `union`.
    Fiat,
    /// A rewrite instantiated by the substitution, given proofs of its premises:
    /// the root pattern first, then each `:when` equality pattern in order.
    Rule {
        /// The source rewrite's name.
        name: String,
        /// Source variables and the terms substituted for them.
        substitution: Vec<(String, TermId)>,
        /// Proofs of the rewrite's pattern premises, in source order.
        premises: Vec<SlottedProofId>,
    },
    /// Reverse an equality and invert its renaming.
    Sym(SlottedProofId),
    /// Compose equalities with matching middle terms.
    Trans(SlottedProofId, SlottedProofId),
    /// Replace one right-hand child using an equality proof.
    Congr {
        /// The equality whose right-hand term is updated.
        proof: SlottedProofId,
        /// The child's zero-based surface column.
        child_index: usize,
        /// The equality used to replace the child.
        child_proof: SlottedProofId,
    },
    /// The right-hand side renamed by a permutation, with the proposition's
    /// renaming adjusted to say the same thing.
    Shift {
        /// The equality being restated.
        proof: SlottedProofId,
        /// The permutation applied to its right-hand term.
        renaming: Renaming,
    },
}

#[derive(Clone, Debug)]
/// A proposition together with the step that justifies it.
pub struct SlottedProof {
    /// The equality stated by this step.
    pub proposition: SlottedProposition,
    /// How it follows from the source program or earlier steps.
    pub justification: SlottedJustification,
}

/// A hash-consed arena of slotted proofs over one [`TermDag`].
#[derive(Clone, Debug, Default)]
pub struct SlottedProofStore {
    /// Shared storage for source terms and instantiated terms.
    pub term_dag: TermDag,
    slot_names: BTreeMap<i64, String>,
    proofs: Vec<SlottedProof>,
    index: HashMap<(SlottedProposition, SlottedJustification), SlottedProofId>,
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
    pub fn get(&self, id: SlottedProofId) -> &SlottedProof {
        &self.proofs[id]
    }

    /// The proposition stated by a stored proof step.
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

    /// State a source union or a built term's reflexivity; the checker validates it.
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

    /// The immediate proof dependencies of a step.
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
        self.named_proposition(
            p,
            &self.display_names(p.renaming.entries().flat_map(|(a, b)| [a, b])),
        )
    }

    /// One injective naming for all terms and permutations, including coordinates
    /// that occur only in a Shift. Reserve rule-local variables as well as source slots.
    fn display_names(&self, extra: impl IntoIterator<Item = i64>) -> BTreeMap<i64, String> {
        let mut names = self.slot_names.clone();
        let mut used: BTreeSet<String> = names.values().cloned().collect();
        for t in 0..self.term_dag.size() {
            if let Term::Var(v) = self.term_dag.get(t) {
                used.insert(format!("${}", v.trim_start_matches('$')));
            }
        }
        let mut slots = (0..self.term_dag.size())
            .filter_map(|t| slot_of(&self.term_dag, t))
            .collect::<Vec<_>>();
        for proof in &self.proofs {
            slots.extend(
                proof
                    .proposition
                    .renaming
                    .entries()
                    .flat_map(|(a, b)| [a, b]),
            );
            match &proof.justification {
                SlottedJustification::Shift { renaming, .. } => {
                    slots.extend(renaming.entries().flat_map(|(a, b)| [a, b]));
                }
                SlottedJustification::Rule { substitution, .. } => {
                    used.extend(
                        substitution
                            .iter()
                            .map(|(v, _)| format!("${}", v.trim_start_matches('$'))),
                    );
                }
                _ => {}
            }
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

    fn named_renaming(renaming: &Renaming, names: &BTreeMap<i64, String>) -> String {
        format!(
            "{{{}}}",
            renaming
                .entries()
                .map(|(a, b)| {
                    format!(
                        "{}->{}",
                        names[&a].trim_start_matches('$'),
                        names[&b].trim_start_matches('$')
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn named_proposition(&self, p: &SlottedProposition, names: &BTreeMap<i64, String>) -> String {
        let p = self.normalize(p.clone());
        let lhs = self.named_term(p.lhs, names);
        let rhs = self.named_term(p.rhs, names);
        if p.renaming.is_identity() {
            format!("{lhs} = {rhs}")
        } else {
            format!("{lhs} = {}·{rhs}", Self::named_renaming(&p.renaming, names))
        }
    }

    /// The proof and everything it depends on, one numbered line each, in
    /// dependency order.
    pub fn proof_to_string(&self, root: SlottedProofId) -> String {
        let order = self.dependencies(root);
        let names = self.display_names([]);
        let number: HashMap<SlottedProofId, usize> =
            order.iter().enumerate().map(|(n, &id)| (id, n)).collect();
        let mut out = String::new();
        for &id in &order {
            let proof = &self.proofs[id];
            let _ = write!(
                out,
                "#{}: {}",
                number[&id],
                self.named_proposition(&proof.proposition, &names)
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
                        .map(|(v, t)| format!("{v} := {}", self.named_term(*t, &names)))
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
                    writeln!(
                        out,
                        "\n    by shift #{} by {}",
                        number[proof],
                        Self::named_renaming(renaming, &names)
                    )
                }
            };
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slotted::proofs::terms::slot_term;

    #[test]
    fn fresh_display_names_cover_permutation_only_coordinates() {
        let mut dag = TermDag::default();
        let a = slot_term(&mut dag, 10);
        dag.var("v1".into());
        let mut store = SlottedProofStore::new(dag)
            .with_slot_names(&BTreeMap::from([("$a".into(), 10), ("$v0".into(), 20)]));
        let refl = store.fiat(a, a);
        let proof = store.shift(refl, Renaming::new([(30, 31), (31, 30)]).unwrap());
        assert_eq!(
            store.proof_to_string(proof),
            "#0: $a = $a\n    by fiat\n#1: $a = $a\n    by shift #0 by {v2->v3, v3->v2}\n"
        );
    }
}
