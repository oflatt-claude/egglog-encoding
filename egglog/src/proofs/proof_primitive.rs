//! Expand deferred primitive and global raw proofs into ordinary proof steps.
//! Primitive validators compute terms during lifting; they introduce no proof rule.

use super::proof_format::{
    Justification, Proof, ProofId, ProofStore, Proposition, RawProof, RawProofId, RawProofStore,
    SynthKey,
};
use super::proof_head::ProofAlgebra;
use crate::{
    Term, TermId,
    ast::ResolvedNCommand,
    util::{HashMap, HashSet},
};

impl ProofStore {
    /// Lift a primitive expression's certificate using its arguments and optional
    /// existence witness. Temporary primitive arguments are evaluated as terms.
    /// Errors if evaluation fails or the supplied evidence cannot certify the result.
    pub(super) fn lift_primitive(
        &mut self,
        program: &Vec<ResolvedNCommand>,
        globals: &HashMap<String, TermId>,
        raw: &RawProofStore,
        root: RawProofId,
    ) -> Result<ProofId, String> {
        let mut arguments = Vec::new();
        let endpoints = self.primitive_terms(
            program,
            globals,
            raw,
            root,
            &mut HashMap::default(),
            &mut arguments,
        )?;
        let RawProof::Primitive(_, _, witness) = raw.get(root) else {
            unreachable!()
        };
        let witness = witness
            .map(|proof| self.convert_raw_proof(program, globals, raw, proof))
            .transpose()?;
        let mut sources = arguments.clone();
        sources.extend(witness);
        let evidence = self.proof_dependencies(&sources);
        self.primitive_certificate(endpoints.lhs(), endpoints.rhs(), &arguments, &evidence)
    }

    /// Evaluate the source and leader terms, appending the ordinary argument
    /// certificates to `arguments`. Deferred primitive arguments need no existence
    /// witness here. Errors if an argument cannot be lifted or a validator fails.
    fn primitive_terms(
        &mut self,
        program: &Vec<ResolvedNCommand>,
        globals: &HashMap<String, TermId>,
        raw: &RawProofStore,
        proof: RawProofId,
        memo: &mut HashMap<RawProofId, Proposition>,
        arguments: &mut Vec<ProofId>,
    ) -> Result<Proposition, String> {
        if let Some(terms) = memo.get(&proof) {
            return Ok(terms.clone());
        }
        let endpoints = if let RawProof::Primitive(primitive, children, _) = raw.get(proof) {
            let children = children
                .iter()
                .map(|&child| self.primitive_terms(program, globals, raw, child, memo, arguments))
                .collect::<Result<Vec<_>, _>>()?;
            let left = children.iter().map(Proposition::lhs).collect::<Vec<_>>();
            let right = children.iter().map(Proposition::rhs).collect::<Vec<_>>();
            let validate = primitive
                .validator()
                .expect("ground primitives have validators");
            let left = validate(&mut self.term_dag, &left)
                .ok_or_else(|| format!("primitive {} failed validation", primitive.name()))?;
            let right = validate(&mut self.term_dag, &right).ok_or_else(|| {
                format!(
                    "primitive {} failed validation at leaders",
                    primitive.name()
                )
            })?;
            Proposition::new(left, right)
        } else {
            let proof = self.convert_raw_proof(program, globals, raw, proof)?;
            arguments.push(proof);
            self.get(proof).proposition().clone()
        };
        memo.insert(proof, endpoints.clone());
        Ok(endpoints)
    }

    /// Recover a global's source connector from its existing view evidence.
    /// Errors if the view and its dependencies contain no such connector.
    pub(super) fn lift_global(&mut self, source: TermId, row: ProofId) -> Result<ProofId, String> {
        let prop = self.get(row).proposition().clone();
        if prop.rhs() == source {
            return Ok(self.sym(row));
        }
        if prop.lhs() == source {
            let back = self.sym(row);
            return Ok(self.trans(row, back));
        }
        let evidence = self.proof_dependencies(&[row]);
        self.existing_equality(source, prop.lhs(), &evidence)
            .ok_or_else(|| "global view has no source connector".to_owned())
    }

    /// Existing proofs reachable from the supplied roots, excluding Eval markers.
    fn proof_dependencies(&self, roots: &[ProofId]) -> Vec<ProofId> {
        let mut pending = roots.iter().rev().copied().collect::<Vec<_>>();
        let mut seen = HashSet::default();
        let mut result = Vec::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            match self.get(id).justification() {
                Justification::Eval => continue,
                Justification::Fiat => {}
                Justification::Rule { premise_proofs, .. } => {
                    pending.extend(premise_proofs.iter().rev())
                }
                Justification::MergeFn {
                    old_proof,
                    new_proof,
                    ..
                } => pending.extend([*new_proof, *old_proof]),
                Justification::Trans(left, right) => pending.extend([*right, *left]),
                Justification::Sym(inner)
                | Justification::Proj { proof: inner, .. }
                | Justification::ContainerNormalize { proof: inner } => pending.push(*inner),
                Justification::Congr {
                    proof, child_proof, ..
                } => pending.extend([*child_proof, *proof]),
            }
            result.push(id);
        }
        result
    }

    /// Find the exact equality in either orientation among the supplied proofs.
    fn existing_equality(
        &mut self,
        left: TermId,
        right: TermId,
        evidence: &[ProofId],
    ) -> Option<ProofId> {
        for &id in evidence {
            let prop = self.get(id).proposition();
            if prop.lhs() == left && prop.rhs() == right {
                return Some(id);
            }
            if prop.rhs() == left && prop.lhs() == right {
                return Some(self.sym(id));
            }
        }
        None
    }

    /// Project an existence witness from an imported proof or its dependencies.
    fn existing_witness(&mut self, term: TermId, evidence: &[ProofId]) -> Option<ProofId> {
        for &id in evidence {
            let prop = self.get(id).proposition().clone();
            for (endpoint, reverse) in [(prop.rhs(), false), (prop.lhs(), true)] {
                let path = if endpoint == term {
                    Some(vec![])
                } else {
                    self.projection_path_to_descendant(endpoint, term)
                };
                if let Some(path) = path {
                    let mut proof = if reverse { self.sym(id) } else { id };
                    for child in path {
                        proof = self.push_projection(proof, child);
                    }
                    return Some(proof);
                }
            }
        }
        None
    }

    // Argument certificates give the canonical spelling of equality-sort leaves.
    // Evaluated container results can rearrange those leaves (set-intersect,
    // vec-get, etc.), so follow the evaluated term rather than the call arguments.
    fn primitive_leader(&mut self, term: TermId, arguments: &[ProofId]) -> TermId {
        if let Some(proof) = arguments.iter().find(|&&id| self.get(id).lhs() == term) {
            return self.get(*proof).rhs();
        }
        if let Term::App(head, children) = self.term_dag.get(term).clone()
            && self.container_normalizers.contains_key(&head)
        {
            let children = children
                .into_iter()
                .map(|child| self.primitive_leader(child, arguments))
                .collect();
            let term = self.term_dag.app(head, children);
            return self.normalize_container(term);
        }
        term
    }

    /// Expand a primitive's equality using existing argument certificates,
    /// projections, positional congruence, and container normalization.
    fn primitive_certificate(
        &mut self,
        left: TermId,
        right: TermId,
        arguments: &[ProofId],
        evidence: &[ProofId],
    ) -> Result<ProofId, String> {
        if let Some(proof) = self.existing_equality(left, right, evidence) {
            return Ok(proof);
        }
        if left == right && self.reflexive_value_term(left) {
            return Ok(self.push_shared_proof(
                SynthKey::Fiat(left, left),
                Proof {
                    proposition: Proposition::new(left, left),
                    justification: Justification::Fiat,
                },
            ));
        }
        let forward = self.existing_witness(left, evidence);
        let anchor = forward
            .or_else(|| self.existing_witness(right, evidence))
            .ok_or_else(|| {
                format!(
                    "Could not find term {} in the e-graph",
                    self.term_dag.to_string(left)
                )
            })?;
        if left == right {
            return Ok(self.reflexive(anchor));
        }
        let Term::App(_, selected) = self.term_dag.get(left).clone() else {
            return Err("a non-container primitive result needs an existing equality".into());
        };
        let mut targets = selected
            .into_iter()
            .map(|term| {
                let leader = self.primitive_leader(term, arguments);
                Some((term, leader))
            })
            .collect::<Vec<_>>();
        let endpoint = self.get(anchor).rhs();
        let Term::App(_, actual) = self.term_dag.get(endpoint).clone() else {
            return Err("a container witness must end at an application".into());
        };
        let mut proof = self.reflexive(anchor);
        for (index, actual) in actual.into_iter().enumerate() {
            let target = targets
                .iter_mut()
                .find(|target| {
                    target.is_some_and(|(term, leader)| {
                        (if forward.is_some() { term } else { leader }) == actual
                    })
                })
                .ok_or_else(|| "container witness has incompatible elements".to_owned())?;
            let (term, leader) = target.take().unwrap();
            let projected = self.push_projection(anchor, index);
            let mut child_evidence = vec![projected];
            child_evidence.extend_from_slice(evidence);
            let step = self.primitive_certificate(term, leader, arguments, &child_evidence)?;
            let step = if forward.is_some() {
                step
            } else {
                self.sym(step)
            };
            proof = self.congr(proof, index, step);
        }
        // A canonical set may have fewer elements than the requested source.
        // Projection cannot provide the discarded occurrences; they require a
        // witness of that original source container in the existing evidence.
        if targets.iter().any(Option::is_some) {
            return Err(format!(
                "Could not find term {} in the e-graph",
                self.term_dag.to_string(left)
            ));
        }
        proof = self.normalize_step(proof);
        Ok(if forward.is_some() {
            proof
        } else {
            self.sym(proof)
        })
    }
}
