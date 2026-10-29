//! Lift proofs of flattened rewrites back to the original source rules.
use super::format::{
    SlottedConclusion, SlottedJustification as Step, SlottedPremise, SlottedProofId,
    SlottedProofStore, SlottedProposition,
};
use super::lifting::Lifting;
use super::source::{Requirement, SlottedProgram, SourceFact, pattern_term};
use super::terms::{Renaming, term_renaming};
use super::{HashMap, HashSet};
use egglog::{Term, TermId};
use std::collections::VecDeque;

type Result<T> = std::result::Result<T, String>;

pub(super) fn lift(
    old: SlottedProofStore,
    program: &SlottedProgram,
    conclusion: SlottedConclusion,
) -> Result<(SlottedProofStore, SlottedConclusion)> {
    let steps: Vec<_> = old
        .dependencies(conclusion.proof)
        .into_iter()
        .map(|id| (id, old.get(id).clone()))
        .collect();
    let mut out = Lifting::new(old);
    let mut lifted = HashMap::default();
    for (id, proof) in steps {
        let result = match &proof.justification {
            Step::Rule {
                name,
                substitution,
                premises,
            } => {
                let premises = premises
                    .iter()
                    .map(|p| out.proof(lifted[&p.proof()]))
                    .collect();
                let result = lift_rule(
                    &mut out,
                    program,
                    name,
                    substitution.clone(),
                    premises,
                    proof.proposition.clone(),
                )
                .map_err(|e| format!("lifting source rule {name}: {e}"))?;
                let rhs = SlottedProofStore::proposition(&out, result).rhs;
                let refreshed = program.refresh_binders(&mut out.term_dag, rhs);
                let result = if refreshed == rhs {
                    result
                } else {
                    out.alpha(result, refreshed)
                };
                let actual = SlottedProofStore::proposition(&out, result).clone();
                let renaming = term_renaming(&out.term_dag, &[(proof.proposition.rhs, actual.rhs)])
                    .ok_or("lifted rule changes the right-hand term's shape")?;
                out.view(result, proof.proposition.rhs, renaming)
            }
            Step::Fiat => {
                let proof = source_fiat(&mut out, program, proof.proposition)?;
                out.plain(proof)
            }
            Step::Sym(p) => out.sym(lifted[p]),
            Step::Alpha(p) => {
                let premise = out.proof(lifted[p]);
                let proof = out.alpha(premise, proof.proposition.rhs);
                out.plain(proof)
            }
            Step::Trans(a, b) => out.trans(lifted[a], lifted[b]).map_err(|e| e.0)?,
            Step::Congr {
                proof: parent,
                child_index,
                child_proof,
            } => {
                // Restore RHS names without changing the child matched by the parent.
                let mut child = lifted[child_proof];
                let actual = SlottedProofStore::proposition(&out, out.proof(child));
                let wanted = out.proposition(child);
                if let Some(renaming) = term_renaming(
                    &out.term_dag,
                    &[(actual.lhs, wanted.lhs), (actual.rhs, wanted.rhs)],
                ) {
                    child = out.equivariance(child, &renaming);
                }
                let p = out
                    .congr(lifted[parent], *child_index, child)
                    .map_err(|e| e.0)?;
                let rhs = out.proposition(p).rhs;
                let renaming = term_renaming(&out.term_dag, &[(rhs, proof.proposition.rhs)])
                    .ok_or("lifting congruence changes the right-hand term's shape")?;
                out.reframe(p, renaming)
            }
            Step::Proj {
                proof: parent,
                child_index,
            } => out.project(lifted[parent], *child_index).map_err(|e| e.0)?,
            Step::Equivariance { proof, renaming } => {
                let p = out.equivariance(lifted[proof], renaming);
                out.reframe(p, renaming.clone())
            }
        };
        lifted.insert(id, result);
    }
    let (store, mut result) = out.finish(lifted[&conclusion.proof]);
    result.renaming = result.renaming.compose(&conclusion.renaming);
    Ok((store, result))
}

fn source_fiat(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    claimed: SlottedProposition,
) -> Result<SlottedProofId> {
    if claimed.lhs == claimed.rhs && program.is_built(&store.term_dag, claimed.lhs)
        || program.union_sort(claimed.lhs, claimed.rhs).is_some()
    {
        return Ok(store.fiat(claimed.lhs, claimed.rhs));
    }
    for union in &program.unions {
        for (lhs, rhs) in [(union.lhs, union.rhs), (union.rhs, union.lhs)] {
            if program.alpha_eq(&mut store.term_dag, lhs, claimed.lhs)
                && program.alpha_eq(&mut store.term_dag, rhs, claimed.rhs)
            {
                let proof = store.fiat(lhs, rhs);
                return Ok(Witnesses::new(store, program, vec![]).alpha_endpoints(
                    proof,
                    claimed.lhs,
                    claimed.rhs,
                ));
            }
        }
    }
    let mut known = vec![];
    for root in program
        .lets
        .values()
        .copied()
        .chain(program.unions.iter().flat_map(|u| [u.lhs, u.rhs]))
    {
        let refreshed = program.refresh_binders(&mut store.term_dag, root);
        let proof = store.fiat(root, root);
        known.push(if refreshed == root {
            proof
        } else {
            store.alpha(proof, refreshed)
        });
    }
    let mut witnesses = Witnesses::new(store, program, known);
    if claimed.lhs == claimed.rhs {
        witnesses.reflexive(claimed.lhs)
    } else {
        Err("fiat is not an original source union".into())
    }
}

fn lift_rule(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    name: &str,
    substitution: Vec<(String, TermId)>,
    premises: Vec<SlottedProofId>,
    claimed: SlottedProposition,
) -> Result<SlottedProofId> {
    let rule = program
        .rewrites
        .get(name)
        .ok_or_else(|| format!("missing original rewrite {name}"))?;
    let sigma: HashMap<_, _> = substitution.iter().cloned().collect();
    let instance = |store: &mut SlottedProofStore, expr| -> Result<TermId> {
        let term = pattern_term(&mut store.term_dag, expr);
        rule.instantiate(&mut store.term_dag, term, &sigma)
    };
    let (lhs, rhs) = rule.endpoints();
    let lhs = instance(store, lhs)?;
    let rhs = instance(store, rhs)?;
    let variables: HashSet<_> = rule
        .patterns()
        .flat_map(|expr| expr.vars())
        .map(|var| var.name)
        .filter(|name| !rule.globals.contains_key(name))
        .collect();
    let substitution = substitution
        .into_iter()
        .filter(|(var, _)| variables.contains(var))
        .collect();
    let mut witnesses = Witnesses::new(store, program, premises);
    let root = witnesses.exists(lhs)?;
    let mut source_premises = vec![SlottedPremise::Equality(root)];
    for requirement in rule.conditions().iter().flat_map(SourceFact::requirements) {
        source_premises.push(match requirement {
            Requirement::Exists(t) => {
                let t = instance(witnesses.store, t)?;
                witnesses.exists(t)?.into()
            }
            Requirement::RenamingEqual(a, b) => {
                let a = instance(witnesses.store, a)?;
                let b = instance(witnesses.store, b)?;
                let proof = witnesses.renaming_equality(a, b)?;
                let representative = witnesses.store.proposition(proof).rhs;
                let renaming = program
                    .renaming_between(&mut witnesses.store.term_dag, b, representative)
                    .ok_or("guard representative has no slot permutation")?;
                SlottedPremise::Renaming { proof, renaming }
            }
            Requirement::Equal(a, b) => {
                let a = instance(witnesses.store, a)?;
                let b = instance(witnesses.store, b)?;
                witnesses.condition_equality(program, a, b)?.into()
            }
        });
    }
    let source = witnesses.store.add(
        SlottedProposition::equal(lhs, rhs),
        Step::Rule {
            name: name.into(),
            substitution,
            premises: source_premises,
        },
    );
    witnesses.add(source);
    if claimed.lhs != claimed.rhs
        && let Some(renaming) = witnesses.renaming(&[(lhs, claimed.lhs)])
    {
        return Ok(witnesses.store.equivariance(source, renaming));
    }
    if claimed.lhs == claimed.rhs {
        return witnesses.reflexive(claimed.lhs);
    }
    witnesses.exists(claimed.lhs)?;
    let before = witnesses.reconstruct(claimed.lhs, lhs, true)?;
    let start = witnesses.store.proposition(before).lhs;
    let renaming = witnesses
        .renaming(&[(start, claimed.lhs)])
        .ok_or("reconstruction changes the left-hand term's shape")?;
    let middle = witnesses.store.trans(before, source).map_err(|e| e.0)?;
    let result = if witnesses.renaming(&[(rhs, claimed.rhs)]).is_some() {
        middle
    } else {
        let after = witnesses.equality(rhs, claimed.rhs)?;
        witnesses.store.trans(middle, after).map_err(|e| e.0)?
    };
    Ok(witnesses.store.equivariance(result, renaming))
}

/// Ordinary equalities for the atoms of one match. Reconstruction depends only
/// on these proofs, not on encoded classes, frames, or compiler variable names.
struct Witnesses<'a> {
    store: &'a mut SlottedProofStore,
    program: &'a SlottedProgram,
    edges: Vec<SlottedProofId>,
    known: HashMap<TermId, SlottedProofId>,
    memo: HashMap<(TermId, TermId, bool), SlottedProofId>,
    active: HashSet<(TermId, TermId, bool)>,
}

impl<'a> Witnesses<'a> {
    fn new(
        store: &'a mut SlottedProofStore,
        program: &'a SlottedProgram,
        proofs: Vec<SlottedProofId>,
    ) -> Self {
        let mut out = Self {
            store,
            program,
            edges: vec![],
            known: HashMap::default(),
            memo: HashMap::default(),
            active: HashSet::default(),
        };
        for proof in proofs {
            out.add(proof);
        }
        out
    }

    fn add(&mut self, proof: SlottedProofId) {
        self.edges.push(proof);
        let inverse = self.store.sym(proof);
        let mut work = vec![inverse, proof];
        while let Some(p) = work.pop() {
            let term = self.store.proposition(p).rhs;
            if self.known.contains_key(&term) {
                continue;
            }
            self.known.insert(term, p);
            if let Term::App(_, children) = self.store.term_dag.get(term) {
                let count = children.len();
                for i in (0..count).rev() {
                    work.push(self.store.project(p, i).expect("valid child index"));
                }
            }
        }
    }

    fn reflexive(&mut self, term: TermId) -> Result<SlottedProofId> {
        let proof = self.exists(term)?;
        if self.store.proposition(proof).lhs == term {
            return Ok(proof);
        }
        let inverse = self.store.sym(proof);
        self.store.trans(inverse, proof).map_err(|e| e.0)
    }

    fn exists(&mut self, term: TermId) -> Result<SlottedProofId> {
        if let Some(&p) = self.known.get(&term) {
            return Ok(p);
        }
        let mut candidates: Vec<_> = self.known.keys().copied().collect();
        candidates.sort_unstable();
        let refreshed = self.program.refresh_binders(&mut self.store.term_dag, term);
        for target in [term, refreshed] {
            for &candidate in &candidates {
                if let Ok(proof) = self.reconstruct(candidate, target, true) {
                    let proof = if target == term {
                        proof
                    } else {
                        self.store.alpha(proof, term)
                    };
                    self.add(proof);
                    return Ok(proof);
                }
            }
        }
        Err(format!(
            "no matched evidence for {}",
            self.store.term_dag.to_string(term)
        ))
    }

    fn renaming(&self, pairs: &[(TermId, TermId)]) -> Option<Renaming> {
        term_renaming(&self.store.term_dag, pairs)
    }

    fn condition_equality(
        &mut self,
        program: &SlottedProgram,
        a: TermId,
        b: TermId,
    ) -> Result<SlottedProofId> {
        for proof in self.edges.clone() {
            let p = self.store.proposition(proof).clone();
            if program.alpha_eq(&mut self.store.term_dag, p.lhs, a)
                && program.alpha_eq(&mut self.store.term_dag, p.rhs, b)
            {
                return Ok(self.alpha_endpoints(proof, a, b));
            }
            if program.alpha_eq(&mut self.store.term_dag, p.rhs, a)
                && program.alpha_eq(&mut self.store.term_dag, p.lhs, b)
            {
                let proof = self.store.sym(proof);
                return Ok(self.alpha_endpoints(proof, a, b));
            }
        }
        if program.alpha_eq(&mut self.store.term_dag, a, b) {
            let proof = self.reflexive(a)?;
            return Ok(self.alpha_endpoints(proof, a, b));
        }
        self.equality(a, b)
    }

    fn alpha_endpoints(
        &mut self,
        mut proof: SlottedProofId,
        lhs: TermId,
        rhs: TermId,
    ) -> SlottedProofId {
        if self.store.proposition(proof).rhs != rhs {
            proof = self.store.alpha(proof, rhs);
        }
        if self.store.proposition(proof).lhs != lhs {
            proof = self.store.sym(proof);
            proof = self.store.alpha(proof, lhs);
            proof = self.store.sym(proof);
        }
        proof
    }

    fn renaming_equality(&mut self, a: TermId, b: TermId) -> Result<SlottedProofId> {
        for term in [a, b] {
            let proof = self.exists(term)?;
            self.add(proof);
        }
        if let Ok(proof) = self.equality(a, b) {
            return Ok(proof);
        }
        let initial = self.reflexive(a)?;
        let mut work = VecDeque::from([initial]);
        let mut seen = Vec::new();
        while let Some(proof) = work.pop_front() {
            let current = self.store.proposition(proof).rhs;
            if self
                .program
                .eq_modulo_renaming(&mut self.store.term_dag, current, b)
            {
                return Ok(proof);
            }
            if seen.iter().any(|&term| {
                self.program
                    .eq_modulo_renaming(&mut self.store.term_dag, current, term)
            }) {
                continue;
            }
            seen.push(current);
            for edge in self.edges.clone() {
                let p = self.store.proposition(edge).clone();
                for (left, reversed) in [(p.lhs, false), (p.rhs, true)] {
                    if let Some(renaming) = self.renaming(&[(left, current)]) {
                        let edge = if reversed { self.store.sym(edge) } else { edge };
                        let edge = self.store.equivariance(edge, renaming);
                        work.push_back(self.store.trans(proof, edge).map_err(|e| e.0)?);
                    }
                }
            }
        }
        Err("no equality up to renaming between the guard's terms".into())
    }

    fn equality(&mut self, from: TermId, to: TermId) -> Result<SlottedProofId> {
        self.reconstruct(from, to, false)
    }

    // Existence allows a permutation of the whole derivation. An equality must
    // preserve its starting term as well as end at the requested target.
    fn reconstruct(
        &mut self,
        from: TermId,
        to: TermId,
        rename_source: bool,
    ) -> Result<SlottedProofId> {
        let key = (from, to, rename_source);
        if let Some(&p) = self.memo.get(&key) {
            return Ok(p);
        }
        if !self.active.insert(key) {
            return Err("cyclic atom expansion".into());
        }
        let result = self.search(from, to, rename_source);
        self.active.remove(&key);
        if let Ok(p) = result {
            self.memo.insert(key, p);
        }
        result
    }

    fn search(&mut self, from: TermId, to: TermId, rename_source: bool) -> Result<SlottedProofId> {
        for edge in self.edges.clone() {
            let p = self.store.proposition(edge).clone();
            if let Some(renaming) = self.renaming(&[(p.lhs, from), (p.rhs, to)]) {
                return Ok(self.store.equivariance(edge, renaming));
            }
            if let Some(renaming) = self.renaming(&[(p.rhs, from), (p.lhs, to)]) {
                let inverse = self.store.sym(edge);
                return Ok(self.store.equivariance(inverse, renaming));
            }
        }
        let initial = self
            .known
            .get(&from)
            .copied()
            .ok_or("unknown starting term")?;
        let back = self.store.sym(initial);
        let initial = self.store.trans(back, initial).map_err(|e| e.0)?;
        let mut work = VecDeque::from([initial]);
        let mut seen = Vec::new();
        while let Some(proof) = work.pop_front() {
            let current = self.store.proposition(proof).rhs;
            if current == to {
                return Ok(proof);
            }
            if self.program.alpha_eq(&mut self.store.term_dag, current, to) {
                return Ok(self.store.alpha(proof, to));
            }
            if rename_source && let Some(renaming) = self.renaming(&[(current, to)]) {
                return Ok(self.store.equivariance(proof, renaming));
            }
            if seen.iter().any(|&term| {
                current == term || rename_source && self.renaming(&[(current, term)]).is_some()
            }) {
                continue;
            }
            seen.push(current);
            if let (Term::App(head, children), Term::App(want, targets)) = (
                self.store.term_dag.get(current).clone(),
                self.store.term_dag.get(to).clone(),
            ) && head == want
                && children.len() == targets.len()
            {
                let mut expanded = Ok(proof);
                for (index, &target) in targets.iter().enumerate() {
                    expanded = expanded.and_then(|mut parent| {
                        let Term::App(_, children) = self
                            .store
                            .term_dag
                            .get(self.store.proposition(parent).rhs)
                            .clone()
                        else {
                            unreachable!()
                        };
                        let child = children[index];
                        if child == target {
                            return Ok(parent);
                        }
                        let projection = self.store.project(parent, index).map_err(|e| e.0)?;
                        self.known.entry(child).or_insert(projection);
                        let proof = self.equality(child, target).or_else(|error| {
                            if rename_source {
                                self.reconstruct(child, target, true)
                            } else {
                                Err(error)
                            }
                        })?;
                        if rename_source {
                            let left = self.store.proposition(proof).lhs;
                            let mut pairs = vec![(child, left)];
                            pairs.extend(targets[..index].iter().map(|&t| (t, t)));
                            let renaming =
                                self.renaming(&pairs).ok_or("inconsistent sibling names")?;
                            parent = self.store.equivariance(parent, renaming);
                        }
                        self.store.congr(parent, index, proof).map_err(|e| e.0)
                    });
                    if expanded.is_err() {
                        break;
                    }
                }
                if let Ok(proof) = expanded {
                    return Ok(proof);
                }
            }
            for edge in self.edges.clone() {
                let p = self.store.proposition(edge).clone();
                for (left, reversed) in [(p.lhs, false), (p.rhs, true)] {
                    let renaming = if left == current {
                        Renaming::identity()
                    } else if rename_source
                        && let Some(renaming) = self.renaming(&[(left, current)])
                    {
                        renaming
                    } else {
                        continue;
                    };
                    let edge = if reversed { self.store.sym(edge) } else { edge };
                    let edge = self.store.equivariance(edge, renaming);
                    work.push_back(self.store.trans(proof, edge).map_err(|e| e.0)?);
                }
            }
        }
        Err(format!(
            "cannot reconstruct {} = {} from matched atoms",
            self.store.term_dag.to_string(from),
            self.store.term_dag.to_string(to)
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::super::source::ColumnKind;
    use super::*;
    use crate::slotted::proofs::check_proof;
    use egglog::TermDag;

    #[test]
    fn reconstructs_nested_binders_after_a_shape_change() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        for head in ["F", "G"] {
            program.add_constructor(head, vec![ColumnKind::Child]);
        }
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program
            .add_let(&mut dag, "input", "(F (G (Lam $0 $0)))")
            .unwrap();
        program
            .add_let(&mut dag, "target", "(F (Lam $3 (Lam $4 $4)))")
            .unwrap();
        program
            .add_union(&mut dag, "(G (Lam $1 $1))", "(Lam $2 (Lam $1 $1))", "U")
            .unwrap();
        let target = program.lets.shift_remove("target").unwrap();
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(program.lets["input"], program.lets["input"]);
        let union = store.fiat(program.unions[0].lhs, program.unions[0].rhs);
        let mut witnesses = Witnesses::new(&mut store, &program, vec![root, union]);
        let proof = witnesses.exists(target).unwrap();
        assert_eq!(witnesses.store.proposition(proof).rhs, target);
        let equality = witnesses.equality(program.lets["input"], target).unwrap();
        assert_eq!(
            witnesses.store.proposition(equality).lhs,
            program.lets["input"]
        );
        assert_eq!(witnesses.store.proposition(equality).rhs, target);
        check_proof(&mut store, &program, proof).unwrap();
        check_proof(&mut store, &program, equality).unwrap();
    }

    #[test]
    fn reconstruction_preserves_shared_sibling_names() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_let(&mut dag, "input", "(Pair $0 $0)").unwrap();
        program.add_let(&mut dag, "target", "(Pair $1 $2)").unwrap();
        let target = program.lets.shift_remove("target").unwrap();
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(program.lets["input"], program.lets["input"]);
        let mut witnesses = Witnesses::new(&mut store, &program, vec![root]);
        assert!(witnesses.exists(target).is_err());
    }

    #[test]
    fn reconstruction_tries_equal_children_before_renaming_them() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        for head in ["F", "G", "H"] {
            program.add_constructor(head, vec![ColumnKind::Child]);
        }
        program
            .add_let(&mut dag, "input", "(Pair $0 (G $0))")
            .unwrap();
        program
            .add_let(&mut dag, "target", "(Pair $0 (F $0))")
            .unwrap();
        for (lhs, rhs) in [
            ("(G $0)", "(H $1)"),
            ("(G $0)", "(H $0)"),
            ("(H $0)", "(F $0)"),
        ] {
            program.add_union(&mut dag, lhs, rhs, "U").unwrap();
        }
        let target = program.lets.shift_remove("target").unwrap();
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(program.lets["input"], program.lets["input"]);
        let mut premises = vec![root];
        for union in &program.unions {
            premises.push(store.fiat(union.lhs, union.rhs));
        }
        let mut witnesses = Witnesses::new(&mut store, &program, premises);
        let proof = witnesses.exists(target).unwrap();
        assert_eq!(witnesses.store.proposition(proof).rhs, target);
        check_proof(&mut store, &program, proof).unwrap();
    }

    #[test]
    fn renaming_guard_lifts_child_equalities_through_congruence() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        for head in ["F", "G", "H"] {
            program.add_constructor(head, vec![ColumnKind::Child]);
        }
        program.add_let(&mut dag, "a", "(F (G $0))").unwrap();
        program.add_let(&mut dag, "b", "(F (H $0))").unwrap();
        program.add_let(&mut dag, "input", "(Pair a b)").unwrap();
        program
            .add_union(&mut dag, "(G $0)", "(H $0)", "U")
            .unwrap();
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(program.lets["input"], program.lets["input"]);
        let union = store.fiat(program.unions[0].lhs, program.unions[0].rhs);
        let mut witnesses = Witnesses::new(&mut store, &program, vec![root, union]);
        let proof = witnesses
            .renaming_equality(program.lets["a"], program.lets["b"])
            .unwrap();
        check_proof(&mut store, &program, proof).unwrap();
    }
}
