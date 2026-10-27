//! Lift proofs of flattened rewrites back to the original source rules.
use super::format::{
    SlottedConclusion, SlottedJustification as Step, SlottedProofId, SlottedProofStore,
    SlottedProposition,
};
use super::lifting::Lifting;
use super::source::{ColumnKind, Condition, Requirement, Rhs, SlottedProgram};
use super::terms::{Renaming, slot_of};
use super::{HashMap, HashSet};
use egglog::{Term, TermDag, TermId};
use std::collections::{BTreeMap, VecDeque};

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
                let premises = premises.iter().map(|p| out.proof(lifted[p])).collect();
                let result = lift_rule(
                    &mut out,
                    program,
                    name,
                    substitution.clone(),
                    premises,
                    proof.proposition.clone(),
                )
                .map_err(|e| format!("lifting source rule {name}: {e}"))?;
                let actual = SlottedProofStore::proposition(&out, result).clone();
                let renaming = term_renaming(&out.term_dag, &[(proof.proposition.rhs, actual.rhs)])
                    .ok_or("lifted rule changes the right-hand term's shape")?;
                out.view(result, proof.proposition.rhs, renaming)
            }
            Step::Fiat => out.fiat(proof.proposition.lhs, proof.proposition.rhs),
            Step::Sym(p) => out.sym(lifted[p]),
            Step::Trans(a, b) => out.trans(lifted[a], lifted[b]).map_err(|e| e.0)?,
            Step::Congr {
                proof: parent,
                child_index,
                child_proof,
            } => {
                let p = out
                    .congr(lifted[parent], *child_index, lifted[child_proof])
                    .map_err(|e| e.0)?;
                let rhs = out.proposition(p).rhs;
                let renaming = term_renaming(&out.term_dag, &[(rhs, proof.proposition.rhs)])
                    .ok_or("lifting congruence changes the right-hand term's shape")?;
                out.reframe(p, renaming)
            }
            Step::Proj {
                proof: parent,
                child_index,
            } => {
                let parent = lifted[parent];
                let inverse = out.proposition(parent).renaming.inverse();
                let ordinary = out.proof(parent);
                let p = out.project(ordinary, *child_index).map_err(|e| e.0)?;
                let p = SlottedProofStore::equivariance(&mut out, p, inverse);
                out.plain(p)
            }
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
    let instance = |store: &mut SlottedProofStore, term| -> Result<TermId> {
        let term = rule.instantiate(&mut store.term_dag, term, &sigma)?;
        Ok(program.refresh_binders(&mut store.term_dag, term))
    };
    let lhs = instance(store, rule.lhs)?;
    let rhs = match &rule.rhs {
        Rhs::Term(term) => instance(store, *term)?,
        Rhs::Var(var) => *sigma.get(var).ok_or_else(|| format!("unbound {var}"))?,
    };
    let variables: HashSet<_> = std::iter::once(rule.lhs)
        .chain(rule.conditions.iter().flat_map(Condition::terms))
        .chain(match &rule.rhs {
            Rhs::Term(t) => Some(*t),
            Rhs::Var(_) => None,
        })
        .flat_map(|term| rule.pattern_vars(&store.term_dag, term))
        .collect();
    let substitution = substitution
        .into_iter()
        .filter(|(var, _)| variables.contains(var) || matches!(&rule.rhs, Rhs::Var(v) if v == var))
        .collect();
    let mut witnesses = Witnesses::new(store, program, premises);
    let root = witnesses.exists(lhs)?;
    let mut source_premises = vec![root];
    for requirement in rule.conditions.iter().flat_map(Condition::requirements) {
        source_premises.push(match requirement {
            Requirement::Exists(t) => {
                let t = instance(witnesses.store, t)?;
                witnesses.exists(t)?
            }
            Requirement::Equal(a, b) => {
                let a = instance(witnesses.store, a)?;
                let b = instance(witnesses.store, b)?;
                witnesses.condition_equality(program, a, b)?
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
    let before = witnesses.equality(claimed.lhs, lhs)?;
    let after = witnesses.equality(rhs, claimed.rhs)?;
    let middle = witnesses.store.trans(before, source).map_err(|e| e.0)?;
    witnesses.store.trans(middle, after).map_err(|e| e.0)
}

/// Ordinary equalities for the atoms of one match. Reconstruction depends only
/// on these proofs, not on encoded classes, frames, or compiler variable names.
struct Witnesses<'a> {
    store: &'a mut SlottedProofStore,
    program: &'a SlottedProgram,
    edges: Vec<SlottedProofId>,
    known: HashMap<TermId, SlottedProofId>,
    memo: HashMap<(TermId, TermId), SlottedProofId>,
    active: HashSet<(TermId, TermId)>,
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
        for mut candidate in candidates {
            if let Some(renaming) = self.renaming(&[(candidate, term)]) {
                let proof = self.store.equivariance(self.known[&candidate], renaming);
                self.known.insert(term, proof);
                return Ok(proof);
            }
            let mut bindings = BTreeMap::new();
            let mut work = vec![(candidate, term)];
            while let Some((a, b)) = work.pop() {
                let (Term::App(head, xs), Term::App(want, ys)) =
                    (self.store.term_dag.get(a), self.store.term_dag.get(b))
                else {
                    continue;
                };
                if head != want || xs.len() != ys.len() {
                    continue;
                }
                if let Some(ctor) = self.program.constructors.get(head) {
                    for (column, (&x, &y)) in ctor.columns.iter().zip(xs.iter().zip(ys)) {
                        if *column == ColumnKind::Binder
                            && let (Some(x), Some(y)) = (
                                slot_of(&self.store.term_dag, x),
                                slot_of(&self.store.term_dag, y),
                            )
                        {
                            bindings.insert(x, y);
                        }
                    }
                }
                work.extend(xs.iter().copied().zip(ys.iter().copied()));
            }
            if let Some(renaming) = Renaming::completing(bindings)
                && !renaming.is_identity()
            {
                let proof = self.store.equivariance(self.known[&candidate], renaming);
                candidate = self.store.proposition(proof).rhs;
                self.add(proof);
            }
            if let Ok(proof) = self.equality(candidate, term) {
                self.known.insert(term, proof);
                return Ok(proof);
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
                return Ok(proof);
            }
            if program.alpha_eq(&mut self.store.term_dag, p.rhs, a)
                && program.alpha_eq(&mut self.store.term_dag, p.lhs, b)
            {
                return Ok(self.store.sym(proof));
            }
        }
        if program.alpha_eq(&mut self.store.term_dag, a, b) {
            return self.reflexive(a);
        }
        self.equality(a, b)
    }

    fn equality(&mut self, from: TermId, to: TermId) -> Result<SlottedProofId> {
        if let Some(&p) = self.memo.get(&(from, to)) {
            return Ok(p);
        }
        if !self.active.insert((from, to)) {
            return Err("cyclic atom expansion".into());
        }
        let result = self.search(from, to);
        self.active.remove(&(from, to));
        if let Ok(p) = result {
            self.memo.insert((from, to), p);
        }
        result
    }

    fn search(&mut self, from: TermId, to: TermId) -> Result<SlottedProofId> {
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
        let mut seen = HashSet::default();
        while let Some(proof) = work.pop_front() {
            let current = self.store.proposition(proof).rhs;
            if current == to {
                return Ok(proof);
            }
            if !seen.insert(current) {
                continue;
            }
            if let (Term::App(head, children), Term::App(want, targets)) = (
                self.store.term_dag.get(current).clone(),
                self.store.term_dag.get(to).clone(),
            ) && head == want
                && children.len() == targets.len()
            {
                let mut expanded = Ok(proof);
                for (index, (child, target)) in children.into_iter().zip(targets).enumerate() {
                    if child == target {
                        continue;
                    }
                    expanded = expanded.and_then(|parent| {
                        let child = self.equality(child, target)?;
                        self.store.congr(parent, index, child).map_err(|e| e.0)
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
                let p = self.store.proposition(edge);
                let edge = if p.lhs == current {
                    edge
                } else if p.rhs == current {
                    self.store.sym(edge)
                } else {
                    continue;
                };
                work.push_back(self.store.trans(proof, edge).map_err(|e| e.0)?);
            }
        }
        Err(format!(
            "cannot reconstruct {} = {} from matched atoms",
            self.store.term_dag.to_string(from),
            self.store.term_dag.to_string(to)
        ))
    }
}

fn term_renaming(dag: &TermDag, pairs: &[(TermId, TermId)]) -> Option<Renaming> {
    let mut work = pairs.to_vec();
    let mut names = BTreeMap::new();
    while let Some((a, b)) = work.pop() {
        match (slot_of(dag, a), slot_of(dag, b)) {
            (Some(a), Some(b)) => {
                if names.insert(a, b).is_some_and(|old| old != b) {
                    return None;
                }
            }
            (None, None) => match (dag.get(a), dag.get(b)) {
                (Term::App(f, xs), Term::App(g, ys)) if f == g && xs.len() == ys.len() => {
                    work.extend(xs.iter().copied().zip(ys.iter().copied()))
                }
                (x, y) if x == y => (),
                _ => return None,
            },
            _ => return None,
        }
    }
    Renaming::completing(names)
}
