//! Checks surface proofs against the slotted source program.

use super::format::{
    SlottedConclusion, SlottedJustification, SlottedProofId, SlottedProofStore, SlottedProposition,
};
use super::source::{Claim, ClaimKind, Condition, Rhs, SlottedProgram};
use super::terms::{all_slots, instantiate, is_subterm, pattern_vars, rename, slot_of};
use super::{HashMap, HashSet};
use egglog::{Term, TermDag, TermId};
use std::collections::BTreeSet;
use thiserror::Error;

#[derive(Debug, Clone, Error)]
/// A proof step or final claim that the source program does not justify.
pub enum SlottedCheckError {
    /// A fiat step is absent from the source program.
    #[error(
        "proof #{proof}: fiat {claim} is neither a built term's reflexivity nor a source union"
    )]
    InvalidFiat {
        /// The rejected step.
        proof: SlottedProofId,
        /// Its printed proposition.
        claim: String,
    },
    /// A rule application names an undeclared rewrite.
    #[error("proof #{proof}: no rewrite named {name:?}")]
    RuleNotFound {
        /// The rejected step.
        proof: SlottedProofId,
        /// The requested rewrite.
        name: String,
    },
    /// A rule application supplies the wrong number of premises.
    #[error("proof #{proof}: rule {name:?} takes {expected} premises, {actual} given")]
    PremiseCount {
        /// The rejected step.
        proof: SlottedProofId,
        /// The applied rewrite.
        name: String,
        /// The number required by the source rewrite.
        expected: usize,
        /// The number supplied by the proof.
        actual: usize,
    },
    /// A substitution omits a variable used by the rewrite.
    #[error("proof #{proof}: rule {name:?} leaves {variable} unbound")]
    Unbound {
        /// The rejected step.
        proof: SlottedProofId,
        /// The applied rewrite.
        name: String,
        /// The missing substitution key.
        variable: String,
    },
    /// A rule application does not match its source rewrite.
    #[error("proof #{proof}: rule {name:?}: {detail}")]
    Rule {
        /// The rejected step.
        proof: SlottedProofId,
        /// The applied rewrite.
        name: String,
        /// The violated rule requirement.
        detail: String,
    },
    /// A proof-algebra step does not follow from its premises.
    #[error("proof #{proof}: {step}: {detail}")]
    Step {
        /// The rejected step.
        proof: SlottedProofId,
        /// The proof operation being checked.
        step: &'static str,
        /// The violated operation requirement.
        detail: String,
    },
    /// The checked root proves a different claim.
    #[error(
        "the claim ({kind}, in {sort}) is not what the proof shows: it proves {proven}, the claim is {claim}"
    )]
    Claim {
        /// The requested equality kind.
        kind: String,
        /// The claim's carrier sort.
        sort: String,
        /// The proposition established by the proof.
        proven: String,
        /// The proposition requested by the source.
        claim: String,
    },
}

/// A verified equality and its carrier sort. Sort-independent equalities, such
/// as slot reflexivity, may be used in any carrier; other equalities retain
/// the sort of their source axiom or rewrite.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Checked {
    /// The equality established by the derivation.
    pub proposition: SlottedProposition,
    /// Its carrier sort, or `None` for a sort-independent equality.
    pub sort: Option<String>,
}

/// Check a proof and every proof it depends on, returning what it proves.
pub fn check_proof(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    root: SlottedProofId,
) -> Result<Checked, SlottedCheckError> {
    let mut checked: HashMap<SlottedProofId, Checked> = HashMap::default();
    for id in store.dependencies(root) {
        let result = check_one(store, program, id, &checked)?;
        checked.insert(id, result);
    }
    Ok(checked[&root].clone())
}

/// Check that a proof establishes a claim.
pub fn check_claim(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    claim: &Claim,
    conclusion: &SlottedConclusion,
) -> Result<(), SlottedCheckError> {
    let Checked {
        proposition: proven,
        sort,
    } = check_proof(store, program, conclusion.proof)?;
    let lhs = program.refresh_binders(&mut store.term_dag, claim.lhs);
    let rhs = program.refresh_binders(&mut store.term_dag, claim.rhs);
    let same_sort = sort.as_deref().is_none_or(|s| s == claim.sort);
    let holds = same_sort
        && proven.lhs == lhs
        && proven.rhs == rename(&mut store.term_dag, &conclusion.renaming, rhs)
        && match claim.kind {
            ClaimKind::RenamingEq => true,
            ClaimKind::Eq => {
                let free_rhs = program.free_slots(&store.term_dag, rhs);
                let free_lhs = program.free_slots(&store.term_dag, lhs);
                !conclusion.renaming.moves_any(&free_rhs)
                    || !conclusion.renaming.moves_any(&free_lhs)
            }
        };
    if holds {
        Ok(())
    } else {
        Err(SlottedCheckError::Claim {
            kind: match claim.kind {
                ClaimKind::Eq => "=".into(),
                ClaimKind::RenamingEq => "renaming-=".into(),
            },
            sort: claim.sort.clone(),
            proven: match sort {
                Some(s) => format!("{} in {s}", store.proposition_to_string(&proven)),
                None => store.proposition_to_string(&proven),
            },
            claim: store.proposition_to_string(&SlottedProposition::equal(claim.lhs, claim.rhs)),
        })
    }
}

/// The sort two parts of a derivation agree on, or the two they disagree on.
fn join_sorts(a: Option<String>, b: Option<String>) -> Result<Option<String>, (String, String)> {
    match (a, b) {
        (Some(a), Some(b)) if a != b => Err((a, b)),
        (Some(a), _) => Ok(Some(a)),
        (None, b) => Ok(b),
    }
}

fn check_one(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    id: SlottedProofId,
    checked: &HashMap<SlottedProofId, Checked>,
) -> Result<Checked, SlottedCheckError> {
    let proof = store.get(id).clone();
    let claimed = proof.proposition.clone();
    let step = |step: &'static str, detail: String| SlottedCheckError::Step {
        proof: id,
        step,
        detail,
    };
    // `dependencies` puts a premise before its use unless the proof is cyclic
    let premise = |p: &SlottedProofId| -> Result<Checked, SlottedCheckError> {
        checked.get(p).cloned().ok_or_else(|| {
            step(
                "premise",
                format!("proof #{p} is used before it is established: the proof is cyclic"),
            )
        })
    };
    let (derived, sort) = match &proof.justification {
        SlottedJustification::Fiat => {
            let dag = &store.term_dag;
            let reflexive = claimed.lhs == claimed.rhs && program.is_built(dag, claimed.lhs);
            let union = program.union_sort(claimed.lhs, claimed.rhs).is_some();
            if !(reflexive || union) {
                return Err(SlottedCheckError::InvalidFiat {
                    proof: id,
                    claim: store.proposition_to_string(&claimed),
                });
            }
            let sort = match program.union_sort(claimed.lhs, claimed.rhs) {
                Some(s) => Some(s.to_string()),
                None => program.sort_of(dag, claimed.lhs),
            };
            (claimed.clone(), sort)
        }
        SlottedJustification::Rule {
            name,
            substitution,
            premises,
        } => {
            let premises = premises
                .iter()
                .map(premise)
                .collect::<Result<Vec<_>, _>>()?;
            check_rule(store, program, id, name, substitution, &premises, &claimed)?
        }
        SlottedJustification::Sym(inner) => {
            let p = premise(inner)?;
            let q = p.proposition;
            (SlottedProposition::equal(q.rhs, q.lhs), p.sort)
        }
        SlottedJustification::Trans(left, right) => {
            let (l, r) = (premise(left)?, premise(right)?);
            if l.proposition.rhs != r.proposition.lhs {
                return Err(step(
                    "trans",
                    format!(
                        "middle terms differ: {} vs {}",
                        store.term_dag.to_string(l.proposition.rhs),
                        store.term_dag.to_string(r.proposition.lhs)
                    ),
                ));
            }
            let sort = join_sorts(l.sort, r.sort)
                .map_err(|(a, b)| step("trans", format!("joins a proof in {a} with one in {b}")))?;
            (
                SlottedProposition::equal(l.proposition.lhs, r.proposition.rhs),
                sort,
            )
        }
        SlottedJustification::Congr {
            proof: inner,
            child_index,
            child_proof,
        } => {
            let (p, c) = (premise(inner)?, premise(child_proof)?);
            let Term::App(head, mut children) = store.term_dag.get(p.proposition.rhs).clone()
            else {
                return Err(step(
                    "congr",
                    "right-hand side is not an application".into(),
                ));
            };
            let Some(&child) = children.get(*child_index) else {
                return Err(step("congr", format!("no child at {child_index}")));
            };
            if child != c.proposition.lhs {
                return Err(step(
                    "congr",
                    format!(
                        "child {} is not the child proof's left side {}",
                        store.term_dag.to_string(child),
                        store.term_dag.to_string(c.proposition.lhs)
                    ),
                ));
            }
            // the child proof is about the column's sort
            let ctor = program
                .constructors
                .get(&head)
                .ok_or_else(|| step("congr", format!("unknown constructor {head}")))?;
            let column_sort = ctor
                .sorts
                .get(*child_index)
                .ok_or_else(|| step("congr", format!("{head} has no column {child_index}")))?;
            if let Some(s) = &c.sort
                && s != column_sort
            {
                return Err(step(
                    "congr",
                    format!(
                        "the child proof is in {s}, but column {child_index} of {head} is {column_sort}"
                    ),
                ));
            }
            children[*child_index] = c.proposition.rhs;
            let rhs = store.term_dag.app(head, children);
            (
                SlottedProposition::equal(p.proposition.lhs, rhs),
                p.sort.or(Some(ctor.output.clone())),
            )
        }
        SlottedJustification::Equivariance {
            proof: inner,
            renaming,
        } => {
            let p = premise(inner)?;
            let lhs = rename(&mut store.term_dag, renaming, p.proposition.lhs);
            let rhs = rename(&mut store.term_dag, renaming, p.proposition.rhs);
            (SlottedProposition::equal(lhs, rhs), p.sort)
        }
    };
    if derived != claimed {
        return Err(step(
            "conclusion",
            format!(
                "states {} but derives {}",
                store.proposition_to_string(&claimed),
                store.proposition_to_string(&derived)
            ),
        ));
    }
    Ok(Checked {
        proposition: claimed,
        sort,
    })
}

/// The sort each variable of a pattern must take, from the columns it occurs in.
fn variable_sorts(
    program: &SlottedProgram,
    dag: &TermDag,
    pattern: TermId,
    out: &mut HashMap<String, String>,
) -> Result<(), String> {
    let Term::App(head, children) = dag.get(pattern).clone() else {
        return Ok(());
    };
    let ctor = program
        .constructors
        .get(&head)
        .ok_or_else(|| format!("unknown constructor {head}"))?;
    for (j, child) in children.iter().enumerate() {
        let Some(sort) = ctor.sorts.get(j) else {
            return Err(format!("{head} has no column {j}"));
        };
        match dag.get(*child) {
            Term::Var(v) => {
                if let Some(other) = out.insert(v.clone(), sort.clone())
                    && other != *sort
                {
                    return Err(format!("{v} occurs as both {other} and {sort}"));
                }
            }
            Term::App(..) => variable_sorts(program, dag, *child, out)?,
            Term::Lit(_) => {}
        }
    }
    Ok(())
}

fn check_rule(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    id: SlottedProofId,
    name: &str,
    substitution: &[(String, TermId)],
    premises: &[Checked],
    claimed: &SlottedProposition,
) -> Result<(SlottedProposition, Option<String>), SlottedCheckError> {
    let rule = program
        .rewrites
        .get(name)
        .ok_or_else(|| SlottedCheckError::RuleNotFound {
            proof: id,
            name: name.to_string(),
        })?;
    let fail = |detail: String| SlottedCheckError::Rule {
        proof: id,
        name: name.to_string(),
        detail,
    };
    let subst: HashMap<String, TermId> = substitution.iter().cloned().collect();
    let unbound = |variable: String| SlottedCheckError::Unbound {
        proof: id,
        name: name.to_string(),
        variable,
    };

    // The premises: the root pattern, then each `(= v call)` in order.
    let equalities: Vec<(&String, TermId)> = rule
        .conditions
        .iter()
        .filter_map(|c| match c {
            Condition::Eq { var, call } => Some((var, *call)),
            _ => None,
        })
        .collect();
    let expected = 1 + equalities.len();
    if premises.len() != expected {
        return Err(SlottedCheckError::PremiseCount {
            proof: id,
            name: name.to_string(),
            expected,
            actual: premises.len(),
        });
    }

    // The sorts: the rewrite is about its left-hand side's, each premise must be
    // about the sort of the pattern it matches, and each binding must have the
    // sort of the columns its variable stands in.
    let mut sort = program.sort_of(&store.term_dag, rule.lhs);
    let mut expected_sorts: HashMap<String, String> = HashMap::default();
    variable_sorts(program, &store.term_dag, rule.lhs, &mut expected_sorts).map_err(&fail)?;
    for (_, call) in &equalities {
        variable_sorts(program, &store.term_dag, *call, &mut expected_sorts).map_err(&fail)?;
    }
    if let Term::Var(root) = store.term_dag.get(rule.lhs) {
        sort = expected_sorts.get(root).cloned().or_else(|| {
            equalities
                .iter()
                .find(|(var, _)| *var == root)
                .and_then(|(_, call)| program.sort_of(&store.term_dag, *call))
        });
    }
    if let Rhs::Term(t) = &rule.rhs {
        variable_sorts(program, &store.term_dag, *t, &mut expected_sorts).map_err(&fail)?;
    }
    for (var, term) in substitution {
        if let Some(want) = expected_sorts.get(var)
            && let Some(got) = program.sort_of(&store.term_dag, *term)
            && got != *want
        {
            return Err(fail(format!(
                "{var} is bound to {}, which is {got}, where the rule wants {want}",
                store.term_dag.to_string(*term)
            )));
        }
    }

    // Slot literals: each is bound to a slot, and different literals to different
    // slots -- `(F $x $y)` does not match `(F $0 $0)`.
    let mut literals: Vec<String> = pattern_vars(&store.term_dag, rule.lhs);
    for condition in &rule.conditions {
        match condition {
            Condition::Eq { call, .. } => literals.extend(pattern_vars(&store.term_dag, *call)),
            Condition::Neq { lhs, rhs } => {
                literals.extend(pattern_vars(&store.term_dag, *lhs));
                literals.extend(pattern_vars(&store.term_dag, *rhs));
            }
            Condition::FreeNames { slots, .. } => literals.extend(slots.iter().cloned()),
            Condition::Free { slot, .. } | Condition::NotFree { slot, .. } => {
                literals.push(slot.clone())
            }
        }
    }
    if let Rhs::Term(t) = &rule.rhs {
        literals.extend(pattern_vars(&store.term_dag, *t));
    }
    let mut by_slot: HashMap<i64, String> = HashMap::default();
    for literal in literals.iter().filter(|v| v.starts_with('$')) {
        let term = *subst.get(literal).ok_or_else(|| unbound(literal.clone()))?;
        let slot = slot_of(&store.term_dag, term).ok_or_else(|| {
            fail(format!(
                "{literal} is bound to {}, not a slot",
                store.term_dag.to_string(term)
            ))
        })?;
        if let Some(other) = by_slot.insert(slot, literal.clone())
            && other != *literal
        {
            return Err(fail(format!(
                "{other} and {literal} are both ${slot}: different slot literals are different slots"
            )));
        }
    }

    let lhs = instantiate(&mut store.term_dag, rule.lhs, &subst).map_err(unbound)?;
    let lhs = program.refresh_binders(&mut store.term_dag, lhs);
    let root = &premises[0].proposition;
    if root.rhs != lhs {
        return Err(fail(format!(
            "the root premise proves {}, which does not end in the matched {}",
            store.proposition_to_string(root),
            store.term_dag.to_string(lhs)
        )));
    }
    sort = join_sorts(sort, premises[0].sort.clone())
        .map_err(|(a, b)| fail(format!("the rewrite is in {a}, its root premise in {b}")))?;
    for ((var, call), premise) in equalities.iter().zip(&premises[1..]) {
        let want_lhs = *subst.get(*var).ok_or_else(|| unbound((*var).clone()))?;
        let want_rhs = instantiate(&mut store.term_dag, *call, &subst).map_err(unbound)?;
        let want_rhs = program.refresh_binders(&mut store.term_dag, want_rhs);
        let got = &premise.proposition;
        // Source equality patterns are alpha-invariant. This does not permit
        // changing free slots; ordinary proof steps still compare exact terms.
        if !program.alpha_eq(&mut store.term_dag, got.lhs, want_lhs)
            || !program.alpha_eq(&mut store.term_dag, got.rhs, want_rhs)
        {
            return Err(fail(format!(
                "the premise for (= {var} ...) proves {}, not {} = {}",
                store.proposition_to_string(got),
                store.term_dag.to_string(want_lhs),
                store.term_dag.to_string(want_rhs)
            )));
        }
        let call_sort = program.sort_of(&store.term_dag, want_rhs);
        join_sorts(call_sort, premise.sort.clone()).map_err(|(a, b)| {
            fail(format!(
                "the pattern for (= {var} ...) is in {a}, its premise in {b}"
            ))
        })?;
    }

    for condition in &rule.conditions {
        match condition {
            Condition::Free { slot, vars } | Condition::NotFree { slot, vars } => {
                let slot_term = *subst.get(slot).ok_or_else(|| unbound(slot.clone()))?;
                let slot_number = slot_of(&store.term_dag, slot_term)
                    .ok_or_else(|| fail(format!("{slot} is bound to a non-slot")))?;
                let want_free = matches!(condition, Condition::Free { .. });
                let mut free = BTreeSet::new();
                for var in vars {
                    let term = *subst.get(var).ok_or_else(|| unbound(var.clone()))?;
                    free.extend(program.free_slots(&store.term_dag, term));
                }
                if free.contains(&slot_number) != want_free {
                    return Err(fail(format!(
                        "({} {slot} {}) fails: {slot} is ${slot_number}, free slots are {free:?}",
                        if want_free { "free" } else { "not-free" },
                        vars.join(" ")
                    )));
                }
            }
            Condition::FreeNames { var, slots } => {
                let term = *subst.get(var).ok_or_else(|| unbound(var.clone()))?;
                let wanted = slots
                    .iter()
                    .map(|slot| {
                        let term = *subst.get(slot).ok_or_else(|| unbound(slot.clone()))?;
                        slot_of(&store.term_dag, term)
                            .ok_or_else(|| fail(format!("{slot} is bound to a non-slot")))
                    })
                    .collect::<Result<BTreeSet<_>, _>>()?;
                let free = program.free_slots(&store.term_dag, term);
                if free != wanted {
                    return Err(fail(format!(
                        "free-names-are {var}: expected {wanted:?}, found {free:?}"
                    )));
                }
            }
            Condition::Neq { lhs, rhs } => {
                // two different terms: what the firing saw as two invocations
                let a = instantiate(&mut store.term_dag, *lhs, &subst).map_err(unbound)?;
                let b = instantiate(&mut store.term_dag, *rhs, &subst).map_err(unbound)?;
                if a == b {
                    return Err(fail(format!(
                        "(!= ...) fails: both sides are {}",
                        store.term_dag.to_string(a)
                    )));
                }
            }
            Condition::Eq { .. } => {}
        }
    }

    // Minted slots: right-hand-side slot literals the body never mentions must be
    // bound to slots that occur in no other binding. The body is the root
    // pattern and each `(= v call)`, `v` included.
    let mut body_vars: HashSet<String> = pattern_vars(&store.term_dag, rule.lhs)
        .into_iter()
        .collect();
    for (var, call) in &equalities {
        body_vars.insert((*var).clone());
        body_vars.extend(pattern_vars(&store.term_dag, *call));
    }
    let rhs = match &rule.rhs {
        Rhs::Term(t) => instantiate(&mut store.term_dag, *t, &subst).map_err(unbound)?,
        Rhs::Var(v) => *subst.get(v).ok_or_else(|| unbound(v.clone()))?,
    };
    let rhs = program.refresh_binders(&mut store.term_dag, rhs);
    if let Rhs::Term(t) = &rule.rhs {
        for var in pattern_vars(&store.term_dag, *t) {
            if body_vars.contains(&var) {
                continue;
            }
            if !var.starts_with('$') {
                return Err(fail(format!("{var} occurs only on the right-hand side")));
            }
            let minted = *subst.get(&var).ok_or_else(|| unbound(var.clone()))?;
            let slot = slot_of(&store.term_dag, minted)
                .ok_or_else(|| fail(format!("minted {var} is bound to a non-slot")))?;
            let used: BTreeSet<i64> = substitution
                .iter()
                .filter(|(name, _)| *name != var)
                .flat_map(|(_, t)| all_slots(&store.term_dag, *t))
                .collect();
            if used.contains(&slot) {
                return Err(fail(format!(
                    "minted {var} is ${slot}, which another binding mentions"
                )));
            }
        }
    }

    // The conclusion: the instance in either direction, or reflexivity of a subterm.
    let instance =
        (claimed.lhs, claimed.rhs) == (lhs, rhs) || (claimed.lhs, claimed.rhs) == (rhs, lhs);
    let reflexive = claimed.lhs == claimed.rhs
        && (is_subterm(&store.term_dag, claimed.lhs, lhs)
            || is_subterm(&store.term_dag, claimed.lhs, rhs));
    if !(instance || reflexive) {
        return Err(fail(format!(
            "concludes {}, but the instance is {} = {}",
            store.proposition_to_string(claimed),
            store.term_dag.to_string(lhs),
            store.term_dag.to_string(rhs)
        )));
    }
    // reflexivity of a subterm is about that subterm's sort
    let sort = if instance {
        sort
    } else {
        program.sort_of(&store.term_dag, claimed.lhs)
    };
    Ok((claimed.clone(), sort))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slotted::proofs::source::ColumnKind;
    use crate::slotted::proofs::terms::{Renaming, slot_term};

    fn figure_3() -> (SlottedProofStore, SlottedProgram, Claim) {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Mul", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor("Null", vec![]);
        program.add_let(&mut dag, "m7", "(Mul $7 (Null))").unwrap();
        program.add_let(&mut dag, "zero", "(Null)").unwrap();
        program.add_union(&mut dag, "m7", "zero", "U").unwrap();
        let claim = program
            .claim(&mut dag, "=", "U", "(Mul $9 (Null))", "zero")
            .unwrap();
        (SlottedProofStore::new(dag), program, claim)
    }

    #[test]
    fn redundancy_by_equivariance() {
        let (mut store, program, claim) = figure_3();
        let (m7, zero) = (program.lets["m7"], program.lets["zero"]);
        let union = store.fiat(m7, zero);
        let back = store.sym(union);
        let renamed = store.equivariance(back, Renaming::new([(7, 9), (9, 7)]).unwrap());
        let proof = store.sym(renamed);
        let proven = check_proof(&mut store, &program, proof).unwrap();
        // Equivariance acts on both endpoints; `(Null)` has no slots.
        assert_eq!(
            store.proposition_to_string(&proven.proposition),
            "(Mul $9 (Null)) = (Null)"
        );
        assert_eq!(proven.sort.as_deref(), Some("U"));
        check_claim(
            &mut store,
            &program,
            &claim,
            &SlottedConclusion {
                proof,
                renaming: Renaming::identity(),
            },
        )
        .unwrap();
        let text = store.proof_to_string(proof);
        assert!(
            text.contains("(Equivariance") && text.contains("(renaming ($7 $9) ($9 $7))"),
            "{text}"
        );
    }

    #[test]
    fn a_non_injective_equivariance_cannot_be_stated() {
        assert!(Renaming::new([(0, 1)]).is_none());
    }

    #[test]
    fn equivariance_checks_both_endpoints() {
        let (mut store, program, _) = figure_3();
        let (term, zero) = (program.lets["m7"], program.lets["zero"]);
        let union = store.fiat(term, zero);
        let sigma = Renaming::new([(7, 9), (9, 7)]).unwrap();
        let transported = store.equivariance(union, sigma.clone());
        assert_eq!(
            check_proof(&mut store, &program, transported)
                .unwrap()
                .sort
                .as_deref(),
            Some("U")
        );
        let forged = store.add(
            SlottedProposition::equal(term, zero),
            SlottedJustification::Equivariance {
                proof: union,
                renaming: sigma,
            },
        );
        assert!(matches!(
            check_proof(&mut store, &program, forged),
            Err(SlottedCheckError::Step {
                step: "conclusion",
                ..
            })
        ));
    }

    #[test]
    fn claim_witnesses_distinguish_free_and_bound_names() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_let(&mut dag, "free", "(F $0)").unwrap();
        program.add_let(&mut dag, "bound", "(Lam $0 $0)").unwrap();
        let free = program.claim(&mut dag, "=", "U", "free", "(F $1)").unwrap();
        let bound = program
            .claim(&mut dag, "=", "U", "bound", "(Lam $1 $1)")
            .unwrap();
        let mut store = SlottedProofStore::new(dag);
        let proof = store.fiat(free.lhs, free.lhs);
        let witness = SlottedConclusion {
            proof,
            renaming: Renaming::new([(0, 1), (1, 0)]).unwrap(),
        };
        assert!(check_claim(&mut store, &program, &free, &witness).is_err());
        let renaming_claim = Claim {
            kind: ClaimKind::RenamingEq,
            ..free
        };
        check_claim(&mut store, &program, &renaming_claim, &witness).unwrap();
        let wrong = SlottedConclusion {
            renaming: Renaming::identity(),
            ..witness.clone()
        };
        assert!(check_claim(&mut store, &program, &renaming_claim, &wrong).is_err());
        let proof = store.fiat(bound.lhs, bound.lhs);
        check_claim(
            &mut store,
            &program,
            &bound,
            &SlottedConclusion { proof, ..witness },
        )
        .unwrap();
    }

    #[test]
    fn rule_side_patterns_accept_alpha_names_but_reject_free_renaming() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_constructor("Pair", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_constructor("K", vec![]);
        program
            .add_let(&mut dag, "child", "(Lam $0 (Pair $0 $3))")
            .unwrap();
        program.add_let(&mut dag, "root", "(F child)").unwrap();
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (F x) (K) :when ((= x (Lam $a (Pair $a $b)))) :name "r")"#,
            )
            .unwrap();
        let (root, child) = (program.lets["root"], program.lets["child"]);
        let mut store = SlottedProofStore::new(dag);
        let premise = store.fiat(root, root);
        let side = store.fiat(child, child);
        let k = store.term_dag.app("K".into(), vec![]);
        let a = slot_term(&mut store.term_dag, 1);
        for (free_slot, valid) in [(3, true), (4, false)] {
            let b = slot_term(&mut store.term_dag, free_slot);
            let rule = store.add(
                SlottedProposition::equal(root, k),
                SlottedJustification::Rule {
                    name: "r".into(),
                    substitution: vec![("x".into(), child), ("$a".into(), a), ("$b".into(), b)],
                    premises: vec![premise, side],
                },
            );
            assert_eq!(check_proof(&mut store, &program, rule).is_ok(), valid);
        }
    }

    #[test]
    fn fiat_needs_a_built_term_or_a_union() {
        let (mut store, program, _claim) = figure_3();
        let s9 = slot_term(&mut store.term_dag, 9);
        let null = store.term_dag.app("Null".into(), vec![]);
        let bogus = store.term_dag.app("Mul".into(), vec![s9, null]);
        let proof = store.fiat(bogus, bogus);
        let err = check_proof(&mut store, &program, proof).unwrap_err();
        assert!(
            matches!(err, SlottedCheckError::InvalidFiat { .. }),
            "{err}"
        );
        let wrong = store.fiat(null, bogus);
        assert!(check_proof(&mut store, &program, wrong).is_err());
    }

    #[test]
    fn free_name_guards_check_the_instantiated_terms() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child; 3]);
        program.add_let(&mut dag, "input", "(F $0 $1 $0)").unwrap();
        let cases = [
            ("free $s x y", true),
            ("not-free $s x y", false),
            ("free-names-are x $s", false),
            ("free-names-are y $s", true),
            ("free-names-are y", false),
        ];
        for (i, (condition, _)) in cases.iter().enumerate() {
            program
                .add_rewrite(
                    &mut dag,
                    &format!("(rewrite (F $s x y) y :name \"guard{i}\" :when (({condition})))"),
                )
                .unwrap();
        }
        let mut store = SlottedProofStore::new(dag);
        let input = program.lets["input"];
        let zero = slot_term(&mut store.term_dag, 0);
        let one = slot_term(&mut store.term_dag, 1);
        let root = store.fiat(input, input);
        for (i, (condition, valid)) in cases.iter().enumerate() {
            let proof = store.add(
                SlottedProposition::equal(input, zero),
                SlottedJustification::Rule {
                    name: format!("guard{i}"),
                    substitution: vec![("$s".into(), zero), ("x".into(), one), ("y".into(), zero)],
                    premises: vec![root],
                },
            );
            assert_eq!(
                check_proof(&mut store, &program, proof).is_ok(),
                *valid,
                "{condition}"
            );
        }
    }

    #[test]
    fn rule_instances_and_minted_slots() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_constructor("App", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor("Num", vec![ColumnKind::Payload]);
        program
            .add_let(&mut dag, "t", "(F (Num 1) (Num 2))")
            .unwrap();
        program.add_let(&mut dag, "u", "(F $1 (Num 2))").unwrap();
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (F x y) (Lam $s (App (F x y) $s)) :name "wrap")"#,
            )
            .unwrap();
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (Lam $x (App f $x)) f :name "eta" :when ((not-free $x f)))"#,
            )
            .unwrap();
        let mut store = SlottedProofStore::new(dag);
        let t = program.lets["t"];
        let one = store.term_dag.lit(egglog::ast::Literal::Int(1));
        let two = store.term_dag.lit(egglog::ast::Literal::Int(2));
        let num1 = store.term_dag.app("Num".into(), vec![one]);
        let num2 = store.term_dag.app("Num".into(), vec![two]);
        let s4 = slot_term(&mut store.term_dag, 4);
        let app = store.term_dag.app("App".into(), vec![t, s4]);
        let wrapped = store.term_dag.app("Lam".into(), vec![s4, app]);
        // a rule instance is stated with its binders named apart
        let wrapped = program.refresh_binders(&mut store.term_dag, wrapped);

        let root = store.fiat(t, t);
        let wrap = store.add(
            SlottedProposition::equal(t, wrapped),
            SlottedJustification::Rule {
                name: "wrap".into(),
                substitution: vec![("x".into(), num1), ("y".into(), num2), ("$s".into(), s4)],
                premises: vec![root],
            },
        );
        check_proof(&mut store, &program, wrap).unwrap();

        // eta on the wrapped term: (Lam $4 (App t $4)) = t, with $4 not free in t
        let eta = store.add(
            SlottedProposition::equal(wrapped, t),
            SlottedJustification::Rule {
                name: "eta".into(),
                substitution: vec![("$x".into(), s4), ("f".into(), t)],
                premises: vec![wrap],
            },
        );
        check_proof(&mut store, &program, eta).unwrap();

        // minting a slot the other bindings mention is refused
        let s1 = slot_term(&mut store.term_dag, 1);
        let f1 = store.term_dag.app("F".into(), vec![s1, num2]);
        let app1 = store.term_dag.app("App".into(), vec![f1, s1]);
        let bad_wrapped = store.term_dag.app("Lam".into(), vec![s1, app1]);
        let f1_root = store.add(
            SlottedProposition::equal(f1, f1),
            SlottedJustification::Fiat,
        );
        let bad = store.add(
            SlottedProposition::equal(f1, bad_wrapped),
            SlottedJustification::Rule {
                name: "wrap".into(),
                substitution: vec![("x".into(), s1), ("y".into(), num2), ("$s".into(), s1)],
                premises: vec![f1_root],
            },
        );
        let err = check_proof(&mut store, &program, bad).unwrap_err();
        assert!(err.to_string().contains("minted"), "{err}");
    }
    #[test]
    fn slot_literals_are_distinct_slots() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor("A", vec![]);
        program.add_let(&mut dag, "ff", "(F $0 $0)").unwrap();
        program.add_let(&mut dag, "fa", "(F (A) $0)").unwrap();
        program
            .add_rewrite(&mut dag, r#"(rewrite (F $x $y) (A) :name "distinct")"#)
            .unwrap();
        let mut store = SlottedProofStore::new(dag);
        let (ff, fa) = (program.lets["ff"], program.lets["fa"]);
        let a = store.term_dag.app("A".into(), vec![]);
        let s0 = slot_term(&mut store.term_dag, 0);
        let root = store.fiat(ff, ff);
        // `(F $x $y)` does not match `(F $0 $0)`: two literals, one slot
        let aliased = store.add(
            SlottedProposition::equal(ff, a),
            SlottedJustification::Rule {
                name: "distinct".into(),
                substitution: vec![("$x".into(), s0), ("$y".into(), s0)],
                premises: vec![root],
            },
        );
        let err = check_proof(&mut store, &program, aliased).unwrap_err();
        assert!(err.to_string().contains("different slot literals"), "{err}");
        // a slot literal is bound to a slot, never to a term
        let root = store.fiat(fa, fa);
        let non_slot = store.add(
            SlottedProposition::equal(fa, a),
            SlottedJustification::Rule {
                name: "distinct".into(),
                substitution: vec![("$x".into(), a), ("$y".into(), s0)],
                premises: vec![root],
            },
        );
        let err = check_proof(&mut store, &program, non_slot).unwrap_err();
        assert!(err.to_string().contains("not a slot"), "{err}");
    }

    #[test]
    fn equalities_stay_in_their_sort() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_sorted_constructor("WA", "A", vec![(ColumnKind::Child, "A".into())]);
        program.add_sorted_constructor("WB", "B", vec![(ColumnKind::Child, "B".into())]);
        program.add_let(&mut dag, "wa0", "(WA $0)").unwrap();
        program.add_let(&mut dag, "wa1", "(WA $1)").unwrap();
        program.add_let(&mut dag, "wb0", "(WB $0)").unwrap();
        program.add_union(&mut dag, "wa0", "wa1", "A").unwrap();
        program
            .add_rewrite(&mut dag, r#"(rewrite (WA x) x :name "unwrap")"#)
            .unwrap();
        let mut store = SlottedProofStore::new(dag);
        let (wa0, wa1, wb0) = (
            program.lets["wa0"],
            program.lets["wa1"],
            program.lets["wb0"],
        );
        let s0 = slot_term(&mut store.term_dag, 0);
        let s1 = slot_term(&mut store.term_dag, 1);
        let unwrap = |store: &mut SlottedProofStore, term: TermId, slot: TermId| {
            let root = store.fiat(term, term);
            store.add(
                SlottedProposition::equal(term, slot),
                SlottedJustification::Rule {
                    name: "unwrap".into(),
                    substitution: vec![("x".into(), slot)],
                    premises: vec![root],
                },
            )
        };
        // in A: $0 = (WA $0) = (WA $1) = $1
        let p0 = unwrap(&mut store, wa0, s0);
        let p1 = unwrap(&mut store, wa1, s1);
        let union = store.fiat(wa0, wa1);
        let back = store.sym(p0);
        let left = store.trans(back, union).unwrap();
        let slots = store.trans(left, p1).unwrap();
        let proven = check_proof(&mut store, &program, slots).unwrap();
        assert_eq!(store.proposition_to_string(&proven.proposition), "$0 = $1");
        assert_eq!(proven.sort.as_deref(), Some("A"));
        // which says nothing about B's slots
        let refl = store.fiat(wb0, wb0);
        let crossed = store.congr(refl, 0, slots).unwrap();
        let err = check_proof(&mut store, &program, crossed).unwrap_err();
        assert!(err.to_string().contains("column 0 of WB is B"), "{err}");
    }

    #[test]
    fn variable_root_rules_keep_the_sort_of_their_binding() {
        for (rule, premise) in [
            (
                r#"(rewrite x y :when ((= p (PairA x y))) :name "r")"#,
                ("pair", "pair"),
            ),
            (
                r#"(rewrite x y :when ((= x (WA y))) :name "r")"#,
                ("zero", "wa"),
            ),
        ] {
            let mut dag = TermDag::default();
            let mut program = SlottedProgram::default();
            program.add_sorted_constructor("PairA", "A", vec![(ColumnKind::Child, "A".into()); 2]);
            program.add_sorted_constructor("WA", "A", vec![(ColumnKind::Child, "A".into())]);
            program.add_sorted_constructor("WB", "B", vec![(ColumnKind::Child, "B".into())]);
            for (name, term) in [
                ("zero", "$0"),
                ("one", "$1"),
                ("pair", "(PairA $0 $1)"),
                ("wa", "(WA $1)"),
                ("wb", "(WB $0)"),
            ] {
                program.add_let(&mut dag, name, term).unwrap();
            }
            program.add_union(&mut dag, "zero", "wa", "A").unwrap();
            program.add_rewrite(&mut dag, rule).unwrap();
            let (s0, s1, wb) = (
                program.lets["zero"],
                program.lets["one"],
                program.lets["wb"],
            );
            let mut store = SlottedProofStore::new(dag);
            let root = store.fiat(s0, s0);
            let side = store.fiat(program.lets[premise.0], program.lets[premise.1]);
            let proof = store.add(
                SlottedProposition::equal(s0, s1),
                SlottedJustification::Rule {
                    name: "r".into(),
                    substitution: vec![
                        ("x".into(), s0),
                        ("y".into(), s1),
                        ("p".into(), program.lets["pair"]),
                    ],
                    premises: vec![root, side],
                },
            );
            assert_eq!(
                check_proof(&mut store, &program, proof)
                    .unwrap()
                    .sort
                    .as_deref(),
                Some("A")
            );
            let refl = store.fiat(wb, wb);
            let crossed = store.congr(refl, 0, proof).unwrap();
            let err = check_proof(&mut store, &program, crossed).unwrap_err();
            assert!(err.to_string().contains("column 0 of WB is B"), "{err}");
        }
    }

    #[test]
    fn corrupt_and_cyclic_proofs_are_rejected() {
        let (mut store, program, _claim) = figure_3();
        let (m7, zero) = (program.lets["m7"], program.lets["zero"]);
        let union = store.fiat(m7, zero);
        let refl = store.fiat(m7, m7);
        // a transitivity whose middle terms differ
        let trans = store.add(
            SlottedProposition::equal(m7, m7),
            SlottedJustification::Trans(union, refl),
        );
        let err = check_proof(&mut store, &program, trans).unwrap_err();
        assert!(err.to_string().contains("middle terms differ"), "{err}");
        // a congruence whose child proof is about another term
        let congr = store.add(
            SlottedProposition::equal(m7, m7),
            SlottedJustification::Congr {
                proof: refl,
                child_index: 1,
                child_proof: union,
            },
        );
        let err = check_proof(&mut store, &program, congr).unwrap_err();
        assert!(err.to_string().contains("child proof's left side"), "{err}");
        // a step stating something other than what it derives
        let sym = store.add(
            SlottedProposition::equal(m7, zero),
            SlottedJustification::Sym(union),
        );
        let err = check_proof(&mut store, &program, sym).unwrap_err();
        assert!(
            matches!(
                err,
                SlottedCheckError::Step {
                    step: "conclusion",
                    ..
                }
            ),
            "{err}"
        );
        // a proof that depends on itself
        let next = store.len();
        let first = store.add(
            SlottedProposition::equal(zero, m7),
            SlottedJustification::Sym(next + 1),
        );
        assert_eq!(first, next);
        let second = store.add(
            SlottedProposition::equal(m7, zero),
            SlottedJustification::Sym(first),
        );
        let err = check_proof(&mut store, &program, second).unwrap_err();
        assert!(err.to_string().contains("cyclic"), "{err}");
    }
}
