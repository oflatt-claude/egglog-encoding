//! Checks surface proofs against the slotted source program.

use super::format::{
    Claim, ClaimKind, SlottedConclusion, SlottedJustification, SlottedPremise, SlottedProofId,
    SlottedProofStore, SlottedProposition,
};
use super::source::{ColumnKind, Requirement, SlottedProgram, SourceFact, pattern_term};
use super::terms::{all_slots, rename, slot_of};
use super::{HashMap, HashSet};
use egglog::ast::{Literal, ResolvedExpr, ResolvedExprExt, ResolvedFact};
use egglog::proof::{
    Justification, Proof, ProofCheckContext, ProofId, ProofStore, Proposition,
    check_actions_produce_equality, check_fact_matches_proposition,
};
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
    let mut ordinary = ProofStore::new(
        std::mem::take(&mut store.term_dag),
        HashMap::default(),
        HashSet::default(),
    );
    let context = ProofCheckContext::new(&[], ordinary.term_dag_mut())
        .expect("an empty program has no invalid axioms");
    let result = (|| {
        let mut checked = HashMap::default();
        for id in store.dependencies(root) {
            let result = check_one(store, &mut ordinary, &context, program, id, &checked)?;
            checked.insert(ordinary_id(id), result);
        }
        Ok(checked[&ordinary_id(root)].clone())
    })();
    store.term_dag = std::mem::take(ordinary.term_dag_mut());
    result
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

fn ordinary_id(id: SlottedProofId) -> ProofId {
    ProofId::new_const(id.try_into().expect("proof ID exceeds u32"))
}

fn proposition_string(dag: &TermDag, p: &SlottedProposition) -> String {
    format!("{} = {}", dag.to_string(p.lhs), dag.to_string(p.rhs))
}

fn check_one(
    store: &SlottedProofStore,
    ordinary: &mut ProofStore,
    context: &ProofCheckContext,
    program: &SlottedProgram,
    id: SlottedProofId,
    checked: &HashMap<ProofId, Checked>,
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
        checked.get(&ordinary_id(*p)).cloned().ok_or_else(|| {
            step(
                "premise",
                format!("proof #{p} is used before it is established: the proof is cyclic"),
            )
        })
    };
    let dag = ordinary.term_dag_mut();
    for term in [claimed.lhs, claimed.rhs] {
        check_term_sort(program, dag, term, None).map_err(|e| step("sort", e))?;
    }
    let (derived, sort) = match &proof.justification {
        SlottedJustification::Fiat => {
            let reflexive = claimed.lhs == claimed.rhs && program.is_built(dag, claimed.lhs);
            let union = program.union_sort(claimed.lhs, claimed.rhs).is_some();
            if !(reflexive || union) {
                return Err(SlottedCheckError::InvalidFiat {
                    proof: id,
                    claim: proposition_string(dag, &claimed),
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
                .map(|p| Ok((p.clone(), premise(&p.proof())?)))
                .collect::<Result<Vec<_>, _>>()?;
            check_rule(dag, program, id, name, substitution, &premises, &claimed)?
        }
        SlottedJustification::Sym(inner) => (claimed.clone(), premise(inner)?.sort),
        SlottedJustification::Alpha(inner) => {
            let p = premise(inner)?;
            if !program.alpha_eq(dag, p.proposition.rhs, claimed.rhs) {
                return Err(step(
                    "alpha",
                    "right endpoints are not alpha-equivalent".into(),
                ));
            }
            (
                SlottedProposition::equal(p.proposition.lhs, claimed.rhs),
                p.sort,
            )
        }
        SlottedJustification::Trans(left, right) => {
            let (l, r) = (premise(left)?, premise(right)?);
            let sort = join_sorts(l.sort, r.sort)
                .map_err(|(a, b)| step("trans", format!("joins a proof in {a} with one in {b}")))?;
            (claimed.clone(), sort)
        }
        SlottedJustification::Congr {
            proof: inner,
            child_index,
            child_proof,
        } => {
            let (p, c) = (premise(inner)?, premise(child_proof)?);
            let Term::App(head, _) = dag.get(p.proposition.rhs).clone() else {
                return Err(step(
                    "congr",
                    "right-hand side is not an application".into(),
                ));
            };
            // the child proof is about the column's sort
            let ctor = program
                .constructors
                .get(&head)
                .ok_or_else(|| step("congr", format!("unknown constructor {head}")))?;
            let column_sort = ctor
                .column_sort(*child_index)
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
            (claimed.clone(), p.sort.or(Some(ctor.sort.clone())))
        }
        SlottedJustification::Proj { proof, child_index } => {
            let p = premise(proof)?;
            let Term::App(head, children) = dag.get(p.proposition.rhs) else {
                return Err(step("proj", "parent is not an application".into()));
            };
            children
                .get(*child_index)
                .ok_or_else(|| step("proj", "index out of bounds".into()))?;
            let sort = program
                .constructors
                .get(head)
                .and_then(|c| c.column_sort(*child_index))
                .map(str::to_owned);
            (claimed.clone(), sort)
        }
        SlottedJustification::Equivariance {
            proof: inner,
            renaming,
        } => {
            let p = premise(inner)?;
            let lhs = rename(dag, renaming, p.proposition.lhs);
            let rhs = rename(dag, renaming, p.proposition.rhs);
            (SlottedProposition::equal(lhs, rhs), p.sort)
        }
    };
    let justification = match &proof.justification {
        SlottedJustification::Sym(p) => Some(Justification::Sym(ordinary_id(*p))),
        SlottedJustification::Trans(a, b) => {
            Some(Justification::Trans(ordinary_id(*a), ordinary_id(*b)))
        }
        SlottedJustification::Congr {
            proof,
            child_index,
            child_proof,
        } => Some(Justification::Congr {
            proof: ordinary_id(*proof),
            child_index: *child_index,
            child_proof: ordinary_id(*child_proof),
        }),
        SlottedJustification::Proj { proof, child_index } => Some(Justification::Proj {
            proof: ordinary_id(*proof),
            child_index: *child_index,
        }),
        _ => None,
    };
    if let Some(justification) = justification {
        let proof = Proof::new(Proposition::new(claimed.lhs, claimed.rhs), justification);
        ordinary
            .check_step(ordinary_id(id), &proof, &[], context, |_, premise| {
                let p = &checked[&premise].proposition;
                Ok(Proposition::new(p.lhs, p.rhs))
            })
            .map_err(|e| step("equality", e.to_string()))?;
    }
    let dag = ordinary.term_dag();
    if derived != claimed {
        return Err(step(
            "conclusion",
            format!(
                "states {} but derives {}",
                proposition_string(dag, &claimed),
                proposition_string(dag, &derived)
            ),
        ));
    }
    Ok(Checked {
        proposition: claimed,
        sort,
    })
}

/// The sort each variable of a pattern must take, from the columns it occurs in.
fn check_term_sort(
    program: &SlottedProgram,
    dag: &TermDag,
    term: TermId,
    expected: Option<&str>,
) -> Result<(), String> {
    let actual = match dag.get(term) {
        Term::Lit(Literal::Int(_)) => Some("i64"),
        Term::Lit(Literal::String(_)) => Some("String"),
        Term::Lit(_) => return Err("unsupported payload literal".into()),
        Term::Var(_) if slot_of(dag, term).is_some() => None,
        Term::Var(v) => return Err(format!("uninstantiated variable {v}")),
        Term::App(head, children) => {
            let ctor = program
                .constructors
                .get(head)
                .ok_or_else(|| format!("unknown constructor {head}"))?;
            if children.len() != ctor.columns.len() {
                return Err(format!("wrong arity for {head}"));
            }
            for ((&child, kind), sort) in children.iter().zip(&ctor.columns).zip(ctor.input_sorts())
            {
                if *kind == ColumnKind::Binder && slot_of(dag, child).is_none() {
                    return Err(format!("{head} requires a slot in its binder column"));
                }
                check_term_sort(program, dag, child, Some(sort))?;
            }
            Some(ctor.sort.as_str())
        }
    };
    if let Some(expected) = expected {
        let matches = match actual {
            Some(actual) => actual == expected,
            None => !matches!(expected, "i64" | "String"),
        };
        if !matches {
            return Err(format!(
                "{} has sort {}, expected {expected}",
                dag.to_string(term),
                actual.unwrap_or("slot")
            ));
        }
    }
    Ok(())
}

fn check_rule(
    dag: &mut TermDag,
    program: &SlottedProgram,
    id: SlottedProofId,
    name: &str,
    substitution: &[(String, TermId)],
    premises: &[(SlottedPremise, Checked)],
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
    if subst.len() != substitution.len() {
        return Err(fail("duplicate substitution variable".into()));
    }
    if let Some(name) = subst.keys().find(|name| rule.globals.contains_key(*name)) {
        return Err(fail(format!(
            "substitution overrides captured global {name}"
        )));
    }
    let mut bindings = subst.clone();
    bindings.extend(
        rule.globals
            .iter()
            .map(|(name, &term)| (name.clone(), term)),
    );
    let unbound = |variable: String| SlottedCheckError::Unbound {
        proof: id,
        name: name.to_string(),
        variable,
    };

    let requirements: Vec<_> = rule
        .conditions()
        .iter()
        .flat_map(SourceFact::requirements)
        .collect();
    let expected = 1 + requirements.len();
    if premises.len() != expected {
        return Err(SlottedCheckError::PremiseCount {
            proof: id,
            name: name.to_owned(),
            expected,
            actual: premises.len(),
        });
    }
    let (lhs_expr, rhs_expr) = rule.endpoints();
    let lhs_pattern = pattern_term(dag, lhs_expr);
    let rhs_pattern = pattern_term(dag, rhs_expr);
    let sort = lhs_expr.output_type().name().to_owned();
    for var in rule.patterns().flat_map(|expr| expr.vars()) {
        let term = *bindings
            .get(&var.name)
            .ok_or_else(|| unbound(var.name.clone()))?;
        check_term_sort(program, dag, term, Some(var.sort.name()))
            .map_err(|e| fail(format!("binding {}: {e}", var.name)))?;
    }

    // Slot literals: each is bound to a slot, and different literals to different
    // slots -- `(F $x $y)` does not match `(F $0 $0)`.
    let literals: Vec<_> = rule
        .patterns()
        .flat_map(|expr| expr.vars())
        .filter(|var| program.sorts.contains(var.sort.name()))
        .map(|var| var.name)
        .filter(|name| !rule.globals.contains_key(name))
        .collect();
    let mut by_slot: HashMap<i64, String> = HashMap::default();
    for literal in literals.iter().filter(|v| v.starts_with('$')) {
        let term = *subst.get(literal).ok_or_else(|| unbound(literal.clone()))?;
        let slot = slot_of(dag, term).ok_or_else(|| {
            fail(format!(
                "{literal} is bound to {}, not a slot",
                dag.to_string(term)
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

    let lhs = rule
        .instantiate(dag, lhs_pattern, &subst)
        .map_err(unbound)?;
    let (SlottedPremise::Equality(_), root) = &premises[0] else {
        return Err(fail(
            "root pattern requires ordinary equality evidence".into(),
        ));
    };
    let root = &root.proposition;
    check_fact_matches_proposition(
        dag,
        &rule.rule.body[0],
        &Proposition::new(root.lhs, root.rhs),
        &bindings,
        name,
    )
    .map_err(|e| fail(format!("root premise: {e}")))?;
    join_sorts(Some(sort.clone()), premises[0].1.sort.clone())
        .map_err(|(a, b)| fail(format!("the rewrite is in {a}, its root premise in {b}")))?;
    for (requirement, (evidence, premise)) in requirements.iter().zip(&premises[1..]) {
        let got = &premise.proposition;
        let (fact, condition_sort) = match requirement {
            Requirement::Exists(expr) => (
                Some(ResolvedFact::Fact((*expr).clone())),
                expr.output_type().name().to_owned(),
            ),
            Requirement::Equal(a, b) => (
                Some(ResolvedFact::Eq(
                    egglog::span!(),
                    (*a).clone(),
                    (*b).clone(),
                )),
                a.output_type().name().to_owned(),
            ),
            Requirement::RenamingEqual(a, b) => {
                let left = pattern_term(dag, a);
                let right = pattern_term(dag, b);
                let left = rule.instantiate(dag, left, &subst).map_err(unbound)?;
                let right = rule.instantiate(dag, right, &subst).map_err(unbound)?;
                let SlottedPremise::Renaming { renaming, .. } = evidence else {
                    return Err(fail(
                        "renaming-= requires an explicit permutation witness".into(),
                    ));
                };
                let renamed = rename(dag, renaming, right);
                if got.lhs != left || !program.alpha_eq(dag, got.rhs, renamed) {
                    return Err(fail(
                        "premise does not establish the original renaming-= guard".into(),
                    ));
                }
                (None, a.output_type().name().to_owned())
            }
        };
        if let Some(fact) = fact {
            if !matches!(evidence, SlottedPremise::Equality(_)) {
                return Err(fail(
                    "ordinary fact requires ordinary equality evidence".into(),
                ));
            }
            check_fact_matches_proposition(
                dag,
                &fact,
                &Proposition::new(got.lhs, got.rhs),
                &bindings,
                name,
            )
            .map_err(|e| fail(format!("original :when fact: {e}")))?;
        }
        join_sorts(Some(condition_sort), premise.sort.clone())
            .map_err(|(a, b)| fail(format!("condition is in {a}, its premise in {b}")))?;
    }

    let instance = |dag: &mut TermDag, expr: &ResolvedExpr| {
        let pattern = pattern_term(dag, expr);
        rule.instantiate(dag, pattern, &subst).map_err(unbound)
    };
    for condition in rule.conditions() {
        let ResolvedFact::Fact(ResolvedExpr::Call(_, egglog::ResolvedCall::Primitive(head), args)) =
            condition
        else {
            continue;
        };
        let head = head.name();
        match (head, args.as_slice()) {
            ("free" | "not-free", [slot, terms @ ..]) => {
                let slot = instance(dag, slot)?;
                let slot = slot_of(dag, slot)
                    .ok_or_else(|| fail("free/not-free requires a slot".into()))?;
                let mut free = BTreeSet::new();
                for term in terms {
                    let term = instance(dag, term)?;
                    free.extend(program.free_slots(dag, term));
                }
                if free.contains(&slot) != (head == "free") {
                    return Err(fail(format!(
                        "{head} fails for ${slot}: free slots are {free:?}"
                    )));
                }
            }
            ("free-names-are", [term, slots @ ..]) => {
                let term = instance(dag, term)?;
                let wanted = slots
                    .iter()
                    .map(|slot| {
                        let term = instance(dag, slot)?;
                        slot_of(dag, term)
                            .ok_or_else(|| fail("free-names-are requires slots".into()))
                    })
                    .collect::<Result<BTreeSet<_>, _>>()?;
                let free = program.free_slots(dag, term);
                if free != wanted {
                    return Err(fail(format!(
                        "free-names-are: expected {wanted:?}, found {free:?}"
                    )));
                }
            }
            ("!=" | "renaming-!=", [a, b]) => {
                let a = instance(dag, a)?;
                let b = instance(dag, b)?;
                let equal = if head == "renaming-!=" {
                    program.eq_modulo_renaming(dag, a, b)
                } else {
                    program.alpha_eq(dag, a, b)
                };
                if equal {
                    return Err(fail(format!("{head} fails for {}", dag.to_string(a))));
                }
            }
            _ => {}
        }
    }

    // Right-hand-side slot literals absent from the body must be fresh.
    let body_vars: HashSet<String> = rule
        .rule
        .body
        .iter()
        .flat_map(SourceFact::terms)
        .flat_map(|expr| expr.vars())
        .map(|var| var.name)
        .collect();
    let rhs = rule
        .instantiate(dag, rhs_pattern, &subst)
        .map_err(unbound)?;
    for var in rule.pattern_vars(dag, rhs_pattern) {
        if body_vars.contains(&var) {
            continue;
        }
        if !var.starts_with('$') {
            return Err(fail(format!("{var} occurs only on the right-hand side")));
        }
        let minted = *subst.get(&var).ok_or_else(|| unbound(var.clone()))?;
        let slot = slot_of(dag, minted)
            .ok_or_else(|| fail(format!("minted {var} is bound to a non-slot")))?;
        let used: BTreeSet<i64> = substitution
            .iter()
            .filter(|(name, _)| *name != var)
            .map(|(_, t)| t)
            .chain(rule.globals.values())
            .flat_map(|t| all_slots(dag, *t))
            .collect();
        if used.contains(&slot) {
            return Err(fail(format!(
                "minted {var} is ${slot}, which another binding mentions"
            )));
        }
    }

    // The conclusion: the instance in either direction, or reflexivity of a subterm.
    let instance =
        (claimed.lhs, claimed.rhs) == (lhs, rhs) || (claimed.lhs, claimed.rhs) == (rhs, lhs);
    let substitution = substitution.iter().cloned().collect();
    check_actions_produce_equality(
        dag,
        &rule.rule.head,
        &substitution,
        &bindings,
        &Proposition::new(claimed.lhs, claimed.rhs),
        name,
    )
    .map_err(|e| fail(e.to_string()))?;
    // reflexivity of a subterm is about that subterm's sort
    let sort = if instance {
        Some(sort)
    } else {
        program.sort_of(dag, claimed.lhs)
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
    fn alpha_checks_scopes_payloads_and_its_premise() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_sorted_constructor("Num", "U", vec![ColumnKind::Payload("i64".into())]);
        let source = "(Lam $0 (Lam $0 (Pair $0 (Pair $2 (Num 1)))))";
        program.add_let(&mut dag, "input", source).unwrap();
        let input = program.lets["input"];
        assert_eq!(dag.to_string(input), source);
        let mut store = SlottedProofStore::new(dag);
        let premise = store.fiat(input, input);
        for (target, valid) in [
            ("(Lam $3 (Lam $4 (Pair $4 (Pair $2 (Num 1)))))", true),
            ("(Lam $3 (Lam $4 (Pair $3 (Pair $2 (Num 1)))))", false),
            ("(Lam $2 (Lam $4 (Pair $4 (Pair $2 (Num 1)))))", false),
            ("(Lam $3 (Lam $4 (Pair $4 (Pair $5 (Num 1)))))", false),
            ("(Lam $3 (Lam $4 (Pair $4 (Pair $2 (Num 2)))))", false),
        ] {
            let rhs = program
                .claim(&mut store.term_dag, "=", "U", "input", target)
                .unwrap()
                .rhs;
            let proof = store.alpha(premise, rhs);
            assert_eq!(
                check_proof(&mut store, &program, proof).is_ok(),
                valid,
                "{target}"
            );
            if valid {
                let renamed = store.equivariance(proof, Renaming::new([(2, 6), (6, 2)]).unwrap());
                let simplified = store.simplify(renamed);
                assert_eq!(
                    check_proof(&mut store, &program, renamed).unwrap(),
                    check_proof(&mut store, &program, simplified).unwrap()
                );
                let changed_left = store.add(
                    SlottedProposition::equal(rhs, rhs),
                    SlottedJustification::Alpha(premise),
                );
                assert!(check_proof(&mut store, &program, changed_left).is_err());
                let invented = store.fiat(rhs, rhs);
                let proof = store.alpha(invented, input);
                assert!(check_proof(&mut store, &program, proof).is_err());
            }
        }
    }

    #[test]
    fn congruence_cannot_put_a_constructor_in_a_binder_column() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_constructor("K", vec![]);
        program.add_let(&mut dag, "input", "(Lam $0 $0)").unwrap();
        program.add_union(&mut dag, "$0", "(K)", "U").unwrap();
        let input = program.lets["input"];
        let union = &program.unions[0];
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        let child = store.fiat(union.lhs, union.rhs);
        let proof = store.congr(root, 0, child).unwrap();
        assert!(
            check_proof(&mut store, &program, proof)
                .unwrap_err()
                .to_string()
                .contains("binder column")
        );
    }

    #[test]
    fn source_globals_cannot_be_overridden_by_a_rule_substitution() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_let(&mut dag, "fixed", "$0").unwrap();
        program.add_let(&mut dag, "input", "(F $1)").unwrap();
        program
            .add_rewrite(&mut dag, r#"(rewrite (F x) fixed :name "r")"#)
            .unwrap();
        // A later scope cannot change what the rule captured.
        program.add_let(&mut dag, "fixed", "$2").unwrap();
        let input = program.lets["input"];
        let old = slot_term(&mut dag, 0);
        let x = slot_term(&mut dag, 1);
        let new = slot_term(&mut dag, 2);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        for (rhs, substitution, valid) in [
            (old, vec![("x".into(), x)], true),
            (new, vec![("x".into(), x)], false),
            (new, vec![("x".into(), x), ("fixed".into(), new)], false),
            (old, vec![("x".into(), x), ("fixed".into(), old)], false),
        ] {
            let proof = store.add(
                SlottedProposition::equal(input, rhs),
                SlottedJustification::Rule {
                    name: "r".into(),
                    substitution,
                    premises: vec![root].into_iter().map(Into::into).collect(),
                },
            );
            assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
        }
    }

    #[test]
    fn rule_side_patterns_require_explicit_alpha_and_preserve_free_names() {
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
        for (free_slot, convert, valid) in [(3, false, false), (3, true, true), (4, true, false)] {
            let b = slot_term(&mut store.term_dag, free_slot);
            let pair = store.term_dag.app("Pair".into(), vec![a, b]);
            let lam = store.term_dag.app("Lam".into(), vec![a, pair]);
            let side = if convert {
                store.alpha(side, lam)
            } else {
                side
            };
            let rule = store.add(
                SlottedProposition::equal(root, k),
                SlottedJustification::Rule {
                    name: "r".into(),
                    substitution: vec![("x".into(), child), ("$a".into(), a), ("$b".into(), b)],
                    premises: vec![premise, side].into_iter().map(Into::into).collect(),
                },
            );
            assert_eq!(check_proof(&mut store, &program, rule).is_ok(), valid);
        }
    }

    #[test]
    fn original_conditions_require_evidence_in_source_order() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        for name in ["F", "G", "H"] {
            program.add_constructor(name, vec![ColumnKind::Child]);
        }
        program.add_constructor("A", vec![]);
        program.add_let(&mut dag, "input", "(F (G (A)))").unwrap();
        program.add_let(&mut dag, "side", "(H (A))").unwrap();
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (F (G x)) (H x) :when ((= (G x) y) (H x)) :name "nested")"#,
            )
            .unwrap();
        let input = program.lets["input"];
        let side = program.lets["side"];
        let a = dag.app("A".into(), vec![]);
        let g = dag.app("G".into(), vec![a]);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        let equality = store.fiat(g, g);
        let existence = store.fiat(side, side);
        for (premises, valid) in [
            (vec![root, equality, existence], true),
            (vec![root, existence, equality], false),
            (vec![root, equality], false),
            (vec![root, equality, equality], false),
        ] {
            let proof = store.add(
                SlottedProposition::equal(input, side),
                SlottedJustification::Rule {
                    name: "nested".into(),
                    substitution: vec![("x".into(), a), ("y".into(), g)],
                    premises: premises.into_iter().map(Into::into).collect(),
                },
            );
            assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
        }
    }

    #[test]
    fn guard_captures_are_independent_of_a_constructor_with_the_same_name() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor(
            "free",
            vec![ColumnKind::Payload("i64".into()), ColumnKind::Child],
        );
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_constructor("Hit", vec![]);
        program.add_let(&mut dag, "n", "$0").unwrap();
        program.add_let(&mut dag, "input", "(Pair $1 $2)").unwrap();
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (Pair x y) (Hit) :when ((free n (Pair x y))) :name "guard")"#,
            )
            .unwrap();
        let input = program.lets["input"];
        let one = slot_term(&mut dag, 1);
        let two = slot_term(&mut dag, 2);
        let hit = dag.app("Hit".into(), vec![]);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        for override_global in [false, true] {
            let mut substitution = vec![("x".into(), one), ("y".into(), two)];
            if override_global {
                substitution.push(("n".into(), one));
            }
            let proof = store.add(
                SlottedProposition::equal(input, hit),
                SlottedJustification::Rule {
                    name: "guard".into(),
                    substitution,
                    premises: vec![root.into(), root.into()],
                },
            );
            let error = check_proof(&mut store, &program, proof)
                .unwrap_err()
                .to_string();
            assert!(
                error.contains(if override_global {
                    "overrides captured global"
                } else {
                    "free fails"
                }),
                "{error}"
            );
        }
    }

    #[test]
    fn renaming_guard_checks_an_equality_witness() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_constructor("G", vec![ColumnKind::Child]);
        program.add_constructor("Hit", vec![]);
        program.add_let(&mut dag, "a", "(F $0)").unwrap();
        program.add_let(&mut dag, "b", "(G $1)").unwrap();
        program.add_let(&mut dag, "input", "(Pair a b)").unwrap();
        program.add_union(&mut dag, "a", "(G $0)", "U").unwrap();
        for predicate in ["=", "renaming-="] {
            program.add_rewrite(&mut dag, &format!(
                r#"(rewrite (Pair x y) (Hit) :when (({predicate} x y)) :name "{predicate}")"#,
            )).unwrap();
        }
        let (a, b, input) = (program.lets["a"], program.lets["b"], program.lets["input"]);
        let hit = dag.app("Hit".into(), vec![]);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        let union = store.fiat(a, program.unions[0].rhs);
        let reflexive = store.fiat(a, a);
        let swap = Renaming::new([(0, 1), (1, 0)]).unwrap();
        for (predicate, evidence, valid) in [
            (
                "renaming-=",
                SlottedPremise::Renaming {
                    proof: union,
                    renaming: swap.clone(),
                },
                true,
            ),
            ("=", SlottedPremise::Equality(union), false),
            (
                "renaming-=",
                SlottedPremise::Renaming {
                    proof: reflexive,
                    renaming: swap,
                },
                false,
            ),
            ("renaming-=", SlottedPremise::Equality(union), false),
            (
                "renaming-=",
                SlottedPremise::Renaming {
                    proof: union,
                    renaming: Renaming::identity(),
                },
                false,
            ),
            (
                "=",
                SlottedPremise::Renaming {
                    proof: union,
                    renaming: Renaming::identity(),
                },
                false,
            ),
        ] {
            let proof = store.add(
                SlottedProposition::equal(input, hit),
                SlottedJustification::Rule {
                    name: predicate.into(),
                    substitution: vec![("x".into(), a), ("y".into(), b)],
                    premises: vec![root.into(), evidence],
                },
            );
            assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
        }
    }

    #[test]
    fn renaming_disequality_rejects_different_spellings_of_the_same_term() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_constructor("Hit", vec![]);
        program
            .add_let(&mut dag, "input", "(Pair (F $0) (F $1))")
            .unwrap();
        for predicate in ["!=", "renaming-!="] {
            program.add_rewrite(&mut dag, &format!(
                r#"(rewrite (Pair x y) (Hit) :when (({predicate} x y)) :name "{predicate}")"#,
            )).unwrap();
        }
        let input = program.lets["input"];
        let Term::App(_, children) = dag.get(input).clone() else {
            unreachable!()
        };
        let hit = dag.app("Hit".into(), vec![]);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        let x = store.project(root, 0).unwrap();
        let y = store.project(root, 1).unwrap();
        for (predicate, valid) in [("!=", true), ("renaming-!=", false)] {
            let proof = store.add(
                SlottedProposition::equal(input, hit),
                SlottedJustification::Rule {
                    name: predicate.into(),
                    substitution: vec![("x".into(), children[0]), ("y".into(), children[1])],
                    premises: vec![root, x, y].into_iter().map(Into::into).collect(),
                },
            );
            assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
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
        let x = store.project(root, 1).unwrap();
        let y = store.project(root, 2).unwrap();
        for (i, (condition, valid)) in cases.iter().enumerate() {
            let proof = store.add(
                SlottedProposition::equal(input, zero),
                SlottedJustification::Rule {
                    name: format!("guard{i}"),
                    substitution: vec![("$s".into(), zero), ("x".into(), one), ("y".into(), zero)],
                    premises: (if i < 2 {
                        vec![root, x, y]
                    } else if i == 2 {
                        vec![root, x]
                    } else {
                        vec![root, y]
                    })
                    .into_iter()
                    .map(Into::into)
                    .collect(),
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
        program.add_constructor("Num", vec![ColumnKind::Payload("i64".into())]);
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
        let root = store.fiat(t, t);
        let wrap = store.add(
            SlottedProposition::equal(t, wrapped),
            SlottedJustification::Rule {
                name: "wrap".into(),
                substitution: vec![("x".into(), num1), ("y".into(), num2), ("$s".into(), s4)],
                premises: vec![root].into_iter().map(Into::into).collect(),
            },
        );
        check_proof(&mut store, &program, wrap).unwrap();

        // eta on the wrapped term: (Lam $4 (App t $4)) = t, with $4 not free in t
        let eta = store.add(
            SlottedProposition::equal(wrapped, t),
            SlottedJustification::Rule {
                name: "eta".into(),
                substitution: vec![("$x".into(), s4), ("f".into(), t)],
                premises: vec![wrap, root].into_iter().map(Into::into).collect(),
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
                premises: vec![f1_root].into_iter().map(Into::into).collect(),
            },
        );
        let err = check_proof(&mut store, &program, bad).unwrap_err();
        assert!(err.to_string().contains("minted"), "{err}");
    }
    #[test]
    fn minted_slots_avoid_source_globals() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_let(&mut dag, "fixed", "$0").unwrap();
        program.add_let(&mut dag, "input", "(F $1)").unwrap();
        program
            .add_rewrite(&mut dag, r#"(rewrite (F x) (Pair fixed $fresh) :name "r")"#)
            .unwrap();
        let input = program.lets["input"];
        let zero = slot_term(&mut dag, 0);
        let one = slot_term(&mut dag, 1);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        for (slot, valid) in [(0, false), (1, false), (2, true), (37, true)] {
            let fresh = slot_term(&mut store.term_dag, slot);
            let rhs = store.term_dag.app("Pair".into(), vec![zero, fresh]);
            let proof = store.add(
                SlottedProposition::equal(input, rhs),
                SlottedJustification::Rule {
                    name: "r".into(),
                    substitution: vec![("x".into(), one), ("$fresh".into(), fresh)],
                    premises: vec![root].into_iter().map(Into::into).collect(),
                },
            );
            assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
        }
    }

    #[test]
    fn equality_conditions_keep_their_source_sort() {
        for condition in ["(= x y)", "(= fixed other)"] {
            let mut dag = TermDag::default();
            let mut program = SlottedProgram::default();
            program.add_sorted_constructor("PairA", "A", vec![ColumnKind::Child; 2]);
            program.add_sorted_constructor("HitA", "A", vec![]);
            program.add_let(&mut dag, "input", "(PairA $0 $1)").unwrap();
            program.add_let(&mut dag, "fixed", "$0").unwrap();
            program.add_let(&mut dag, "other", "$1").unwrap();
            program.add_union(&mut dag, "$0", "$1", "B").unwrap();
            program
                .add_rewrite(
                    &mut dag,
                    &format!(r#"(rewrite (PairA x y) (HitA) :when ({condition}) :name "r")"#),
                )
                .unwrap();
            let input = program.lets["input"];
            let zero = slot_term(&mut dag, 0);
            let one = slot_term(&mut dag, 1);
            let hit = dag.app("HitA".into(), vec![]);
            let mut store = SlottedProofStore::new(dag);
            let root = store.fiat(input, input);
            let side = store.fiat(zero, one);
            let proof = store.add(
                SlottedProposition::equal(input, hit),
                SlottedJustification::Rule {
                    name: "r".into(),
                    substitution: vec![("x".into(), zero), ("y".into(), one)],
                    premises: vec![root, side].into_iter().map(Into::into).collect(),
                },
            );
            let error = check_proof(&mut store, &program, proof).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("condition is in A, its premise in B"),
                "{error}"
            );
        }
    }

    #[test]
    fn global_root_rules_keep_their_source_sort() {
        for source in [
            r#"(rewrite fixed (WA fixed) :name "r")"#,
            r#"(rewrite fixed other :name "r")"#,
            r#"(rewrite fixed x :when ((= x (WA y))) :name "r")"#,
        ] {
            let mut dag = TermDag::default();
            let mut program = SlottedProgram::default();
            program.add_sorted_constructor("WA", "A", vec![ColumnKind::Child]);
            program.add_sorted_constructor("WB", "B", vec![ColumnKind::Child]);
            program.add_let(&mut dag, "fixed", "$0").unwrap();
            program.add_let(&mut dag, "other", "(WA $0)").unwrap();
            program.add_let(&mut dag, "b", "(WB $0)").unwrap();
            program.add_rewrite(&mut dag, source).unwrap();
            let (fixed, other, b) = (
                program.lets["fixed"],
                program.lets["other"],
                program.lets["b"],
            );
            let mut store = SlottedProofStore::new(dag);
            let root = store.fiat(fixed, fixed);
            let side = store.fiat(other, other);
            let premises = if program.rewrites["r"].conditions().is_empty() {
                vec![root]
            } else {
                vec![root, side]
            };
            let proof = store.add(
                SlottedProposition::equal(fixed, other),
                SlottedJustification::Rule {
                    name: "r".into(),
                    substitution: vec![("x".into(), other), ("y".into(), fixed)],
                    premises: premises.into_iter().map(Into::into).collect(),
                },
            );
            assert_eq!(
                check_proof(&mut store, &program, proof)
                    .unwrap()
                    .sort
                    .as_deref(),
                Some("A")
            );
            let parent = store.fiat(b, b);
            let crossed = store.congr(parent, 0, proof).unwrap();
            let error = check_proof(&mut store, &program, crossed).unwrap_err();
            assert!(
                error.to_string().contains("column 0 of WB is B")
                    || error.to_string().contains("expected B"),
                "{source}: {error}"
            );
        }
    }

    #[test]
    fn constructor_conditions_determine_a_slot_rules_carrier() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_sorted_constructor("WA", "A", vec![ColumnKind::Child]);
        program.add_sorted_constructor("WB", "B", vec![ColumnKind::Child]);
        program.add_let(&mut dag, "fixed", "$0").unwrap();
        program.add_let(&mut dag, "side", "(WA $0)").unwrap();
        program.add_let(&mut dag, "b", "(WB $0)").unwrap();
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite fixed $fresh :when ((WA x)) :name "r")"#,
            )
            .unwrap();
        let (fixed, side, b) = (
            program.lets["fixed"],
            program.lets["side"],
            program.lets["b"],
        );
        let fresh = slot_term(&mut dag, 2);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(fixed, fixed);
        let side = store.fiat(side, side);
        let proof = store.add(
            SlottedProposition::equal(fixed, fresh),
            SlottedJustification::Rule {
                name: "r".into(),
                substitution: vec![("x".into(), fixed), ("$fresh".into(), fresh)],
                premises: vec![root, side].into_iter().map(Into::into).collect(),
            },
        );
        assert_eq!(
            check_proof(&mut store, &program, proof)
                .unwrap()
                .sort
                .as_deref(),
            Some("A")
        );
        let parent = store.fiat(b, b);
        let crossed = store.congr(parent, 0, proof).unwrap();
        assert!(check_proof(&mut store, &program, crossed).is_err());
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
                premises: vec![root].into_iter().map(Into::into).collect(),
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
                premises: vec![root].into_iter().map(Into::into).collect(),
            },
        );
        let err = check_proof(&mut store, &program, non_slot).unwrap_err();
        assert!(err.to_string().contains("not a slot"), "{err}");
    }

    #[test]
    fn equalities_stay_in_their_sort() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_sorted_constructor("WA", "A", vec![ColumnKind::Child]);
        program.add_sorted_constructor("WB", "B", vec![ColumnKind::Child]);
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
                    premises: vec![root].into_iter().map(Into::into).collect(),
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
            program.add_sorted_constructor("PairA", "A", vec![ColumnKind::Child; 2]);
            program.add_sorted_constructor("WA", "A", vec![ColumnKind::Child]);
            program.add_sorted_constructor("WB", "B", vec![ColumnKind::Child]);
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
                    premises: vec![root, side].into_iter().map(Into::into).collect(),
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
        assert!(err.to_string().contains("matching middle terms"), "{err}");
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
        assert!(err.to_string().contains("child proof lhs"), "{err}");
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
                    step: "equality",
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
