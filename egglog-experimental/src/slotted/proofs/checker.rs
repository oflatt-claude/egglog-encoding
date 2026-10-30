//! Checks surface proofs against the slotted source program.

use super::format::{Claim, ClaimKind, SlottedConclusion, SlottedProof, SlottedProofStore};
use super::source::{ColumnKind, Requirement, SlottedProgram, SourceFact, pattern_term};
use super::terms::{all_slots, instantiate, rename, slot_of};
use super::{HashMap, HashSet};
use egglog::ast::{Literal, ResolvedExpr, ResolvedExprExt, ResolvedFact};
use egglog::proof::{
    Justification, ProofCheckContext, ProofId, ProofStore, Proposition,
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
        proof: ProofId,
        /// Its printed proposition.
        claim: String,
    },
    /// A rule application names an undeclared rewrite.
    #[error("proof #{proof}: no rewrite named {name:?}")]
    RuleNotFound {
        /// The rejected step.
        proof: ProofId,
        /// The requested rewrite.
        name: String,
    },
    /// A rule application supplies the wrong number of premises.
    #[error("proof #{proof}: rule {name:?} takes {expected} premises, {actual} given")]
    PremiseCount {
        /// The rejected step.
        proof: ProofId,
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
        proof: ProofId,
        /// The applied rewrite.
        name: String,
        /// The missing substitution key.
        variable: String,
    },
    /// A rule application does not match its source rewrite.
    #[error("proof #{proof}: rule {name:?}: {detail}")]
    Rule {
        /// The rejected step.
        proof: ProofId,
        /// The applied rewrite.
        name: String,
        /// The violated rule requirement.
        detail: String,
    },
    /// A proof-algebra step does not follow from its premises.
    #[error("proof #{proof}: {step}: {detail}")]
    Step {
        /// The rejected step.
        proof: ProofId,
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
/// the sort of their source axiom or rewrite. The checker derives the sort;
/// the proof does not supply it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Checked {
    /// The equality established by the derivation.
    pub proposition: Proposition,
    /// Its carrier sort, or `None` for a sort-independent equality.
    pub sort: Option<String>,
}

/// Check a proof and every proof it depends on, returning what it proves.
pub fn check_proof(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    root: ProofId,
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
            checked.insert(id, result);
        }
        Ok(checked[&root].clone())
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
            claim: store.proposition_to_string(&Proposition::new(claim.lhs, claim.rhs)),
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

fn proposition_string(dag: &TermDag, p: &Proposition) -> String {
    format!("{} = {}", dag.to_string(p.lhs), dag.to_string(p.rhs))
}

fn check_one(
    store: &SlottedProofStore,
    ordinary: &mut ProofStore,
    context: &ProofCheckContext,
    program: &SlottedProgram,
    id: ProofId,
    checked: &HashMap<ProofId, Checked>,
) -> Result<Checked, SlottedCheckError> {
    let proof = store.get(id);
    let claimed = proof.proposition();
    let step = |step: &'static str, detail: String| SlottedCheckError::Step {
        proof: id,
        step,
        detail,
    };
    for p in proof.premises() {
        if !checked.contains_key(&p) {
            return Err(step(
                "premise",
                format!("proof #{p} is used before it is established: the proof is cyclic"),
            ));
        }
    }
    let premise = |p: &ProofId| checked[p].clone();
    let dag = ordinary.term_dag_mut();
    for term in [claimed.lhs, claimed.rhs] {
        check_term_sort(program, dag, term, None).map_err(|e| step("sort", e))?;
    }
    if let SlottedProof::Ordinary(proof) = proof
        && matches!(
            proof.justification(),
            Justification::Sym(_)
                | Justification::Trans(..)
                | Justification::Congr { .. }
                | Justification::Proj { .. }
        )
    {
        ordinary
            .check_step(id, proof, &[], context, |_, p| {
                Ok(checked[&p].proposition.clone())
            })
            .map_err(|e| step("equality", e.to_string()))?;
    }
    let dag = ordinary.term_dag_mut();
    let (derived, sort) = match proof {
        SlottedProof::Alpha { proof, .. } => {
            let p = premise(proof);
            if !program.alpha_eq(dag, p.proposition.rhs, claimed.rhs) {
                return Err(step(
                    "alpha",
                    "right endpoints are not alpha-equivalent".into(),
                ));
            }
            (Proposition::new(p.proposition.lhs, claimed.rhs), p.sort)
        }
        SlottedProof::Equivariance {
            proof, renaming, ..
        } => {
            let p = premise(proof);
            let lhs = rename(dag, renaming, p.proposition.lhs);
            let rhs = rename(dag, renaming, p.proposition.rhs);
            (Proposition::new(lhs, rhs), p.sort)
        }
        SlottedProof::Ordinary(proof) => {
            let sort = match proof.justification() {
                Justification::Fiat => {
                    let reflexive =
                        claimed.lhs == claimed.rhs && program.is_built(dag, claimed.lhs);
                    let union = program.union_sort(claimed.lhs, claimed.rhs);
                    if !(reflexive || union.is_some()) {
                        return Err(SlottedCheckError::InvalidFiat {
                            proof: id,
                            claim: proposition_string(dag, claimed),
                        });
                    }
                    union
                        .map(str::to_owned)
                        .or_else(|| program.sort_of(dag, claimed.lhs))
                }
                Justification::Rule {
                    name,
                    substitution,
                    premise_proofs,
                } => {
                    let premises = premise_proofs.iter().map(premise).collect::<Vec<_>>();
                    return check_rule(dag, program, id, name, substitution, &premises, claimed)
                        .map(|(proposition, sort)| Checked { proposition, sort });
                }
                Justification::Sym(inner) => premise(inner).sort,
                Justification::Trans(left, right) => {
                    join_sorts(premise(left).sort, premise(right).sort).map_err(|(a, b)| {
                        step("trans", format!("joins a proof in {a} with one in {b}"))
                    })?
                }
                Justification::Congr {
                    proof,
                    child_index,
                    child_proof,
                } => {
                    let (p, c) = (premise(proof), premise(child_proof));
                    let Term::App(head, _) = dag.get(p.proposition.rhs) else {
                        unreachable!("ordinary congruence validated the parent")
                    };
                    let ctor = &program.constructors[head];
                    let column_sort = ctor
                        .column_sort(*child_index)
                        .expect("ordinary congruence validated the column");
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
                    p.sort.or(Some(ctor.sort.clone()))
                }
                Justification::Proj { proof, child_index } => {
                    let p = premise(proof);
                    let Term::App(head, _) = dag.get(p.proposition.rhs) else {
                        unreachable!("ordinary projection validated the parent")
                    };
                    program
                        .constructors
                        .get(head)
                        .and_then(|c| c.column_sort(*child_index))
                        .map(str::to_owned)
                }
                Justification::MergeFn { .. }
                | Justification::ContainerNormalize { .. }
                | Justification::Eval => {
                    return Err(step(
                        "source",
                        "this step is not supported by the slotted source language".into(),
                    ));
                }
            };
            (claimed.clone(), sort)
        }
    };
    if &derived != claimed {
        return Err(step(
            "conclusion",
            format!(
                "states {} but derives {}",
                proposition_string(ordinary.term_dag(), claimed),
                proposition_string(ordinary.term_dag(), &derived)
            ),
        ));
    }
    Ok(Checked {
        proposition: derived,
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
    id: ProofId,
    name: &str,
    substitution: &egglog::util::IndexMap<String, TermId>,
    premises: &[Checked],
    claimed: &Proposition,
) -> Result<(Proposition, Option<String>), SlottedCheckError> {
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
    if let Some(name) = substitution
        .keys()
        .find(|name| rule.globals.contains_key(*name))
    {
        return Err(fail(format!(
            "substitution overrides captured global {name}"
        )));
    }
    let bindings: HashMap<_, _> = substitution
        .iter()
        .chain(rule.globals.iter())
        .map(|(name, &term)| (name.clone(), term))
        .collect();
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
        let term = *substitution
            .get(literal)
            .ok_or_else(|| unbound(literal.clone()))?;
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

    let lhs = instantiate(dag, lhs_pattern, &bindings).map_err(unbound)?;
    let root = &premises[0].proposition;
    check_fact_matches_proposition(dag, &rule.rule.body[0], root, &bindings, name)
        .map_err(|e| fail(format!("root premise: {e}")))?;
    join_sorts(Some(sort.clone()), premises[0].sort.clone())
        .map_err(|(a, b)| fail(format!("the rewrite is in {a}, its root premise in {b}")))?;
    for (requirement, premise) in requirements.iter().zip(&premises[1..]) {
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
                let left = instantiate(dag, left, &bindings).map_err(unbound)?;
                let right = instantiate(dag, right, &bindings).map_err(unbound)?;
                if got.lhs != left || !program.eq_modulo_renaming(dag, got.rhs, right) {
                    return Err(fail(
                        "premise does not establish the original renaming-= guard".into(),
                    ));
                }
                (None, a.output_type().name().to_owned())
            }
        };
        if let Some(fact) = fact {
            check_fact_matches_proposition(dag, &fact, got, &bindings, name)
                .map_err(|e| fail(format!("original :when fact: {e}")))?;
        }
        join_sorts(Some(condition_sort), premise.sort.clone())
            .map_err(|(a, b)| fail(format!("condition is in {a}, its premise in {b}")))?;
    }

    let instance = |dag: &mut TermDag, expr: &ResolvedExpr| {
        let pattern = pattern_term(dag, expr);
        instantiate(dag, pattern, &bindings).map_err(unbound)
    };
    for condition in rule.conditions() {
        let ResolvedFact::Fact(ResolvedExpr::Call(_, egglog::ResolvedCall::Primitive(head), args)) =
            condition
        else {
            continue;
        };
        let head = head.name();
        match (head, args.as_slice()) {
            // Equality evidence was checked with the other premises above.
            ("renaming-=", [_, _]) => {}
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
            _ => return Err(fail(format!("unsupported source guard {head}"))),
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
    let rhs = instantiate(dag, rhs_pattern, &bindings).map_err(unbound)?;
    for var in rule.pattern_vars(dag, rhs_pattern) {
        if body_vars.contains(&var) {
            continue;
        }
        if !var.starts_with('$') {
            return Err(fail(format!("{var} occurs only on the right-hand side")));
        }
        let minted = *substitution.get(&var).ok_or_else(|| unbound(var.clone()))?;
        let slot = slot_of(dag, minted)
            .ok_or_else(|| fail(format!("minted {var} is bound to a non-slot")))?;
        let used: BTreeSet<i64> = substitution
            .iter()
            .filter(|(name, _)| name.as_str() != var)
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
    check_actions_produce_equality(dag, &rule.rule.head, substitution, &bindings, claimed, name)
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
#[path = "checker_tests.rs"]
mod tests;
