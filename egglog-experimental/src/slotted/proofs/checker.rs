//! Checks surface proofs against the slotted source program.

use super::format::{Claim, ClaimKind, SlottedConclusion, SlottedProof, SlottedProofStore};
use super::guards::{GuardValidators, proof_body};
use super::source::{ColumnKind, SlottedProgram, SourceFact, pattern_term};
use super::terms::{all_slots, instantiate, rename, slot_of};
use super::{HashMap, HashSet};
use egglog::ast::{
    Literal, ResolvedExpr, ResolvedExprExt, ResolvedFact, ResolvedNCommand, ResolvedVar,
};
use egglog::proof::{Justification, Proof, ProofCheckContext, ProofId, ProofStore, Proposition};
use egglog::util::{FreshGen, INTERNAL_SYMBOL_PREFIX, SymbolGen};
use egglog::{Term, TermDag, TermId};
use egglog_numeric_id::NumericId;
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
    #[error(
        "proof #{proof}: rule {name:?} takes {expected} premises after guard normalization, {actual} given"
    )]
    PremiseCount {
        /// The rejected step.
        proof: ProofId,
        /// The applied rewrite.
        name: String,
        /// The number required after guard normalization.
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

// `None` marks RenamingEq evidence, checked against the enclosing rule condition.
type CheckedProofs = HashMap<ProofId, Option<Checked>>;

/// Check an equality proof and every proof it depends on, returning what it proves.
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
    let validators = GuardValidators::new(program);
    let result = (|| {
        let mut checked = HashMap::default();
        for id in store.dependencies(root) {
            let result = check_one(
                store,
                &mut ordinary,
                &context,
                &validators,
                program,
                id,
                &checked,
            )?;
            checked.insert(id, result);
        }
        checked
            .remove(&root)
            .flatten()
            .ok_or_else(|| SlottedCheckError::Step {
                proof: root,
                step: "root",
                detail: "renaming equality must be used by a rule, not as an ordinary equality"
                    .into(),
            })
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

#[allow(clippy::too_many_arguments)]
fn check_one(
    store: &SlottedProofStore,
    ordinary: &mut ProofStore,
    context: &ProofCheckContext,
    validators: &GuardValidators,
    program: &SlottedProgram,
    id: ProofId,
    checked: &CheckedProofs,
) -> Result<Option<Checked>, SlottedCheckError> {
    let proof = store.get(id);
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
    let equality = |p: &ProofId| {
        checked[p].as_ref().ok_or_else(|| {
            step(
                "premise",
                format!("renaming-equality proof #{p} is not an equality"),
            )
        })
    };
    if let SlottedProof::RenamingEq { left, right } = proof {
        for p in [left, right] {
            equality(p)?;
        }
        return Ok(None);
    }
    if !matches!(proof, SlottedProof::Ordinary(p) if matches!(p.justification(), Justification::Rule { .. }))
    {
        for p in proof.premises() {
            equality(&p)?;
        }
    }
    let premise = |p: &ProofId| checked[p].as_ref().expect("premise is an equality").clone();
    let claimed = proof.proposition().expect("equality step");
    if let SlottedProof::Ordinary(proof) = proof
        && matches!(proof.justification(), Justification::Fiat)
        && claimed.lhs == claimed.rhs
        && matches!(
            ordinary.term_dag().get(claimed.lhs),
            Term::Lit(Literal::Unit)
        )
    {
        // Ordinary primitive guards use Unit reflexivity as their result premise.
        let proposition = ordinary
            .check_step(id, proof, &[], context, |_, _| {
                unreachable!("Fiat has no premises")
            })
            .map_err(|e| step("literal", e.to_string()))?;
        return Ok(Some(Checked {
            proposition,
            sort: None,
        }));
    }
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
                Ok(checked[&p]
                    .as_ref()
                    .expect("premise is an equality")
                    .proposition
                    .clone())
            })
            .map_err(|e| step("equality", e.to_string()))?;
    }
    let dag = ordinary.term_dag_mut();
    let (derived, sort) = match proof {
        SlottedProof::RenamingEq { .. } => unreachable!("renaming equality handled above"),
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
                Justification::Rule { .. } => {
                    return check_rule(store, ordinary, validators, program, id, proof, checked)
                        .map(|(proposition, sort)| Some(Checked { proposition, sort }));
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
    Ok(Some(Checked {
        proposition: derived,
        sort,
    }))
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
    store: &SlottedProofStore,
    ordinary: &mut ProofStore,
    validators: &GuardValidators,
    program: &SlottedProgram,
    id: ProofId,
    proof: &Proof,
    checked: &CheckedProofs,
) -> Result<(Proposition, Option<String>), SlottedCheckError> {
    let Justification::Rule {
        name,
        substitution,
        premise_proofs,
    } = proof.justification()
    else {
        unreachable!("called for a Rule step")
    };
    let claimed = proof.proposition();
    let dag = ordinary.term_dag_mut();
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

    let (facts, auxiliary) = proof_body(rule, dag, &bindings).map_err(&fail)?;
    if premise_proofs.len() != facts.len() {
        return Err(SlottedCheckError::PremiseCount {
            proof: id,
            name: name.clone(),
            expected: facts.len(),
            actual: premise_proofs.len(),
        });
    }
    let mut substitution = substitution.clone();
    substitution.extend(rule.globals.clone());
    substitution.extend(auxiliary);
    let mut prefix = format!("{INTERNAL_SYMBOL_PREFIX}slotted-guard-");
    while substitution.keys().any(|name| name.starts_with(&prefix)) {
        prefix.push('-');
    }
    let mut symbols = SymbolGen::new(prefix);
    let mut body = Vec::new();
    let mut premises = Vec::new();
    let equality = |p: ProofId| {
        checked[&p]
            .as_ref()
            .ok_or_else(|| fail(format!("renaming-equality proof #{p} is not an equality")))
    };
    for (fact, &premise_id) in facts.iter().zip(premise_proofs) {
        if let ResolvedFact::Fact(ResolvedExpr::Call(
            span,
            egglog::ResolvedCall::Primitive(head),
            args,
        )) = fact
        {
            let (arguments, result) = if head.name() == "renaming-=" {
                let SlottedProof::RenamingEq { left, right } = store.get(premise_id) else {
                    return Err(fail("renaming-= requires a RenamingEq proof".into()));
                };
                let mut variables = Vec::new();
                for (arg, &p) in args.iter().zip([left, right]) {
                    let checked = equality(p)?;
                    let p = &checked.proposition;
                    check_term_sort(program, dag, p.rhs, Some(arg.output_type().name()))
                        .map_err(&fail)?;
                    join_sorts(
                        Some(arg.output_type().name().to_owned()),
                        checked.sort.clone(),
                    )
                    .map_err(|(a, b)| fail(format!("condition is in {a}, its premise in {b}")))?;
                    let variable = symbols.fresh("argument");
                    substitution.insert(variable.clone(), p.rhs);
                    let var = ResolvedExpr::Var(
                        arg.span(),
                        ResolvedVar {
                            name: variable,
                            sort: arg.output_type().clone(),
                            is_global_ref: false,
                        },
                    );
                    body.push(ResolvedFact::Eq(arg.span(), arg.clone(), var.clone()));
                    premises.push(p.clone());
                    variables.push(var);
                }
                let unit = dag.lit(Literal::Unit);
                (variables, Proposition::new(unit, unit))
            } else {
                (args.clone(), equality(premise_id)?.proposition.clone())
            };
            let head = validators.resolve(head.name(), args).map_err(&fail)?;
            body.push(ResolvedFact::Fact(ResolvedExpr::Call(
                span.clone(),
                head,
                arguments,
            )));
            premises.push(result);
        } else {
            let checked = equality(premise_id)?;
            let condition_sort = match fact {
                ResolvedFact::Eq(_, expr, _) | ResolvedFact::Fact(expr) => expr.output_type(),
            };
            join_sorts(Some(condition_sort.name().to_owned()), checked.sort.clone())
                .map_err(|(a, b)| fail(format!("condition is in {a}, its premise in {b}")))?;
            body.push(fact.clone());
            premises.push(checked.proposition.clone());
        }
    }
    let native_rule = egglog::ast::ResolvedRule {
        body,
        ..rule.rule.clone()
    };
    let commands = [ResolvedNCommand::NormRule { rule: native_rule }];
    let context = ProofCheckContext::new(&commands, dag).map_err(|e| fail(e.to_string()))?;
    let native_proof = Proof::new(
        claimed.clone(),
        Justification::Rule {
            name: name.clone(),
            substitution,
            premise_proofs: (0..premises.len()).map(ProofId::from_usize).collect(),
        },
    );
    let proven = ordinary
        .check_step(id, &native_proof, &commands, &context, |_, p| {
            Ok(premises[p.index()].clone())
        })
        .map_err(|e| fail(e.to_string()))?;
    let instance =
        (claimed.lhs, claimed.rhs) == (lhs, rhs) || (claimed.lhs, claimed.rhs) == (rhs, lhs);
    let sort = if instance {
        Some(sort)
    } else {
        program.sort_of(ordinary.term_dag(), claimed.lhs)
    };
    Ok((proven, sort))
}

#[cfg(test)]
#[path = "checker_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "checker_guard_tests.rs"]
mod guard_tests;
