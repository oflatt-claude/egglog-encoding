//! Checks a slotted proof against the slotted source program, by the rules of
//! `slotted/PROOFS.md`. The checker reads only the program: it knows nothing of
//! the encoding the proof was translated from.

use super::format::{SlottedJustification, SlottedProofId, SlottedProofStore, SlottedProposition};
use super::source::{Claim, ClaimKind, Condition, Rhs, SlottedProgram};
use super::terms::{all_slots, instantiate, is_subterm, pattern_vars, rename, slot_of};
use crate::util::{HashMap, HashSet};
use crate::{Term, TermId};
use std::collections::BTreeSet;
use thiserror::Error;

#[derive(Debug, Clone, Error)]
pub enum SlottedCheckError {
    #[error(
        "proof #{proof}: fiat {claim} is neither a built term's reflexivity nor a source union"
    )]
    InvalidFiat {
        proof: SlottedProofId,
        claim: String,
    },
    #[error("proof #{proof}: no rewrite named {name:?}")]
    RuleNotFound { proof: SlottedProofId, name: String },
    #[error("proof #{proof}: rule {name:?} takes {expected} premises, {actual} given")]
    PremiseCount {
        proof: SlottedProofId,
        name: String,
        expected: usize,
        actual: usize,
    },
    #[error("proof #{proof}: rule {name:?} leaves {variable} unbound")]
    Unbound {
        proof: SlottedProofId,
        name: String,
        variable: String,
    },
    #[error("proof #{proof}: rule {name:?}: {detail}")]
    Rule {
        proof: SlottedProofId,
        name: String,
        detail: String,
    },
    #[error("proof #{proof}: {step}: {detail}")]
    Step {
        proof: SlottedProofId,
        step: &'static str,
        detail: String,
    },
    #[error(
        "claim {index} ({kind}) is not what the proof shows: it proves {proven}, the claim is {claim}"
    )]
    Claim {
        index: i64,
        kind: String,
        proven: String,
        claim: String,
    },
}

/// Check a proof and every proof it depends on, returning what it proves.
pub fn check_proof(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    root: SlottedProofId,
) -> Result<SlottedProposition, SlottedCheckError> {
    let mut checked: HashMap<SlottedProofId, SlottedProposition> = HashMap::default();
    for id in store.dependencies(root) {
        let proposition = check_one(store, program, id, &checked)?;
        checked.insert(id, proposition);
    }
    Ok(checked[&root].clone())
}

/// Check that a proof establishes a claim.
pub fn check_claim(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    claim: &Claim,
    proof: SlottedProofId,
) -> Result<(), SlottedCheckError> {
    let proven = check_proof(store, program, proof)?;
    let proven = store.normalize(proven);
    let lhs = program.refresh_binders(&mut store.term_dag, claim.lhs);
    let rhs = program.refresh_binders(&mut store.term_dag, claim.rhs);
    let holds = proven.lhs == lhs
        && proven.rhs == rhs
        && match claim.kind {
            ClaimKind::RenamingEq => true,
            ClaimKind::Eq => {
                let free_rhs = program.free_slots(&store.term_dag, rhs);
                let free_lhs = program.free_slots(&store.term_dag, lhs);
                !proven.renaming.moves_any(&free_rhs) || !proven.renaming.moves_any(&free_lhs)
            }
        };
    if holds {
        Ok(())
    } else {
        Err(SlottedCheckError::Claim {
            index: claim.index,
            kind: match claim.kind {
                ClaimKind::Eq => "=".into(),
                ClaimKind::RenamingEq => "renaming-=".into(),
            },
            proven: store.proposition_to_string(&proven),
            claim: store.proposition_to_string(&SlottedProposition::equal(claim.lhs, claim.rhs)),
        })
    }
}

fn check_one(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    id: SlottedProofId,
    checked: &HashMap<SlottedProofId, SlottedProposition>,
) -> Result<SlottedProposition, SlottedCheckError> {
    let proof = store.get(id).clone();
    // the stored proposition carries its whole permutation, which the derived
    // steps compose; what it claims is its restriction to the right-hand side
    let stored = proof.proposition.clone();
    let claimed = store.normalize(stored.clone());
    let step = |step: &'static str, detail: String| SlottedCheckError::Step {
        proof: id,
        step,
        detail,
    };
    let derived = match &proof.justification {
        SlottedJustification::Fiat => {
            let dag = &store.term_dag;
            let reflexive = claimed.lhs == claimed.rhs
                && claimed.renaming.is_identity()
                && program.is_built(dag, claimed.lhs);
            let union =
                claimed.renaming.is_identity() && program.is_union(claimed.lhs, claimed.rhs);
            if !(reflexive || union) {
                return Err(SlottedCheckError::InvalidFiat {
                    proof: id,
                    claim: store.proposition_to_string(&claimed),
                });
            }
            claimed.clone()
        }
        SlottedJustification::Rule {
            name,
            substitution,
            premises,
        } => check_rule(
            store,
            program,
            id,
            name,
            substitution,
            premises,
            checked,
            &claimed,
        )?,
        SlottedJustification::Sym(inner) => {
            let p = &checked[inner];
            SlottedProposition::new(p.rhs, p.renaming.inverse(), p.lhs)
        }
        SlottedJustification::Trans(left, right) => {
            let (l, r) = (&checked[left], &checked[right]);
            if l.rhs != r.lhs {
                return Err(step(
                    "trans",
                    format!(
                        "middle terms differ: {} vs {}",
                        store.term_dag.to_string(l.rhs),
                        store.term_dag.to_string(r.lhs)
                    ),
                ));
            }
            SlottedProposition::new(l.lhs, l.renaming.compose(&r.renaming), r.rhs)
        }
        SlottedJustification::Congr {
            proof: inner,
            child_index,
            child_proof,
        } => {
            let (p, c) = (checked[inner].clone(), checked[child_proof].clone());
            let Term::App(head, mut children) = store.term_dag.get(p.rhs).clone() else {
                return Err(step(
                    "congr",
                    "right-hand side is not an application".into(),
                ));
            };
            let Some(&child) = children.get(*child_index) else {
                return Err(step("congr", format!("no child at {child_index}")));
            };
            if child != c.lhs {
                return Err(step(
                    "congr",
                    format!(
                        "child {} is not the child proof's left side {}",
                        store.term_dag.to_string(child),
                        store.term_dag.to_string(c.lhs)
                    ),
                ));
            }
            children[*child_index] = rename(&mut store.term_dag, &c.renaming, c.rhs);
            let rhs = store.term_dag.app(head, children);
            SlottedProposition::new(p.lhs, p.renaming, rhs)
        }
        SlottedJustification::Shift {
            proof: inner,
            renaming,
        } => {
            let p = checked[inner].clone();
            let rhs = rename(&mut store.term_dag, renaming, p.rhs);
            SlottedProposition::new(p.lhs, p.renaming.compose(&renaming.inverse()), rhs)
        }
    };
    let derived = store.normalize(derived);
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
    Ok(stored)
}

#[allow(clippy::too_many_arguments)]
fn check_rule(
    store: &mut SlottedProofStore,
    program: &SlottedProgram,
    id: SlottedProofId,
    name: &str,
    substitution: &[(String, TermId)],
    premises: &[SlottedProofId],
    checked: &HashMap<SlottedProofId, SlottedProposition>,
    claimed: &SlottedProposition,
) -> Result<SlottedProposition, SlottedCheckError> {
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

    let lhs = instantiate(&mut store.term_dag, rule.lhs, &subst).map_err(unbound)?;
    let lhs = program.refresh_binders(&mut store.term_dag, lhs);
    let root = store.normalize(checked[&premises[0]].clone());
    if root.rhs != lhs {
        return Err(fail(format!(
            "the root premise proves {}, which does not end in the matched {}",
            store.proposition_to_string(&root),
            store.term_dag.to_string(lhs)
        )));
    }
    for ((var, call), premise) in equalities.iter().zip(&premises[1..]) {
        let want_lhs = *subst.get(*var).ok_or_else(|| unbound((*var).clone()))?;
        let want_rhs = instantiate(&mut store.term_dag, *call, &subst).map_err(unbound)?;
        let want_rhs = program.refresh_binders(&mut store.term_dag, want_rhs);
        let got = store.normalize(checked[premise].clone());
        // the same invocation: the renaming leaves one side's free slots alone,
        // which fixes the other side's by renaming both sides back
        let free_rhs = program.free_slots(&store.term_dag, want_rhs);
        let free_lhs = program.free_slots(&store.term_dag, want_lhs);
        let same = !got.renaming.moves_any(&free_rhs) || !got.renaming.moves_any(&free_lhs);
        if got.lhs != want_lhs || got.rhs != want_rhs || !same {
            return Err(fail(format!(
                "the premise for (= {var} ...) proves {}, not {} = {}",
                store.proposition_to_string(&got),
                store.term_dag.to_string(want_lhs),
                store.term_dag.to_string(want_rhs)
            )));
        }
    }

    for condition in &rule.conditions {
        match condition {
            Condition::Free { slot, var } | Condition::NotFree { slot, var } => {
                let slot_term = *subst.get(slot).ok_or_else(|| unbound(slot.clone()))?;
                let slot_number = slot_of(&store.term_dag, slot_term)
                    .ok_or_else(|| fail(format!("{slot} is bound to a non-slot")))?;
                let term = *subst.get(var).ok_or_else(|| unbound(var.clone()))?;
                let free = program.free_slots(&store.term_dag, term);
                let is_free = free.contains(&slot_number);
                let want_free = matches!(condition, Condition::Free { .. });
                if is_free != want_free {
                    return Err(fail(format!(
                        "({} {slot} {var}) fails: {slot} is ${slot_number}, {var} is {} with free slots {free:?}",
                        if want_free { "free" } else { "not-free" },
                        store.term_dag.to_string(term)
                    )));
                }
            }
            Condition::Neq { lhs, rhs } => {
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
    // bound to slots that occur in no other binding.
    let mut body_vars: HashSet<String> = pattern_vars(&store.term_dag, rule.lhs)
        .into_iter()
        .collect();
    for (_, call) in &equalities {
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
    let identity = claimed.renaming.is_identity();
    let instance = identity
        && ((claimed.lhs, claimed.rhs) == (lhs, rhs) || (claimed.lhs, claimed.rhs) == (rhs, lhs));
    let reflexive = identity
        && claimed.lhs == claimed.rhs
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
    Ok(claimed.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TermDag;
    use crate::proofs::slotted::source::ColumnKind;
    use crate::proofs::slotted::terms::{Renaming, slot_term};

    fn figure_3() -> (SlottedProofStore, SlottedProgram) {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Mul", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor("Null", vec![]);
        program.add_let(&mut dag, "m7", "(Mul $7 (Null))").unwrap();
        program.add_let(&mut dag, "zero", "(Null)").unwrap();
        program.add_union(&mut dag, "m7", "zero").unwrap();
        program
            .add_claim(&mut dag, 0, "=", "(Mul $9 (Null))", "zero")
            .unwrap();
        (SlottedProofStore::new(dag), program)
    }

    #[test]
    fn redundancy_by_sym_and_shift() {
        let (mut store, program) = figure_3();
        let (m7, zero) = (program.lets["m7"], program.lets["zero"]);
        let union = store.fiat(m7, zero);
        let back = store.sym(union);
        let shifted = store.shift(back, Renaming::new([(7, 9), (9, 7)]).unwrap());
        let proof = store.sym(shifted);
        let proven = check_proof(&mut store, &program, proof).unwrap();
        // the renaming is normalized away: `(Null)` has no slot for it to act on
        assert_eq!(
            store.proposition_to_string(&proven),
            "(Mul $9 (Null)) = (Null)"
        );
        check_claim(&mut store, &program, &program.claims[0], proof).unwrap();
        let text = store.proof_to_string(proof);
        assert!(text.contains("by shift #1 by {7->9, 9->7}"), "{text}");
    }

    #[test]
    fn a_non_injective_shift_cannot_be_stated() {
        assert!(Renaming::new([(0, 1)]).is_none());
    }

    #[test]
    fn fiat_needs_a_built_term_or_a_union() {
        let (mut store, program) = figure_3();
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
        let one = store.term_dag.lit(crate::ast::Literal::Int(1));
        let two = store.term_dag.lit(crate::ast::Literal::Int(2));
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
}
