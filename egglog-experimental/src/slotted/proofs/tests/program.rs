use crate::slotted::proofs::terms::{Renaming, slot_term};
use crate::slotted::proofs::{RulePremise, SlottedProofStore, check_proof};
use egglog::TermDag;
use egglog::ast::{Literal, parse_sexps};
use egglog::proof::Proposition;
use std::collections::BTreeMap;

fn program(text: &str) -> Vec<egglog::ast::Sexp> {
    parse_sexps(None, text).unwrap()
}

#[test]
fn source_alone_supplies_axioms_and_binders() {
    let source = program(
        "(datatype E (V Var) (Lam Var E :binder 0) (Zero)) (let id (Lam $0 (V $0))) (union id (Zero))",
    );
    let mut dag = TermDag::default();
    let s0 = slot_term(&mut dag, 0);
    let s1 = slot_term(&mut dag, 1);
    let v0 = dag.app("V".into(), vec![s0]);
    let v1 = dag.app("V".into(), vec![s1]);
    let l0 = dag.app("Lam".into(), vec![s0, v0]);
    let l1 = dag.app("Lam".into(), vec![s1, v1]);
    let zero = dag.app("Zero".into(), vec![]);
    let mut store = SlottedProofStore::new(dag);
    let fiat = store.fiat(zero, l0);
    let proof = store.alpha(fiat, l1);
    check_proof(&mut store, &source, proof).unwrap();
    let without_union =
        program("(datatype E (V Var) (Lam Var E :binder 0) (Zero)) (let id (Lam $0 (V $0)))");
    assert!(check_proof(&mut store, &without_union, proof).is_err());
    let without_binder = program(
        "(datatype E (V Var) (Lam Var E) (Zero)) (let id (Lam $0 (V $0))) (union id (Zero))",
    );
    assert!(check_proof(&mut store, &without_binder, proof).is_err());
}

#[test]
fn named_slots_are_injective_even_with_incomplete_proof_names() {
    let source = program("(datatype E (V Var)) (let a (V $a)) (let b (V $b))");
    let mut dag = TermDag::default();
    let s0 = slot_term(&mut dag, 0);
    let s1 = slot_term(&mut dag, 1);
    let a = dag.app("V".into(), vec![s0]);
    let b = dag.app("V".into(), vec![s1]);
    let mut store = SlottedProofStore::new(dag)
        .with_slot_names(&BTreeMap::from([("$a".into(), 0), ("$b".into(), 1)]));
    let reflexivity = store.fiat(a, a);
    check_proof(&mut store, &source, reflexivity).unwrap();
    let forged = store.fiat(a, b);
    assert!(check_proof(&mut store, &source, forged).is_err());
    let mut ambiguous = store
        .clone()
        .with_slot_names(&BTreeMap::from([("$0".into(), 0), ("$+0".into(), 1)]));
    assert!(check_proof(&mut ambiguous, &source, reflexivity).is_err());
    let mut incomplete = store.with_slot_names(&BTreeMap::from([("$a".into(), 0)]));
    assert!(check_proof(&mut incomplete, &source, forged).is_err());
}

#[test]
fn scopes_and_original_when_are_checked_without_the_compiler() {
    let prefix = "(datatype E (N i64)) (let n (N 1)) (push) (rewrite (N x) (N 2) :when ((!= x 0)))";
    let mut dag = TermDag::default();
    let one = dag.lit(Literal::Int(1));
    let two = dag.lit(Literal::Int(2));
    let unit = dag.lit(Literal::Unit);
    let n1 = dag.app("N".into(), vec![one]);
    let n2 = dag.app("N".into(), vec![two]);
    let mut store = SlottedProofStore::new(dag);
    let built = store.fiat(n1, n1);
    let guard = store.fiat(unit, unit);
    let proof = store.rule(
        Proposition::new(n1, n2),
        "_slotted_match_0".into(),
        [("x".into(), one)].into_iter().collect(),
        vec![RulePremise::Equality(built), RulePremise::Equality(guard)],
    );
    check_proof(&mut store, &program(prefix), proof).unwrap();
    assert!(
        check_proof(
            &mut store,
            &program(&prefix.replace("(!= x 0)", "(!= x 1)")),
            proof
        )
        .is_err()
    );
    assert!(check_proof(&mut store, &program(&format!("{prefix} (pop)")), proof).is_err());
    let named = prefix.replace("(N 2) :when", "(N 2) :name other :when");
    assert!(check_proof(&mut store, &program(&named), proof).is_err());
}

#[test]
fn source_unions_cannot_equate_rigid_names() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 0);
    let b = slot_term(&mut dag, 1);
    let mut store = SlottedProofStore::new(dag);
    let proof = store.fiat(a, b);
    assert!(check_proof(&mut store, &program("(union $0 $1)"), proof).is_err());
    let renamed = store.equivariance(proof, Renaming::new([(0, 1), (1, 0)]).unwrap());
    assert!(check_proof(&mut store, &program("(union $0 $1)"), renamed).is_err());
}

#[test]
fn disequality_validator_respects_alpha_equivalence() {
    for distinct in [false, true] {
        let slot = if distinct { 2 } else { 1 };
        let source = program(&format!(
            "(datatype E (V Var) (Lam Var E :binder 0) (Pair E E) (Hit)) (let pair (Pair (Lam $0 (V $0)) (Lam $1 (V ${slot})))) (rewrite (Pair x y) (Hit) :when ((!= x y)) :name r)"
        ));
        let mut dag = TermDag::default();
        let zero = slot_term(&mut dag, 0);
        let one = slot_term(&mut dag, 1);
        let name = slot_term(&mut dag, slot);
        let a = dag.app("V".into(), vec![zero]);
        let b = dag.app("V".into(), vec![name]);
        let a = dag.app("Lam".into(), vec![zero, a]);
        let b = dag.app("Lam".into(), vec![one, b]);
        let pair = dag.app("Pair".into(), vec![a, b]);
        let hit = dag.app("Hit".into(), vec![]);
        let unit = dag.lit(Literal::Unit);
        let mut store = SlottedProofStore::new(dag);
        let built = store.fiat(pair, pair);
        let guard = store.fiat(unit, unit);
        let proof = store.rule(
            Proposition::new(pair, hit),
            "r".into(),
            [("x".into(), a), ("y".into(), b)].into_iter().collect(),
            vec![RulePremise::Equality(built), RulePremise::Equality(guard)],
        );
        assert_eq!(check_proof(&mut store, &source, proof).is_ok(), distinct);
    }
}
