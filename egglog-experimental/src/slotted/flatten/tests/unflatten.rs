use super::*;
use crate::slotted::proofs::checker::check_proof_in_program as check_proof;
use crate::slotted::proofs::context::ColumnKind;
use egglog::TermDag;

#[test]
fn congruence_restores_binders_in_independent_scopes() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("Start", vec![]);
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_constructor("Box", vec![ColumnKind::Child]);
    program.add_let(&mut dag, "input", "(Box (Start))").unwrap();
    program
        .add_rewrite(
            &mut dag,
            "(rewrite (Start) (Pair (Lam $x (V $x)) (Lam $x (V $x))) :name duplicate)",
        )
        .unwrap();
    program
        .add_let(&mut dag, "target", "(Pair (Lam $0 (V $0)) (Lam $0 (V $0)))")
        .unwrap();
    let target = program.lets.shift_remove("target").unwrap();
    let start = dag.app("Start".into(), vec![]);
    let slot = crate::slotted::proofs::terms::slot_term(&mut dag, 0);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(program.lets["input"], program.lets["input"]);
    let exists = store.project(root, 0).unwrap();
    let rewrite = store.rule(
        Proposition::new(start, target),
        "duplicate".into(),
        [("$x".into(), slot)].into_iter().collect(),
        vec![RulePremise::Equality(exists)],
    );
    let proof = store.congr(root, 0, rewrite).unwrap();
    check_proof(&mut store, &program, proof).unwrap();
    let expected = store.proposition(proof).clone();
    let (mut store, proof) = lift(store, &program, proof).unwrap();
    check_proof(&mut store, &program, proof).unwrap();
    assert_eq!(store.proposition(proof), &expected);
}

#[test]
fn reconstructs_nested_binders_after_a_shape_change() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    for head in ["F", "G"] {
        program.add_constructor(head, vec![ColumnKind::Child]);
    }
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program
        .add_let(&mut dag, "input", "(F (G (Lam $0 (V $0))))")
        .unwrap();
    program
        .add_let(&mut dag, "target", "(F (Lam $3 (Lam $4 (V $4))))")
        .unwrap();
    program
        .add_union(&mut dag, "(G (Lam $1 (V $1)))", "(Lam $2 (Lam $1 (V $1)))")
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
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program
        .add_let(&mut dag, "input", "(Pair (V $0) (V $0))")
        .unwrap();
    program
        .add_let(&mut dag, "target", "(Pair (V $1) (V $2))")
        .unwrap();
    let target = program.lets.shift_remove("target").unwrap();
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(program.lets["input"], program.lets["input"]);
    let mut witnesses = Witnesses::new(&mut store, &program, vec![root]);
    assert!(witnesses.exists(target).is_err());
}

#[test]
fn reconstruction_tries_equal_children_before_renaming_them() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    for head in ["F", "G", "H"] {
        program.add_constructor(head, vec![ColumnKind::Child]);
    }
    program
        .add_let(&mut dag, "input", "(Pair (V $0) (G (V $0)))")
        .unwrap();
    program
        .add_let(&mut dag, "target", "(Pair (V $0) (F (V $0)))")
        .unwrap();
    for (lhs, rhs) in [
        ("(G (V $0))", "(H (V $1))"),
        ("(G (V $0))", "(H (V $0))"),
        ("(H (V $0))", "(F (V $0))"),
    ] {
        program.add_union(&mut dag, lhs, rhs).unwrap();
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
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    for head in ["F", "G", "H"] {
        program.add_constructor(head, vec![ColumnKind::Child]);
    }
    program.add_let(&mut dag, "a", "(F (G (V $0)))").unwrap();
    program.add_let(&mut dag, "b", "(F (H (V $0)))").unwrap();
    program.add_let(&mut dag, "input", "(Pair a b)").unwrap();
    program
        .add_union(&mut dag, "(G (V $0))", "(H (V $0))")
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
