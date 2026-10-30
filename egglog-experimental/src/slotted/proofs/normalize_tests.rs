use super::*;
use crate::slotted::proofs::checker::check_proof;
use crate::slotted::proofs::source::{ColumnKind, SlottedProgram};
use egglog::TermDag;

#[test]
fn transports_binder_children_and_preserves_source_axioms() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_constructor("G", vec![ColumnKind::Child]);
    program.add_constructor("Wrap", vec![ColumnKind::Child]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    for (name, term) in [
        ("f", "(F $0)"),
        ("g", "(G $0)"),
        ("lam", "(Lam $0 (F $0))"),
        ("wrap", "(Wrap (Lam $0 (F $0)))"),
    ] {
        program.add_let(&mut dag, name, term).unwrap();
    }
    program.add_union(&mut dag, "f", "g", "U").unwrap();
    let mut store = SlottedProofStore::new(dag);
    let union = store.fiat(program.lets["f"], program.lets["g"]);
    let lam = store.fiat(program.lets["lam"], program.lets["lam"]);
    let lam = store.congr(lam, 1, union).unwrap();
    let wrap = store.fiat(program.lets["wrap"], program.lets["wrap"]);
    let wrap = store.congr(wrap, 0, lam).unwrap();
    let root = store.equivariance(wrap, Renaming::new([(0, 1), (1, 2), (2, 0)]).unwrap());
    let expected = check_proof(&mut store, &program, root).unwrap();
    let normalized = store.simplify(root);
    assert_eq!(
        check_proof(&mut store, &program, normalized).unwrap(),
        expected
    );
    assert_eq!(
        store.term_dag.to_string(expected.proposition.rhs),
        "(Wrap (Lam $1 (G $1)))"
    );
    for id in store.dependencies(normalized) {
        if let SlottedProof::Equivariance { proof, .. } = store.get(id) {
            assert!(
                matches!(store.get(*proof), SlottedProof::Ordinary(p) if matches!(p.justification(), Step::Fiat | Step::Rule { .. }))
            );
        }
    }
    let again = store.simplify(normalized);
    assert_eq!(store.proposition(again), &expected.proposition);
}

#[test]
fn inverse_transports_cancel_without_trusting_new_fiats() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_let(&mut dag, "f", "(F $0)").unwrap();
    let mut store = SlottedProofStore::new(dag);
    let source = store.fiat(program.lets["f"], program.lets["f"]);
    let rho = Renaming::new([(0, 1), (1, 2), (2, 0)]).unwrap();
    let first = store.equivariance(source, rho.clone());
    let second = store.equivariance(first, rho.inverse());
    let normalized = store.simplify(second);
    assert_eq!(normalized, source);
    check_proof(&mut store, &program, normalized).unwrap();
    let transported = store.simplify(first);
    let p = store.proposition(transported).clone();
    let forged = store.fiat(p.lhs, p.rhs);
    assert!(check_proof(&mut store, &program, forged).is_err());
    check_proof(&mut store, &program, transported).unwrap();
}
