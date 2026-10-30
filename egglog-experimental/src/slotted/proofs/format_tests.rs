use super::*;
use crate::slotted::proofs::terms::slot_term;

#[test]
fn shared_renaming_equality_prints_as_a_proof() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 0);
    let b = slot_term(&mut dag, 1);
    let mut store = SlottedProofStore::new(dag);
    let left = store.fiat(a, a);
    let right = store.fiat(b, b);
    let guard = store.renaming_eq(left, right);
    let proof = store.ordinary(
        Proposition::new(a, b),
        Justification::Rule {
            name: "r".into(),
            substitution: Default::default(),
            premise_proofs: vec![guard, guard],
        },
    );
    let text = store.proof_to_string(proof);
    assert!(text.contains("(let prf0 (RenamingEq"), "{text}");
    assert!(text.contains("(premises prf0 prf0)"), "{text}");
}

#[test]
fn fresh_display_names_cover_permutation_only_coordinates() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 10);
    dag.var("v1".into());
    let mut store = SlottedProofStore::new(dag)
        .with_slot_names(&BTreeMap::from([("$a".into(), 10), ("$v0".into(), 20)]));
    let refl = store.fiat(a, a);
    let proof = store.equivariance(refl, Renaming::new([(30, 31), (31, 30)]).unwrap());
    assert_eq!(
        store.proof_to_string(proof),
        "(Equivariance (= $a $a) (Fiat (= $a $a)) (renaming ($v2 $v3) ($v3 $v2)))"
    );
}

#[test]
fn malformed_steps_preserve_the_store_and_report_the_conflict() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 0);
    let b = slot_term(&mut dag, 1);
    let fa = dag.app("F".into(), vec![a]);
    let mut store = SlottedProofStore::new(dag);
    let a_refl = store.fiat(a, a);
    let b_refl = store.fiat(b, b);
    let f_refl = store.fiat(fa, fa);
    let before = store.len();

    assert_eq!(
        store.trans(a_refl, b_refl),
        Err(MalformedStep::MiddleTermMismatch {
            left: "$0".into(),
            right: "$1".into(),
        })
    );
    assert_eq!(
        store.congr(f_refl, 0, b_refl),
        Err(MalformedStep::ChildMismatch {
            child: "$0".into(),
            premise_lhs: "$1".into(),
        })
    );
    for result in [store.congr(a_refl, 0, a_refl), store.project(a_refl, 0)] {
        assert_eq!(
            result,
            Err(MalformedStep::ExpectedApplication { term: "$0".into() })
        );
    }
    for result in [store.congr(f_refl, 1, a_refl), store.project(f_refl, 1)] {
        assert_eq!(
            result,
            Err(MalformedStep::ChildIndexOutOfBounds { index: 1, arity: 1 })
        );
    }
    assert_eq!(store.len(), before);
}
