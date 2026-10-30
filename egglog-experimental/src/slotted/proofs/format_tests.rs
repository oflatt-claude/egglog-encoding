use super::*;
use crate::slotted::proofs::terms::slot_term;

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
