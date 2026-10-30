use super::{SlottedCheckError, check_claim, check_proof};
use crate::slotted::proofs::format::{
    Claim, ClaimKind, ProofId, SlottedConclusion, SlottedProof, SlottedProofStore,
};
use crate::slotted::proofs::source::{ColumnKind, SlottedProgram};
use crate::slotted::proofs::terms::{Renaming, slot_term};
use egglog::proof::{Justification, Proposition};
use egglog::{Term, TermDag, TermId};
use egglog_numeric_id::NumericId;

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
    let forged = store.add(SlottedProof::Equivariance {
        proposition: Proposition::new(term, zero),
        proof: union,
        renaming: sigma,
    });
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
            let changed_left = store.add(SlottedProof::Alpha {
                proposition: Proposition::new(rhs, rhs),
                proof: premise,
            });
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
        let proof = store.ordinary(
            Proposition::new(input, rhs),
            Justification::Rule {
                name: "r".into(),
                substitution: substitution.into_iter().collect(),
                premise_proofs: vec![root],
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
        let rule = store.ordinary(
            Proposition::new(root, k),
            Justification::Rule {
                name: "r".into(),
                substitution: vec![("x".into(), child), ("$a".into(), a), ("$b".into(), b)]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![premise, side],
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
        let proof = store.ordinary(
            Proposition::new(input, side),
            Justification::Rule {
                name: "nested".into(),
                substitution: vec![("x".into(), a), ("y".into(), g)].into_iter().collect(),
                premise_proofs: premises,
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
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: "guard".into(),
                substitution: substitution.into_iter().collect(),
                premise_proofs: vec![root, root],
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
        program
            .add_rewrite(
                &mut dag,
                &format!(
                    r#"(rewrite (Pair x y) (Hit) :when (({predicate} x y)) :name "{predicate}")"#,
                ),
            )
            .unwrap();
    }
    let (a, b, input) = (program.lets["a"], program.lets["b"], program.lets["input"]);
    let hit = dag.app("Hit".into(), vec![]);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(input, input);
    let union = store.fiat(a, program.unions[0].rhs);
    let reflexive = store.fiat(a, a);
    let wrong_left = store.sym(union);
    for (predicate, evidence, valid) in [
        ("renaming-=", union, true),
        ("=", union, false),
        ("renaming-=", reflexive, false),
        ("renaming-=", wrong_left, false),
    ] {
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: predicate.into(),
                substitution: vec![("x".into(), a), ("y".into(), b)].into_iter().collect(),
                premise_proofs: vec![root, evidence],
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
        program
            .add_rewrite(
                &mut dag,
                &format!(
                    r#"(rewrite (Pair x y) (Hit) :when (({predicate} x y)) :name "{predicate}")"#,
                ),
            )
            .unwrap();
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
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: predicate.into(),
                substitution: vec![("x".into(), children[0]), ("y".into(), children[1])]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![root, x, y],
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
        let proof = store.ordinary(
            Proposition::new(input, zero),
            Justification::Rule {
                name: format!("guard{i}"),
                substitution: vec![("$s".into(), zero), ("x".into(), one), ("y".into(), zero)]
                    .into_iter()
                    .collect(),
                premise_proofs: (if i < 2 {
                    vec![root, x, y]
                } else if i == 2 {
                    vec![root, x]
                } else {
                    vec![root, y]
                }),
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
    let wrap = store.ordinary(
        Proposition::new(t, wrapped),
        Justification::Rule {
            name: "wrap".into(),
            substitution: vec![("x".into(), num1), ("y".into(), num2), ("$s".into(), s4)]
                .into_iter()
                .collect(),
            premise_proofs: vec![root],
        },
    );
    check_proof(&mut store, &program, wrap).unwrap();

    // eta on the wrapped term: (Lam $4 (App t $4)) = t, with $4 not free in t
    let eta = store.ordinary(
        Proposition::new(wrapped, t),
        Justification::Rule {
            name: "eta".into(),
            substitution: vec![("$x".into(), s4), ("f".into(), t)]
                .into_iter()
                .collect(),
            premise_proofs: vec![wrap, root],
        },
    );
    check_proof(&mut store, &program, eta).unwrap();

    // minting a slot the other bindings mention is refused
    let s1 = slot_term(&mut store.term_dag, 1);
    let f1 = store.term_dag.app("F".into(), vec![s1, num2]);
    let app1 = store.term_dag.app("App".into(), vec![f1, s1]);
    let bad_wrapped = store.term_dag.app("Lam".into(), vec![s1, app1]);
    let f1_root = store.ordinary(Proposition::new(f1, f1), Justification::Fiat);
    let bad = store.ordinary(
        Proposition::new(f1, bad_wrapped),
        Justification::Rule {
            name: "wrap".into(),
            substitution: vec![("x".into(), s1), ("y".into(), num2), ("$s".into(), s1)]
                .into_iter()
                .collect(),
            premise_proofs: vec![f1_root],
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
        let proof = store.ordinary(
            Proposition::new(input, rhs),
            Justification::Rule {
                name: "r".into(),
                substitution: vec![("x".into(), one), ("$fresh".into(), fresh)]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![root],
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
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: "r".into(),
                substitution: vec![("x".into(), zero), ("y".into(), one)]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![root, side],
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
        let proof = store.ordinary(
            Proposition::new(fixed, other),
            Justification::Rule {
                name: "r".into(),
                substitution: vec![("x".into(), other), ("y".into(), fixed)]
                    .into_iter()
                    .collect(),
                premise_proofs: premises,
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
    let proof = store.ordinary(
        Proposition::new(fixed, fresh),
        Justification::Rule {
            name: "r".into(),
            substitution: vec![("x".into(), fixed), ("$fresh".into(), fresh)]
                .into_iter()
                .collect(),
            premise_proofs: vec![root, side],
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
    let aliased = store.ordinary(
        Proposition::new(ff, a),
        Justification::Rule {
            name: "distinct".into(),
            substitution: vec![("$x".into(), s0), ("$y".into(), s0)]
                .into_iter()
                .collect(),
            premise_proofs: vec![root],
        },
    );
    let err = check_proof(&mut store, &program, aliased).unwrap_err();
    assert!(err.to_string().contains("different slot literals"), "{err}");
    // a slot literal is bound to a slot, never to a term
    let root = store.fiat(fa, fa);
    let non_slot = store.ordinary(
        Proposition::new(fa, a),
        Justification::Rule {
            name: "distinct".into(),
            substitution: vec![("$x".into(), a), ("$y".into(), s0)]
                .into_iter()
                .collect(),
            premise_proofs: vec![root],
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
        store.ordinary(
            Proposition::new(term, slot),
            Justification::Rule {
                name: "unwrap".into(),
                substitution: vec![("x".into(), slot)].into_iter().collect(),
                premise_proofs: vec![root],
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
        let proof = store.ordinary(
            Proposition::new(s0, s1),
            Justification::Rule {
                name: "r".into(),
                substitution: vec![
                    ("x".into(), s0),
                    ("y".into(), s1),
                    ("p".into(), program.lets["pair"]),
                ]
                .into_iter()
                .collect(),
                premise_proofs: vec![root, side],
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
    let trans = store.ordinary(Proposition::new(m7, m7), Justification::Trans(union, refl));
    let err = check_proof(&mut store, &program, trans).unwrap_err();
    assert!(err.to_string().contains("matching middle terms"), "{err}");
    // a congruence whose child proof is about another term
    let congr = store.ordinary(
        Proposition::new(m7, m7),
        Justification::Congr {
            proof: refl,
            child_index: 1,
            child_proof: union,
        },
    );
    let err = check_proof(&mut store, &program, congr).unwrap_err();
    assert!(err.to_string().contains("child proof lhs"), "{err}");
    // a step stating something other than what it derives
    let sym = store.ordinary(Proposition::new(m7, zero), Justification::Sym(union));
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
    let first = store.ordinary(
        Proposition::new(zero, m7),
        Justification::Sym(ProofId::from_usize(next + 1)),
    );
    assert_eq!(first, ProofId::from_usize(next));
    let second = store.ordinary(Proposition::new(m7, zero), Justification::Sym(first));
    let err = check_proof(&mut store, &program, second).unwrap_err();
    assert!(err.to_string().contains("cyclic"), "{err}");
}

#[test]
fn renaming_guards_preserve_binding_scopes_and_injectivity() {
    for (representative, candidate, valid) in [
        ("(Lam $0 (Pair $0 $1))", "(Lam $2 (Pair $2 $3))", true),
        ("(Lam $0 (Pair $0 $1))", "(Lam $2 (Pair $2 $2))", false),
        ("(Pair $0 $1)", "(Pair $2 $2)", false),
        ("(Lam $0 (Lam $0 $0))", "(Lam $1 (Lam $2 $1))", false),
    ] {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("A", vec![]);
        program.add_constructor("Hit", vec![]);
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_let(&mut dag, "a", "(A)").unwrap();
        program.add_let(&mut dag, "b", candidate).unwrap();
        program.add_let(&mut dag, "input", "(Pair a b)").unwrap();
        program
            .add_union(&mut dag, "a", representative, "U")
            .unwrap();
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (Pair x y) (Hit) :when ((renaming-= x y)) :name "guard")"#,
            )
            .unwrap();
        let (a, b, input) = (program.lets["a"], program.lets["b"], program.lets["input"]);
        let hit = dag.app("Hit".into(), vec![]);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        let witness = store.fiat(a, program.unions[0].rhs);
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: "guard".into(),
                substitution: [("x".into(), a), ("y".into(), b)].into_iter().collect(),
                premise_proofs: vec![root, witness],
            },
        );
        assert_eq!(
            check_proof(&mut store, &program, proof).is_ok(),
            valid,
            "{representative} versus {candidate}"
        );
    }
}
