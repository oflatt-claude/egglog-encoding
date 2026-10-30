use super::check_proof;
use crate::slotted::proofs::format::{SlottedProof, SlottedProofStore};
use crate::slotted::proofs::source::{ColumnKind, SlottedProgram};
use crate::slotted::proofs::terms::{Renaming, slot_term};
use egglog::ast::Literal;
use egglog::proof::{Justification, Proposition};
use egglog::{Term, TermDag};

#[test]
fn ordinary_guard_normal_form_requires_nested_operand_evidence() {
    for local in ["x", "@slotted-proof-v"] {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_constructor("F", vec![ColumnKind::Child]);
        program.add_constructor("G", vec![ColumnKind::Child]);
        program.add_constructor("Hit", vec![]);
        program.add_let(&mut dag, "input", "(Pair $0 $1)").unwrap();
        program
            .add_union(&mut dag, "(F $1)", "(G $1)", "U")
            .unwrap();
        program
            .add_rewrite(&mut dag, &format!(r#"(rewrite (Pair $s {local}) (Hit) :when ((not-free $s (F {local}))) :name "r")"#))
            .unwrap();
        let input = program.lets["input"];
        let a = slot_term(&mut dag, 0);
        let b = slot_term(&mut dag, 1);
        let hit = dag.app("Hit".into(), vec![]);
        let unit = dag.lit(Literal::Unit);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        let operand = program.unions[0].lhs;
        let existence = store.fiat(operand, operand);
        let changed = store.fiat(operand, program.unions[0].rhs);
        let result = store.fiat(unit, unit);
        let wrong_result = store.fiat(a, a);
        for (premises, valid) in [
            (vec![root, existence, result], true),
            (vec![root, result], false),
            (vec![root, root, result], false),
            (vec![root, changed, result], false),
            (vec![root, existence, wrong_result], false),
        ] {
            let proof = store.ordinary(
                Proposition::new(input, hit),
                Justification::Rule {
                    name: "r".into(),
                    substitution: [("$s".into(), a), (local.into(), b)].into_iter().collect(),
                    premise_proofs: premises,
                },
            );
            assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
        }
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
    let unit = store.term_dag.lit(Literal::Unit);
    let guard = store.fiat(unit, unit);
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
                premise_proofs: vec![root, root, guard],
            },
        );
        let error = check_proof(&mut store, &program, proof)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains(if override_global {
                "overrides captured global"
            } else {
                "Primitive 'slotted-proof-free' validation failed"
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
    for predicate in ["=", "renaming-=", "renaming-!="] {
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
    let right = store.fiat(b, b);
    let wrong_left = store.sym(union);
    for (predicate, evidence, valid) in [
        ("renaming-=", union, true),
        ("=", union, false),
        ("renaming-=", reflexive, false),
        ("renaming-=", wrong_left, false),
    ] {
        let evidence = if predicate == "renaming-=" {
            store.renaming_eq(evidence, right)
        } else {
            evidence
        };
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

    for (predicate, guard, error) in [
        ("renaming-=", union, "requires a RenamingEq proof"),
        (
            "renaming-=",
            store.renaming_eq(right, union),
            "equality fact mismatch",
        ),
        (
            "renaming-!=",
            store.renaming_eq(union, right),
            "is not an equality",
        ),
    ] {
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: predicate.into(),
                substitution: [("x".into(), a), ("y".into(), b)].into_iter().collect(),
                premise_proofs: vec![root, guard],
            },
        );
        let actual = check_proof(&mut store, &program, proof).unwrap_err();
        assert!(actual.to_string().contains(error), "{actual}");
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
    let unit = store.term_dag.lit(Literal::Unit);
    let guard = store.fiat(unit, unit);
    for (predicate, valid) in [("!=", true), ("renaming-!=", false)] {
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: predicate.into(),
                substitution: vec![("x".into(), children[0]), ("y".into(), children[1])]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![root, guard],
            },
        );
        assert_eq!(check_proof(&mut store, &program, proof).is_ok(), valid);
    }
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
    let unit = store.term_dag.lit(Literal::Unit);
    let guard = store.fiat(unit, unit);
    for (i, (condition, valid)) in cases.iter().enumerate() {
        let proof = store.ordinary(
            Proposition::new(input, zero),
            Justification::Rule {
                name: format!("guard{i}"),
                substitution: vec![("$s".into(), zero), ("x".into(), one), ("y".into(), zero)]
                    .into_iter()
                    .collect(),
                premise_proofs: vec![root, guard],
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
        let right = store.fiat(b, b);
        let guard = store.renaming_eq(witness, right);
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: "guard".into(),
                substitution: [("x".into(), a), ("y".into(), b)].into_iter().collect(),
                premise_proofs: vec![root, guard],
            },
        );
        assert_eq!(
            check_proof(&mut store, &program, proof).is_ok(),
            valid,
            "{representative} versus {candidate}"
        );
    }
}

#[test]
fn guard_evidence_cannot_be_used_as_an_equality() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_let(&mut dag, "input", "(F $0)").unwrap();
    program
        .add_rewrite(&mut dag, r#"(rewrite (F x) x :when ((= x x)) :name "r")"#)
        .unwrap();
    let input = program.lets["input"];
    let slot = slot_term(&mut dag, 0);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(input, input);
    let refl = store.fiat(slot, slot);
    let guard = store.renaming_eq(refl, refl);
    assert!(check_proof(&mut store, &program, guard).is_err());

    for step in [
        Justification::Sym(guard),
        Justification::Trans(refl, guard),
        Justification::Congr {
            proof: root,
            child_index: 0,
            child_proof: guard,
        },
        Justification::Proj {
            proof: guard,
            child_index: 0,
        },
        Justification::Rule {
            name: "r".into(),
            substitution: [("x".into(), slot)].into_iter().collect(),
            premise_proofs: vec![root, guard],
        },
    ] {
        let proof = store.ordinary(Proposition::new(input, slot), step);
        let error = check_proof(&mut store, &program, proof).unwrap_err();
        assert!(error.to_string().contains("is not an equality"), "{error}");
    }
    for step in [
        SlottedProof::Alpha {
            proposition: Proposition::new(slot, slot),
            proof: guard,
        },
        SlottedProof::Equivariance {
            proposition: Proposition::new(slot, slot),
            proof: guard,
            renaming: Renaming::identity(),
        },
        SlottedProof::RenamingEq {
            left: guard,
            right: refl,
        },
    ] {
        let proof = store.add(step);
        let error = check_proof(&mut store, &program, proof).unwrap_err();
        assert!(error.to_string().contains("is not an equality"), "{error}");
    }
}

#[test]
fn guard_representatives_preserve_captured_operands_and_later_binder_declarations() {
    for (local, operands) in [
        ("y", "x y"),
        ("y", "fixed other"),
        ("@slotted-guard-argument", "x @slotted-guard-argument"),
    ] {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        for name in ["A", "B", "Hit"] {
            program.add_constructor(name, vec![]);
        }
        program.add_let(&mut dag, "fixed", "(A)").unwrap();
        program.add_let(&mut dag, "other", "(B)").unwrap();
        program
            .add_let(&mut dag, "input", "(Pair fixed other)")
            .unwrap();
        program
            .add_rewrite(
                &mut dag,
                &format!(
                    r#"(rewrite (Pair x {local}) (Hit) :when ((renaming-= {operands})) :name "r")"#
                ),
            )
            .unwrap();
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        // The left term reuses $0 as a bound and a free name. Treating Lam as
        // an ordinary constructor would reject this valid renaming.
        program
            .add_union(&mut dag, "fixed", "(Pair (Lam $0 $0) $0)", "U")
            .unwrap();
        program
            .add_union(&mut dag, "other", "(Pair (Lam $2 $2) $3)", "U")
            .unwrap();
        let (a, b, input) = (
            program.lets["fixed"],
            program.lets["other"],
            program.lets["input"],
        );
        program.add_let(&mut dag, "fixed", "$9").unwrap();
        program.add_let(&mut dag, "other", "$10").unwrap();
        let hit = dag.app("Hit".into(), vec![]);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        let left = store.fiat(a, program.unions[0].rhs);
        let right = store.fiat(b, program.unions[1].rhs);
        let guard = store.renaming_eq(left, right);
        let proof = store.ordinary(
            Proposition::new(input, hit),
            Justification::Rule {
                name: "r".into(),
                substitution: [("x".into(), a), (local.into(), b)].into_iter().collect(),
                premise_proofs: vec![root, guard],
            },
        );
        check_proof(&mut store, &program, proof).unwrap();
        let simplified = store.simplify(proof);
        check_proof(&mut store, &program, simplified).unwrap();
    }
}

#[test]
fn guard_operand_equalities_keep_their_carrier_sort() {
    for (sort, valid) in [("U", true), ("V", false)] {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_let(&mut dag, "input", "(Pair $0 $1)").unwrap();
        program.add_union(&mut dag, "$0", "$1", sort).unwrap();
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (Pair x y) x :when ((renaming-= x y)) :name "r")"#,
            )
            .unwrap();
        let input = program.lets["input"];
        let a = slot_term(&mut dag, 0);
        let b = slot_term(&mut dag, 1);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(input, input);
        let left = store.fiat(a, b);
        let right = store.fiat(b, b);
        let guard = store.renaming_eq(left, right);
        let proof = store.ordinary(
            Proposition::new(input, a),
            Justification::Rule {
                name: "r".into(),
                substitution: [("x".into(), a), ("y".into(), b)].into_iter().collect(),
                premise_proofs: vec![root, guard],
            },
        );
        assert_eq!(
            check_proof(&mut store, &program, proof).is_ok(),
            valid,
            "{sort}"
        );
    }
}
