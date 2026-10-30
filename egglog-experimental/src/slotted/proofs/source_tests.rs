use super::*;

#[test]
fn parses_rewrites_lets_unions_and_claims() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("App", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor("Mul", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor("Null", vec![]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_let(&mut dag, "m7", "(Mul $7 (Null))").unwrap();
    program.add_let(&mut dag, "zero", "(Null)").unwrap();
    program.add_union(&mut dag, "m7", "zero", "U").unwrap();
    let claim = program
        .claim(&mut dag, "=", "U", "(Mul $9 (Null))", "zero")
        .unwrap();
    let name = program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (Lam $x (App f $x)) f :name "eta" :when ((not-free $x f)))"#,
        )
        .unwrap();
    assert_eq!(name, "eta");
    let eta = &program.rewrites["eta"];
    let (lhs, rhs) = eta.endpoints();
    assert_eq!(lhs.to_string(), "(Lam $x (App f $x))");
    assert_eq!(rhs.to_string(), "f");
    assert_eq!(eta.conditions()[0].to_string(), "(not-free $x f)");
    // a condition names as many variables as it likes
    program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (App (Lam $z x) y) (App x y) :name "two" :when ((not-free $z x y)))"#,
        )
        .unwrap();
    assert_eq!(
        program.rewrites["two"].conditions()[0].to_string(),
        "(not-free $z x y)"
    );
    let Union { lhs: a, rhs: b, .. } = program.unions[0].clone();
    assert_eq!(program.unions[0].sort, "U");
    assert_eq!(dag.to_string(a), "(Mul $7 (Null))");
    assert_eq!(dag.to_string(b), "(Null)");
    assert!(program.is_union(b, a));
    assert!(program.is_built(&dag, a));
    assert_eq!(claim.kind, ClaimKind::Eq);
    assert_eq!(dag.to_string(claim.lhs), "(Mul $9 (Null))");
}

#[test]
fn free_slots_respect_binders() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("App", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor(
        "Let",
        vec![ColumnKind::Child, ColumnKind::Binder, ColumnKind::Child],
    );
    program
        .add_let(&mut dag, "k", "(Lam $0 (App $0 $3))")
        .unwrap();
    assert_eq!(
        program.free_slots(&dag, program.lets["k"]),
        BTreeSet::from([3])
    );
    program.add_let(&mut dag, "l", "(Let $1 $1 $1)").unwrap();
    // the value's occurrence is free, the body's is bound
    assert_eq!(
        program.free_slots(&dag, program.lets["l"]),
        BTreeSet::from([1])
    );
}

#[test]
fn alpha_matching_preserves_free_names_and_binding_scope() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("Pair", vec![ColumnKind::Child, ColumnKind::Child]);
    program.add_constructor(
        "Let",
        vec![ColumnKind::Binder, ColumnKind::Child, ColumnKind::Child],
    );
    for (a, b, equal) in [
        ("(Lam $0 (Pair $0 $3))", "(Lam $1 (Pair $1 $3))", true),
        ("(Lam $0 (Pair $0 $3))", "(Lam $1 (Pair $1 $4))", false),
        ("(Lam $0 $1)", "(Lam $1 $1)", false),
        ("(Lam $0 $0)", "(Lam $1 $0)", false),
        ("(Lam $0 (Lam $0 $0))", "(Lam $1 (Lam $2 $2))", true),
        ("(Lam $0 (Lam $1 $0))", "(Lam $2 (Lam $2 $2))", false),
        ("(Let $0 $0 $0)", "(Let $1 $1 $0)", true),
        ("(Let $0 $0 $0)", "(Let $1 $1 $1)", false),
        ("(Pair (Lam $0 $0) $0)", "(Pair (Lam $1 $1) $0)", true),
    ] {
        let terms = program.claim(&mut dag, "=", "U", a, b).unwrap();
        assert_eq!(
            program.alpha_eq(&mut dag, terms.lhs, terms.rhs),
            equal,
            "{a} versus {b}"
        );
        assert_eq!(
            program.alpha_eq(&mut dag, terms.rhs, terms.lhs),
            equal,
            "{b} versus {a}"
        );
    }
}

#[test]
fn renaming_comparison_preserves_aliasing_payloads_and_binding() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("Num", vec![ColumnKind::Payload("i64".into())]);
    for (a, b, equal) in [
        ("(Pair $0 $1)", "(Pair $1 $0)", true),
        ("(Pair $0 $0)", "(Pair $1 $2)", false),
        ("(Lam $0 $0)", "(Lam $1 $2)", false),
        ("(Lam $0 (Pair $0 $1))", "(Lam $2 (Pair $2 $3))", true),
        ("(Pair (Lam $0 $0) $0)", "(Pair (Lam $1 $1) $2)", true),
        ("(Lam $0 (Lam $0 $0))", "(Lam $1 (Lam $2 $2))", true),
        ("(Lam $0 (Lam $0 $0))", "(Lam $1 (Lam $2 $1))", false),
        ("(Num 1)", "(Num 2)", false),
    ] {
        let lhs = program
            .ground_term(&mut dag, &parse_expr(a).unwrap())
            .unwrap();
        let rhs = program
            .ground_term(&mut dag, &parse_expr(b).unwrap())
            .unwrap();
        assert_eq!(
            program.eq_modulo_renaming(&mut dag, lhs, rhs),
            equal,
            "{a} vs {b}"
        );
    }
}

#[test]
fn subst_is_refused() {
    let mut dag = TermDag::default();
    let mut program = SlottedProgram::default();
    program.add_constructor(
        "Let",
        vec![ColumnKind::Child, ColumnKind::Binder, ColumnKind::Child],
    );
    let err = program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (Let t $x b) (subst b $x t) :name "beta")"#,
        )
        .unwrap_err();
    assert!(err.0.contains("subst"));
}
