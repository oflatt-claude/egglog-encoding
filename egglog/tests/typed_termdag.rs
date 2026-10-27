use egglog::ast::Literal;
use egglog::{Context, EGraph, GroundTypeError, TermDag, TypedTerm};

#[test]
fn source_signatures_are_available_from_unexecuted_encoded_declarations() {
    use egglog::ResolvedCall;
    use egglog::ast::{FunctionRole, FunctionSubtype};

    let mut eg = EGraph::default();
    // No original typechecker and no runtime tables: everything needed to type
    // source terms must come from these encoded declarations.
    eg.resolve_program(
        None,
        r#"
        (sort E)
        (sort Es (Vec E))
        (sort Ints (Vec i64))
        (function C (Es) (E Unit) :no-merge :internal-role constructor-view)
        (function F (E) (E Unit) :no-merge :internal-role function-view)
        (function g () (E Unit) :no-merge :internal-role global-view)
        (function TupleEntry () (E Unit) :no-merge)
        (prove-extract (F (C (vec-empty))))
        (prove-extract g)
        "#,
    )
    .unwrap();

    let mut terms = TermDag::default();
    let empty = terms.app("vec-empty".into(), vec![]);
    let constructor = terms.app("C".into(), vec![empty]);
    let function = terms.app("F".into(), vec![constructor]);
    let global = terms.app("g".into(), vec![]);
    let types = eg.type_info();
    let source = types.source_types();
    let (typed, roots) = source
        .typecheck_term_dag(
            &terms,
            &[(constructor, None), (function, None), (global, None)],
            Context::Read,
        )
        .unwrap();
    for (id, subtype, role) in [
        (
            roots[0],
            FunctionSubtype::Constructor,
            FunctionRole::Ordinary,
        ),
        (roots[1], FunctionSubtype::Custom, FunctionRole::Ordinary),
        (roots[2], FunctionSubtype::Custom, FunctionRole::Global),
    ] {
        let TypedTerm::App(ResolvedCall::Func(call), _) = typed.get(id) else {
            panic!("expected a resolved source function");
        };
        assert_eq!(call.subtype, subtype);
        assert_eq!(call.role, role);
        assert_eq!(call.num_outputs(), 1);
        assert_eq!(call.output().name(), "E");
    }
    let TypedTerm::App(_, children) = typed.get(roots[0]) else {
        unreachable!();
    };
    assert_eq!(typed.get(children[0]).sort().name(), "Es");

    // Table typing retains all columns, and an unmarked tuple function is not
    // silently treated as a view just because its shape matches one.
    assert_eq!(types.get_func_type("C").unwrap().num_outputs(), 2);
    assert!(
        types
            .typecheck_term_dag(&terms, &[(constructor, None)], Context::Read)
            .is_err()
    );
    let pair = terms.app("TupleEntry".into(), vec![]);
    assert!(
        source
            .typecheck_term_dag(&terms, &[(pair, None)], Context::Read)
            .is_err()
    );
}

#[test]
fn shared_polymorphic_syntax_has_independent_typings() {
    let mut eg = EGraph::default();
    eg.parse_and_run_program(
        None,
        "
        (datatype A (MakeA))
        (datatype B (MakeB))
        (sort As (Vec A))
        (sort Bs (Vec B))
        (datatype Root (Wrap As Bs))
    ",
    )
    .unwrap();
    let mut terms = TermDag::default();
    let empty = terms.app("vec-empty".into(), vec![]);
    let wrap = terms.app("Wrap".into(), vec![empty, empty]);
    let a_sort = eg.type_info().get_sort_by_name("As").unwrap().clone();
    let b_sort = eg.type_info().get_sort_by_name("Bs").unwrap().clone();
    let (typed, roots) = eg
        .type_info()
        .typecheck_term_dag(
            &terms,
            &[
                (wrap, None),
                (empty, Some(b_sort)),
                (empty, Some(a_sort)),
                (wrap, None),
            ],
            Context::Read,
        )
        .unwrap();
    let TypedTerm::App(_, children) = typed.get(roots[0]) else {
        panic!()
    };
    assert_ne!(children[0], children[1]);
    assert_eq!(roots, [roots[0], children[1], children[0], roots[0]]);
    assert_eq!(typed.to_string(children[0]), terms.to_string(empty));
    assert_eq!(typed.to_string(children[1]), terms.to_string(empty));
    assert_eq!(typed.get(children[0]).sort().name(), "As");
    assert_eq!(typed.get(children[1]).sort().name(), "Bs");
    assert_eq!(typed.nodes().len(), 3);
}

#[test]
fn nested_primitives_constrain_overloads_bottom_up() {
    let mut eg = EGraph::default();
    eg.parse_and_run_program(
        None,
        "
        (sort Numbers (Map String i64))
        (sort Words (Map String String))
    ",
    )
    .unwrap();
    let mut terms = TermDag::default();
    let key = terms.lit(Literal::String("key".into()));
    let value = terms.lit(Literal::Int(42));
    let map = terms.app("map-of".into(), vec![key, value]);
    let length = terms.app("map-length".into(), vec![map]);
    let (typed, roots) = eg
        .type_info()
        .typecheck_term_dag(&terms, &[(length, None)], Context::Read)
        .unwrap();
    let TypedTerm::App(_, children) = typed.get(roots[0]) else {
        panic!()
    };
    assert_eq!(typed.get(roots[0]).sort().name(), "i64");
    assert_eq!(typed.get(children[0]).sort().name(), "Numbers");
    assert_eq!(eg.num_nodes(), 0, "typing must not insert any terms");
}

#[test]
fn expected_root_sort_selects_an_overload_but_not_ambiguous_children() {
    let mut eg = EGraph::default();
    eg.parse_and_run_program(None, "(sort Ints (Vec i64)) (sort Strings (Vec String))")
        .unwrap();
    let ints = eg.type_info().get_sort_by_name("Ints").unwrap().clone();
    let i64_sort = eg.type_info().get_sort_by_name("i64").unwrap().clone();
    let mut terms = TermDag::default();
    let empty = terms.app("vec-empty".into(), vec![]);
    let length = terms.app("vec-length".into(), vec![empty]);
    assert!(matches!(
        eg.type_info()
            .typecheck_term_dag(&terms, &[(empty, None)], Context::Read),
        Err(GroundTypeError::Ambiguous { .. })
    ));
    let (typed, roots) = eg
        .type_info()
        .typecheck_term_dag(&terms, &[(empty, Some(ints))], Context::Read)
        .unwrap();
    assert_eq!(typed.get(roots[0]).sort().name(), "Ints");
    assert!(matches!(
        eg.type_info()
            .typecheck_term_dag(&terms, &[(length, Some(i64_sort))], Context::Read),
        Err(GroundTypeError::Ambiguous { .. })
    ));
}

#[test]
fn shared_ground_dag_stays_shared_and_does_not_use_the_call_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut eg = EGraph::default();
            eg.parse_and_run_program(None, "(datatype E (A) (Pair E E))")
                .unwrap();
            let mut terms = TermDag::default();
            let mut root = terms.app("A".into(), vec![]);
            for _ in 0..2000 {
                root = terms.app("Pair".into(), vec![root, root]);
            }
            let (typed, _) = eg
                .type_info()
                .typecheck_term_dag(&terms, &[(root, None)], Context::Read)
                .unwrap();
            assert_eq!(typed.nodes().len(), terms.size());
            for (_, node) in typed.nodes() {
                if let TypedTerm::App(_, children) = node
                    && children.len() == 2
                {
                    assert_eq!(children[0], children[1]);
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn rejects_wrong_types_variables_and_invalid_references() {
    let mut eg = EGraph::default();
    let mut terms = TermDag::default();
    let one = terms.lit(Literal::Int(1));
    let word = terms.lit(Literal::String("hello".into()));
    let bad = terms.app("+".into(), vec![one, word]);
    let variable = terms.var("x".into());
    assert!(
        eg.type_info()
            .typecheck_term_dag(&terms, &[(bad, None)], Context::Read)
            .is_err()
    );
    assert!(matches!(
        eg.type_info()
            .typecheck_term_dag(&terms, &[(variable, None)], Context::Read),
        Err(GroundTypeError::Variable { .. })
    ));
    assert!(matches!(
        eg.type_info()
            .typecheck_term_dag(&terms, &[(terms.size(), None)], Context::Read),
        Err(GroundTypeError::InvalidTerm { .. })
    ));
    let string = eg.type_info().get_sort_by_name("String").unwrap().clone();
    assert!(matches!(
        eg.type_info()
            .typecheck_term_dag(&terms, &[(one, Some(string))], Context::Read),
        Err(GroundTypeError::WrongSort { .. })
    ));
    // Neither the bad application nor the unbound variable is reachable here.
    eg.type_info()
        .typecheck_term_dag(&terms, &[(one, None)], Context::Read)
        .unwrap();
}

#[test]
fn primitive_resolution_obeys_the_requested_capability_context() {
    let mut eg = EGraph::default();
    eg.parse_and_run_program(None, "(datatype E (A)) (sort Es (Vec E))")
        .unwrap();
    let mut terms = TermDag::default();
    let empty = terms.app("vec-empty".into(), vec![]);
    let union = terms.app("vec-union".into(), vec![empty, empty]);
    assert!(
        eg.type_info()
            .typecheck_term_dag(&terms, &[(union, None)], Context::Read)
            .is_err()
    );
    eg.type_info()
        .typecheck_term_dag(&terms, &[(union, None)], Context::Full)
        .unwrap();
}

#[test]
fn indistinguishable_primitive_registrations_are_rejected() {
    use egglog::ast::Span;
    use egglog::constraint::{SimpleTypeConstraint, TypeConstraint};
    use egglog::{Primitive, PurePrim, PureState, Value};

    #[derive(Clone)]
    struct Identity(egglog::ArcSort);
    impl Primitive for Identity {
        fn name(&self) -> &str {
            "identity"
        }
        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(
                self.name(),
                vec![self.0.clone(), self.0.clone()],
                span.clone(),
            )
            .into_box()
        }
    }
    impl PurePrim for Identity {
        fn apply<'a, 'db>(&self, _: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
            Some(args[0])
        }
    }

    let mut eg = EGraph::default();
    let i64_sort = eg.type_info().get_sort_by_name("i64").unwrap().clone();
    let string = eg.type_info().get_sort_by_name("String").unwrap().clone();
    eg.add_pure_primitive(Identity(i64_sort.clone()), None);
    eg.add_pure_primitive(Identity(i64_sort), None);
    eg.add_pure_primitive(Identity(string), None);
    let mut terms = TermDag::default();
    let one = terms.lit(Literal::Int(1));
    let word = terms.lit(Literal::String("hello".into()));
    let bad = terms.app("identity".into(), vec![one]);
    let good = terms.app("identity".into(), vec![word]);
    assert!(matches!(
        eg.type_info()
            .typecheck_term_dag(&terms, &[(bad, None)], Context::Read),
        Err(GroundTypeError::Type {
            source: egglog::TypeError::AmbiguousPrimitive { .. },
            ..
        })
    ));
    eg.type_info()
        .typecheck_term_dag(&terms, &[(good, None)], Context::Read)
        .unwrap();
}
