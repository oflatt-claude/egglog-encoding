use egglog::ast::Span;
use egglog::constraint::{SimpleTypeConstraint, TypeConstraint};
use egglog::sort::VecContainer;
use egglog::{
    ArcSort, Core, EGraph, Primitive, PrimitiveValidator, PurePrim, PureState, Term, Value,
};

#[derive(Clone)]
struct FirstWithDecoy {
    vector: ArcSort,
    element: ArcSort,
}

impl Primitive for FirstWithDecoy {
    fn name(&self) -> &str {
        "first-with-decoy"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![
                self.vector.clone(),
                self.element.clone(),
                self.element.clone(),
            ],
            span.clone(),
        )
        .into_box()
    }
}

impl PurePrim for FirstWithDecoy {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [vector, _decoy] = args else {
            return None;
        };
        state
            .container_values()
            .get_val::<VecContainer>(*vector)?
            .data
            .first()
            .copied()
    }
}

#[derive(Clone)]
struct DeepFirst {
    outer: ArcSort,
    element: ArcSort,
}

impl Primitive for DeepFirst {
    fn name(&self) -> &str {
        "deep-first"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![self.outer.clone(), self.element.clone()],
            span.clone(),
        )
        .into_box()
    }
}

impl PurePrim for DeepFirst {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [outer] = args else {
            return None;
        };
        let inner = state
            .container_values()
            .get_val::<VecContainer>(*outer)?
            .data
            .first()
            .copied()?;
        state
            .container_values()
            .get_val::<VecContainer>(inner)?
            .data
            .first()
            .copied()
    }
}

#[test]
fn proj_prim_uses_the_typed_container_argument() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(None, "(datatype N (Z) (S N)) (sort Ns (Vec N))")
        .unwrap();

    let vector = egraph.get_sort_by_name("Ns").unwrap().clone();
    let element = egraph.get_sort_by_name("N").unwrap().clone();
    let validator: PrimitiveValidator = std::sync::Arc::new(|dag, args| {
        let [vector, _decoy] = args else {
            return None;
        };
        let Term::App(head, children) = dag.get(*vector) else {
            return None;
        };
        if head != "vec-of" {
            return None;
        }
        children.first().copied()
    });
    egraph.add_pure_primitive(FirstWithDecoy { vector, element }, Some(validator));

    // The validator returns `(Z)` from `xs`, while the non-container decoy
    // `(S (Z))` also has `(Z)` as a direct child. Only the typed `Ns` argument
    // is valid projection provenance.
    egraph
        .parse_and_run_program(
            None,
            r#"
            (constructor Holder (Ns) N)
            (relation Seen (N))
            (let $held (Holder (vec-of (Z))))
            (let $decoy (S (Z)))

            (rule ((= $held (Holder xs))
                   (= z (first-with-decoy xs $decoy)))
                  ((Seen z))
                  :name "first-with-decoy")

            (run 1)
            (prove (Seen (Z)))
            "#,
        )
        .unwrap();
}

#[test]
fn proj_prim_builds_projection_chain_through_nested_containers() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(
            None,
            "(datatype N (Z)) (sort Ns (Vec N)) (sort Nss (Vec Ns))",
        )
        .unwrap();

    let outer = egraph.get_sort_by_name("Nss").unwrap().clone();
    let element = egraph.get_sort_by_name("N").unwrap().clone();
    let validator: PrimitiveValidator = std::sync::Arc::new(|dag, args| {
        let [outer] = args else {
            return None;
        };
        let Term::App(outer_head, outer_children) = dag.get(*outer) else {
            return None;
        };
        if outer_head != "vec-of" {
            return None;
        }
        let inner = *outer_children.first()?;
        let Term::App(inner_head, inner_children) = dag.get(inner) else {
            return None;
        };
        if inner_head != "vec-of" {
            return None;
        }
        inner_children.first().copied()
    });
    egraph.add_pure_primitive(DeepFirst { outer, element }, Some(validator));

    egraph
        .parse_and_run_program(
            None,
            r#"
            (constructor Holder (Nss) N)
            (relation Seen (N))
            (let $held (Holder (vec-of (vec-of (Z)))))

            (rule ((= $held (Holder xss))
                   (= z (deep-first xss)))
                  ((Seen z))
                  :name "deep-first")

            (run 1)
            (prove (Seen (Z)))
            "#,
        )
        .unwrap();
}
