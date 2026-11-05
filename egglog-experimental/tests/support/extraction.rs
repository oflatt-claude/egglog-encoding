//! Shared extraction correctness instrumentation for ordinary and paper fixtures.
//!
//! Every intercepted top-level source extraction checks the actual returned terms:
//! - Ordinary and congruence-encoded graphs use the same read-only DAG lookup
//!   to require each returned term in the requested root e-class.
//! - Ordinary graphs also check the other tree/greedy-DAG extractor; their cost
//!   models may choose differently.
//! - Proof-enabled graphs check ordered certificates for the exact returned terms
//!   and a checked connection from the requested source root to each certificate's LHS.
//!
//! Extra validation runs on pre-command clones, preserving the real workload graph.
//! Both fixture harnesses share the cost/term/variant comparison policy.
//! For its equal-cost best-term tie policy, this helper also checks a supplied
//! comparison term against the root; it never rewrites returned terms or certificates.
//! Extractions inside included files are not intercepted.
use egglog::{
    CommandOutput, Context, Error, Term, TermDag, TermId,
    ast::{Action, Command, Expr},
    extract::TreeCostModelFromDag,
    span,
    util::FreshGen,
};
use egglog_experimental::*;

pub struct CheckedRun {
    pub outputs: Vec<CommandOutput>,
    /// Per extraction output, equality of an intercepted comparison term to
    /// this run's requested root. Congruence alternatives are judged by the
    /// ordinary run; proof mode also checks the corresponding source proof.
    pub comparison_in_root_class: Vec<Option<bool>>,
}

/// Check source extraction automatically from the graph's enabled features.
/// The root undergoes its normal source evaluation once on the validation clone;
/// returned/comparison candidates are only looked up, never materialized.
/// Included commands retain their normal execution; nested extracts are not intercepted.
pub fn run_program_with_extract_checks(
    egraph: &mut EGraph,
    program: Vec<Command>,
    baseline_terms: &[Option<&str>],
) -> Result<CheckedRun, Error> {
    let mut outputs = Vec::new();
    let mut comparison_in_root_class = Vec::new();

    for command in program {
        let extract = extract_command_parts(&command);
        // Validate from the same pre-command state without letting test
        // instrumentation mutate the program's real e-graph.
        let mut validation_egraph = extract.as_ref().map(|_| egraph.clone());
        let command_outputs = egraph.run_program(vec![command])?;

        let Some(extract) = extract else {
            // Included files execute normally inside their include command.
            // Their outputs retain exact comparison but have no intercepted root.
            comparison_in_root_class.extend(command_outputs.iter().filter_map(|output| {
                matches!(
                    output,
                    CommandOutput::ExtractBest(..) | CommandOutput::ExtractVariants(..)
                )
                .then_some(None)
            }));
            outputs.extend(command_outputs);
            continue;
        };

        let graph = validation_egraph.as_mut().unwrap();
        let baseline = baseline_terms
            .get(comparison_in_root_class.len())
            .copied()
            .flatten()
            .map(|text| graph.parser.get_expr_from_string(None, text))
            .transpose()?;
        // Identical returned syntax already receives membership and certificate
        // checks; do not generate the same equality proof a second time.
        let baseline = baseline.as_ref().filter(|expr| {
            let mut terms = TermDag::default();
            let term = source_term(&mut terms, expr);
            command_outputs.iter().any(|output| matches!(output,
                CommandOutput::ExtractBest(dag, _, actual) if !same_term(dag, *actual, &terms, term)))
        });
        let root = capture_source_value(graph, &extract.root)?;
        let variants = if let Some(variants) = &extract.variants {
            let variants = capture_source_value(graph, variants)?;
            let mut terms = TermDag::default();
            let id = source_term(&mut terms, &variants);
            let value = graph.lookup_term_dag(&terms, &[(id, None)])?.remove(0).1;
            usize::try_from(graph.value_to_base::<i64>(value)).map_err(|_| {
                Error::ExtractError("extract variant count must be nonnegative".into())
            })?
        } else {
            0
        };
        let mut equivalent =
            validate_extract_outputs(graph, &extract, &root, variants, &command_outputs, baseline)?;
        if graph.are_proofs_enabled() {
            let proven = validate_extract_proofs(graph, &root, &command_outputs, baseline)?;
            equivalent = equivalent
                .zip(proven)
                .map(|(present, proven)| present && proven);
        }
        comparison_in_root_class.push(equivalent);
        outputs.extend(command_outputs);
    }

    Ok(CheckedRun {
        outputs,
        comparison_in_root_class,
    })
}

/// Encode ground source expressions for the existing term-DAG APIs. Source
/// variables at a top-level extraction boundary are global zero-argument reads.
fn source_term(dag: &mut TermDag, expr: &Expr) -> TermId {
    match expr {
        Expr::Lit(_, literal) => dag.lit(literal.clone()),
        Expr::Var(_, name) => dag.app(name.clone(), vec![]),
        Expr::Call(_, name, args) => {
            let args = args.iter().map(|arg| source_term(dag, arg)).collect();
            dag.app(name.clone(), args)
        }
    }
}

/// Evaluate a source operand once on the validation clone and retain its value.
/// This captures roots/counts through the normal pipeline, including encoded
/// batched actions that the native eval_expr API cannot execute.
fn capture_source_value(graph: &mut EGraph, root: &Expr) -> Result<Expr, Error> {
    let name = graph.parser.symbol_gen.fresh("extract-validation-root");
    graph.run_program(vec![Command::Action(Action::Let(
        span!(),
        name.clone(),
        root.clone(),
    ))])?;
    Ok(Expr::Var(span!(), name))
}

struct ExtractCheck {
    root: Expr,
    variants: Option<Expr>,
    use_greedy_dag: bool,
}

fn extract_command_parts(command: &Command) -> Option<ExtractCheck> {
    match command {
        Command::Extract(_, root, variants) => Some(ExtractCheck {
            root: root.clone(),
            variants: Some(variants.clone()),
            use_greedy_dag: false,
        }),
        Command::UserDefined(_, name, args) if name == "extract" => {
            let use_greedy_dag = matches!(
                args.last_chunk::<2>(),
                Some([Expr::Var(_, keyword), Expr::Var(..)]) if keyword == ":extractor"
            );
            let positional = if use_greedy_dag {
                args.get(..args.len() - 2)?
            } else {
                args
            };
            match positional {
                [root] => Some(ExtractCheck {
                    root: root.clone(),
                    variants: None,
                    use_greedy_dag,
                }),
                [root, variants] => Some(ExtractCheck {
                    root: root.clone(),
                    variants: Some(variants.clone()),
                    use_greedy_dag,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

fn validate_extract_outputs(
    graph: &mut EGraph,
    extract: &ExtractCheck,
    root: &Expr,
    nvariants: usize,
    outputs: &[CommandOutput],
    baseline: Option<&Expr>,
) -> Result<Option<bool>, Error> {
    let mut root_terms = TermDag::default();
    let root_id = source_term(&mut root_terms, root);
    let (root_sort, root_value) = graph
        .lookup_term_dag(&root_terms, &[(root_id, None)])?
        .remove(0);
    let actual = extracted_terms(outputs)?;
    let paired = if graph
        .functions_iter()
        .any(|(_, function)| function.is_view())
    {
        None
    } else {
        // The root's normal source evaluation has already happened exactly once.
        // Both extractors and all membership lookups now see that same state.
        let roots = vec![(root_sort.clone(), root_value)];
        let (dag, terms) = if nvariants == 0 {
            let extracted = if extract.use_greedy_dag {
                graph.extract_best_with_cost_model(roots, TreeCostModelFromDag(DynamicCostModel))?
            } else {
                extract_best_greedy_dag(graph, roots, DynamicCostModel)?
            };
            let term = extracted
                .terms
                .into_iter()
                .next()
                .expect("one root was requested")
                .ok_or_else(|| {
                    Error::ExtractError("paired extractor returned no term".to_owned())
                })?;
            (extracted.termdag, vec![term.term])
        } else {
            let extracted = if extract.use_greedy_dag {
                graph.extract_variants_with_cost_model(
                    roots,
                    nvariants,
                    TreeCostModelFromDag(DynamicCostModel),
                )?
            } else {
                extract_variants_greedy_dag(graph, roots, nvariants, DynamicCostModel)?
            };
            let terms = extracted
                .variants
                .into_iter()
                .next()
                .expect("one root was requested")
                .into_iter()
                .map(|variant| variant.term)
                .collect();
            (extracted.termdag, terms)
        };
        if actual.is_empty() != terms.is_empty() {
            return Err(Error::ExtractError(
                "only one extractor returned variants for the requested root".to_owned(),
            ));
        }
        Some((dag, terms))
    };
    for (dag, term) in actual.into_iter().chain(
        paired
            .iter()
            .flat_map(|(dag, terms)| terms.iter().map(move |&term| (dag, term))),
    ) {
        let values = graph.lookup_term_dag(dag, &[(term, Some(root_sort.clone()))])?;
        if values[0].1 != root_value {
            return Err(Error::ExtractError(
                "extractor returned a term outside the requested root e-class".into(),
            ));
        }
    }
    if let Some(baseline) = baseline {
        let mut terms = TermDag::default();
        let term = source_term(&mut terms, baseline);
        Ok(Some(
            graph
                .lookup_term_dag(&terms, &[(term, Some(root_sort))])
                .is_ok_and(|values| values[0].1 == root_value),
        ))
    } else {
        Ok(None)
    }
}

fn extracted_terms(outputs: &[CommandOutput]) -> Result<Vec<(&TermDag, TermId)>, Error> {
    let mut saw_extract = false;
    let mut extracted = Vec::new();
    for output in outputs {
        match output {
            CommandOutput::ExtractBest(dag, _, term) => {
                extracted.push((dag, *term));
                saw_extract = true;
            }
            CommandOutput::ExtractVariants(dag, terms) => {
                extracted.extend(terms.iter().map(|&term| (dag, term)));
                saw_extract = true;
            }
            _ => {}
        }
    }
    if saw_extract {
        Ok(extracted)
    } else {
        Err(Error::ExtractError(
            "extract command should produce an extract output".to_owned(),
        ))
    }
}

/// Compare exact source syntax across shared DAGs without expanding them to trees.
fn same_term(left: &TermDag, a: TermId, right: &TermDag, b: TermId) -> bool {
    let mut pending = vec![(a, b)];
    let mut visited = std::collections::HashSet::new();
    while let Some((a, b)) = pending.pop() {
        if !visited.insert((a, b)) {
            continue;
        }
        match (left.get(a), right.get(b)) {
            (Term::Lit(a), Term::Lit(b)) if a == b => {}
            (Term::Var(a), Term::Var(b)) if a == b => {}
            (Term::App(a, xs), Term::App(b, ys)) if a == b && xs.len() == ys.len() => {
                pending.extend(xs.iter().copied().zip(ys.iter().copied()));
            }
            _ => return false,
        }
    }
    true
}

/// Certify the actual extraction outputs in order, with an independently checked
/// connection from the requested source root to each certificate's left endpoint.
/// All supplementary checks run on the pre-command clone, never the real graph.
fn validate_extract_proofs(
    graph: &mut EGraph,
    root: &Expr,
    outputs: &[CommandOutput],
    baseline: Option<&Expr>,
) -> Result<Option<bool>, Error> {
    let terms = extracted_terms(outputs)?;
    let certificates: Vec<_> = outputs
        .iter()
        .filter_map(|output| match output {
            CommandOutput::ProveExtract {
                proof_store,
                proof_ids,
            } => Some((proof_store, proof_ids)),
            _ => None,
        })
        .collect();
    if certificates.len() > 1 {
        return Err(Error::ExtractError(
            "proof-enabled extraction returned multiple proof bundles".into(),
        ));
    }
    // Recording-only source outputs have no bundle. Certify those exact terms
    // locally; validation must never append outputs to the workload's result.
    let generated = if certificates.is_empty() {
        let (mut dag, ids) = outputs
            .iter()
            .find_map(|output| match output {
                CommandOutput::ExtractBest(dag, _, term) => Some((dag.clone(), vec![*term])),
                CommandOutput::ExtractVariants(dag, terms) => Some((dag.clone(), terms.clone())),
                _ => None,
            })
            .expect("validated extraction output");
        let root_id = source_term(&mut dag, root);
        let (typed, roots) = graph
            .typecheck_term_dag(&dag, &[(root_id, None)], Context::Read)
            .map_err(|error| Error::ExtractError(error.to_string()))?;
        Some(graph.prove_extracted_terms(&dag, root_id, &ids, typed.get(roots[0]).sort())?)
    } else {
        None
    };
    let (store, ids) = certificates
        .first()
        .copied()
        .or_else(|| generated.as_ref().map(|(store, ids)| (store, ids)))
        .expect("one supplied or generated proof bundle");
    if ids.len() != terms.len() {
        return Err(Error::ExtractError(
            "extraction certificate count differs from returned terms".into(),
        ));
    }
    let mut dag = store.term_dag().clone();
    let root = source_term(&mut dag, root);
    let (typed, typed_roots) = graph
        .typecheck_term_dag(&dag, &[(root, None)], Context::Read)
        .map_err(|error| Error::ExtractError(error.to_string()))?;
    let sort = typed.get(typed_roots[0]).sort();
    let baseline = baseline.map(|expr| source_term(&mut dag, expr));
    let mut equivalent = None;
    for (id, &(term_dag, term)) in ids.iter().zip(&terms) {
        let proof = store.get(*id);
        if !same_term(store.term_dag(), proof.rhs(), term_dag, term) {
            return Err(Error::ExtractError(
                "certificate RHS differs from the exact returned term".into(),
            ));
        }
        graph.prove_equal_terms(&dag, root, proof.lhs(), sort.clone())?;
        if let Some(baseline) = baseline {
            // The verified bridge above connects the requested root to this
            // certificate's LHS. Prove the tie from that same endpoint, without
            // another evaluation of the source root.
            equivalent = Some(
                graph
                    .prove_equal_terms(&dag, proof.lhs(), baseline, sort.clone())
                    .is_ok(),
            );
        }
    }
    Ok(equivalent)
}

#[cfg(test)]
// The custom files harness omits #[test] functions; paper_support runs them.
#[allow(unused_imports)]
mod tests {
    use super::*;
    use egglog::prelude::BaseSort;

    #[test]
    fn extraction_checks_reject_missing_terms_without_inserting_them() {
        let mut graph = new_experimental_egraph();
        graph
            .parse_and_run_program(None, "(datatype T (A) (B)) (A)")
            .unwrap();
        let command = graph
            .parse_program(None, "(extract (A))")
            .unwrap()
            .remove(0);
        let extract = extract_command_parts(&command).unwrap();
        let outputs = graph.clone().run_program(vec![command]).unwrap();
        assert_eq!(graph.read(|state| state.table_size("B")), Some(0));
        let root = capture_source_value(&mut graph, &extract.root).unwrap();
        let baseline = graph.parser.get_expr_from_string(None, "(B)").unwrap();
        let result =
            validate_extract_outputs(&mut graph, &extract, &root, 0, &outputs, Some(&baseline))
                .unwrap();
        assert_eq!(result, Some(false));
        assert_eq!(
            graph.read(|state| state.table_size("B")),
            Some(0),
            "membership checking must not insert a missing comparison constructor"
        );
        let mut incorrect = outputs.clone();
        for output in &mut incorrect {
            if let CommandOutput::ExtractBest(dag, _, term) = output {
                *term = dag.app("B".into(), vec![]);
            }
        }
        assert!(
            validate_extract_outputs(&mut graph, &extract, &root, 0, &incorrect, None).is_err()
        );
        assert_eq!(graph.read(|state| state.table_size("B")), Some(0));
        graph.parse_and_run_program(None, "(B)").unwrap();
        assert!(
            validate_extract_outputs(&mut graph, &extract, &root, 0, &incorrect, None).is_err(),
            "an existing term in a different class is also invalid"
        );
    }

    #[test]
    fn membership_lookup_canonicalizes_nested_containers_without_insertion() {
        for mut graph in [
            new_experimental_egraph(),
            new_experimental_egraph_with_term_encoding(),
            new_experimental_egraph_with_proof_testing(),
        ] {
            graph
                .parse_and_run_program(
                    None,
                    r#"
                (datatype T (A) (B) (Missing))
                (sort Ts (Vec T))
                (sort Lists (Vec Ts))
                (constructor Bag (Lists) T)
                (let root (Bag (vec-of (vec-of (A)))))
                (let alias root)
                (B)
                (union (A) (B))
                (run 1)
            "#,
                )
                .unwrap();
            let before = graph.print_size(None).unwrap().to_string();
            let mut terms = TermDag::default();
            let roots: Vec<_> = [
                "root",
                "alias",
                "(Bag (vec-of (vec-of (A))))",
                "(Bag (vec-of (vec-of (B))))",
            ]
            .into_iter()
            .map(|text| {
                let expr = graph.parser.get_expr_from_string(None, text).unwrap();
                (source_term(&mut terms, &expr), None)
            })
            .collect();
            let values = graph.lookup_term_dag(&terms, &roots).unwrap();
            assert!(values.iter().all(|(_, value)| *value == values[0].1));
            let expr = graph
                .parser
                .get_expr_from_string(None, "(Bag (vec-of (vec-of (Missing))))")
                .unwrap();
            let missing = source_term(&mut terms, &expr);
            assert!(graph.lookup_term_dag(&terms, &[(missing, None)]).is_err());
            assert_eq!(graph.print_size(None).unwrap().to_string(), before);
        }
    }

    #[test]
    fn shared_extracted_dags_do_not_expand_into_trees_during_checks() {
        for mut graph in [
            new_experimental_egraph(),
            new_experimental_egraph_with_term_encoding(),
            new_experimental_egraph_with_proof_testing(),
        ] {
            let mut source = "(datatype T (A) (Pair T T)) (let t0 (A))".to_owned();
            for depth in 1..=30 {
                source.push_str(&format!(
                    " (let t{depth} (Pair t{} t{}))",
                    depth - 1,
                    depth - 1
                ));
            }
            source.push_str(" (extract t30)");
            let program = graph.parse_program(None, &source).unwrap();
            let checked = run_program_with_extract_checks(&mut graph, program, &[]).unwrap();
            let extracted = extracted_terms(&checked.outputs).unwrap();
            assert_eq!(extracted.len(), 1);
            assert!(extracted[0].0.size() <= 31);
        }
    }

    #[test]
    fn equal_root_membership_does_not_replace_the_exact_returned_term_certificate() {
        let mut graph = new_experimental_egraph_with_proof_testing();
        graph
            .parse_and_run_program(None, "(datatype T (A) (B)) (union (A) (B))")
            .unwrap();
        let command = graph
            .parse_program(None, "(extract (A))")
            .unwrap()
            .remove(0);
        let extract = extract_command_parts(&command).unwrap();
        let mut outputs = graph.clone().run_program(vec![command]).unwrap();
        for output in &mut outputs {
            if let CommandOutput::ExtractBest(dag, _, term) = output {
                let opposite = if dag.to_string(*term) == "(A)" {
                    "B"
                } else {
                    "A"
                };
                *term = dag.app(opposite.into(), vec![]);
            }
        }
        let root = capture_source_value(&mut graph, &extract.root).unwrap();
        assert!(validate_extract_outputs(&mut graph, &extract, &root, 0, &outputs, None).is_ok());
        assert!(validate_extract_proofs(&mut graph, &root, &outputs, None).is_err());
    }

    #[test]
    fn nested_container_lookup_respects_custom_union_find_layouts() {
        for relation in [false, true] {
            let mut graph = new_experimental_egraph();
            let uf = if relation {
                "(sort UF) (constructor Parent (E E) UF) (Parent (A) (A)) (Parent (B) (A))"
            } else {
                "(function Parent (E) E :merge old) (set (Parent (A)) (A)) (set (Parent (B)) (A))"
            };
            graph
                .parse_and_run_program(
                    None,
                    &format!(
                        r#"
                (sort E :internal-uf Parent)
                (constructor A () E) (constructor B () E)
                (sort Es (Vec E)) (sort Lists (Vec Es))
                {uf}
            "#
                    ),
                )
                .unwrap();
            let before = graph.print_size(None).unwrap().to_string();
            let mut terms = TermDag::default();
            let roots: Vec<_> = ["(vec-of (vec-of (A)))", "(vec-of (vec-of (B)))"]
                .into_iter()
                .map(|text| {
                    let expr = graph.parser.get_expr_from_string(None, text).unwrap();
                    (
                        source_term(&mut terms, &expr),
                        Some(graph.get_sort_by_name("Lists").unwrap().clone()),
                    )
                })
                .collect();
            let values = graph.lookup_term_dag(&terms, &roots).unwrap();
            assert_eq!(values[0].1, values[1].1);
            assert_eq!(graph.print_size(None).unwrap().to_string(), before);
        }
    }

    #[test]
    fn proof_feature_automatically_checks_returned_extraction_certificates() {
        let mut graph = new_experimental_egraph_with_proofs();
        let commands = graph
            .parse_program(None, "(datatype T (A) (B)) (B) (extract (A))")
            .unwrap();
        let expected = graph.clone().run_program(commands.clone()).unwrap();
        let checked = run_program_with_extract_checks(&mut graph, commands, &[]).unwrap();
        assert_eq!(
            checked.outputs.len(),
            expected.len(),
            "validation must preserve source outputs"
        );
        assert!(
            !checked
                .outputs
                .iter()
                .any(|output| matches!(output, CommandOutput::ProveExtract { .. }))
        );
        assert_eq!(
            checked
                .outputs
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            expected.iter().map(ToString::to_string).collect::<Vec<_>>()
        );
        let root = graph.parser.get_expr_from_string(None, "(A)").unwrap();
        let root = capture_source_value(&mut graph, &root).unwrap();
        let mut incorrect = checked.outputs;
        for output in &mut incorrect {
            if let CommandOutput::ExtractBest(dag, _, term) = output {
                *term = dag.app("B".into(), vec![]);
            }
        }
        assert!(
            validate_extract_proofs(&mut graph, &root, &incorrect, None).is_err(),
            "a generated certificate must reject a wrong-class returned term"
        );
    }

    #[test]
    fn stateful_variant_count_runs_once_before_membership_is_captured() {
        let mut graph = new_experimental_egraph();
        graph
            .parse_and_run_program(None, "(datatype T (A) (B)) (A) (B)")
            .unwrap();
        let a = graph.parser.get_expr_from_string(None, "(A)").unwrap();
        let (_, a) = graph.eval_expr(&a).unwrap();
        let b = graph.parser.get_expr_from_string(None, "(B)").unwrap();
        let (_, b) = graph.eval_expr(&b).unwrap();
        let calls = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        #[derive(Clone)]
        struct CountAndUnion {
            calls: std::sync::Arc<std::sync::atomic::AtomicUsize>,
            a: Value,
            b: Value,
        }
        impl Primitive for CountAndUnion {
            fn name(&self) -> &str {
                "count-and-union"
            }
            fn get_type_constraints(
                &self,
                span: &egglog::ast::Span,
            ) -> Box<dyn egglog::constraint::TypeConstraint> {
                egglog::constraint::SimpleTypeConstraint::new(
                    self.name(),
                    vec![egglog::sort::I64Sort.to_arcsort()],
                    span.clone(),
                )
                .into_box()
            }
        }
        impl FullPrim for CountAndUnion {
            fn apply<'a, 'db>(
                &self,
                mut state: FullState<'a, 'db>,
                _args: &[Value],
            ) -> Option<Value> {
                self.calls.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                state.union(self.a, self.b).ok()?;
                Some(state.base_to_value(2_i64))
            }
        }
        graph.add_full_primitive(
            CountAndUnion {
                calls: calls.clone(),
                a,
                b,
            },
            None,
        );
        let commands = graph
            .parse_program(None, "(extract (A) (count-and-union))")
            .unwrap();
        let checked = run_program_with_extract_checks(&mut graph, commands, &[]).unwrap();
        assert_eq!(
            calls.load(std::sync::atomic::Ordering::SeqCst),
            2,
            "one normal count evaluation per actual and validation run"
        );
        assert!(
            matches!(&checked.outputs[0], CommandOutput::ExtractVariants(_, terms) if terms.len() == 2)
        );
    }

    #[test]
    fn zero_argument_function_root_is_captured_before_a_stateful_count() {
        let mut graph = new_experimental_egraph();
        graph
            .parse_and_run_program(
                None,
                "(datatype T (A) (B)) (function current () T :merge new) (set (current) (A)) (B)",
            )
            .unwrap();
        let expr = graph.parser.get_expr_from_string(None, "(B)").unwrap();
        let (_, b) = graph.eval_expr(&expr).unwrap();
        let calls = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        #[derive(Clone)]
        struct ReplaceCurrent {
            value: Value,
            calls: std::sync::Arc<std::sync::atomic::AtomicUsize>,
        }
        impl Primitive for ReplaceCurrent {
            fn name(&self) -> &str {
                "replace-current"
            }
            fn get_type_constraints(
                &self,
                span: &egglog::ast::Span,
            ) -> Box<dyn egglog::constraint::TypeConstraint> {
                egglog::constraint::SimpleTypeConstraint::new(
                    self.name(),
                    vec![egglog::sort::I64Sort.to_arcsort()],
                    span.clone(),
                )
                .into_box()
            }
        }
        impl FullPrim for ReplaceCurrent {
            fn apply<'a, 'db>(
                &self,
                mut state: FullState<'a, 'db>,
                _args: &[Value],
            ) -> Option<Value> {
                self.calls.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                state.set("current", &[] as &[Value], self.value).ok()?;
                Some(state.base_to_value(0_i64))
            }
        }
        graph.add_full_primitive(
            ReplaceCurrent {
                value: b,
                calls: calls.clone(),
            },
            None,
        );
        let commands = graph
            .parse_program(None, "(extract (current) (replace-current))")
            .unwrap();
        let checked = run_program_with_extract_checks(&mut graph, commands, &[]).unwrap();
        assert_eq!(calls.load(std::sync::atomic::Ordering::SeqCst), 2);
        assert!(
            matches!(&checked.outputs[0], CommandOutput::ExtractBest(dag, _, term) if dag.to_string(*term) == "(A)")
        );
    }
}
