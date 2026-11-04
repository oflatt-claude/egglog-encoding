//! Shared extraction correctness instrumentation for ordinary and paper fixtures.
//!
//! Every intercepted top-level source extraction checks the actual returned terms:
//! - Ordinary mode also runs the other tree/greedy-DAG extractor and checks all
//!   returned terms equal the requested root; the two cost models may choose differently.
//! - Term-encoded mode checks each returned source term equal to the source root
//!   through the encoding's normal check pipeline.
//! - Strict proof-testing checks ordered certificates for the exact returned terms
//!   and a checked connection from the requested source root to each certificate's LHS.
//!
//! Extra validation runs on pre-command clones, preserving the real workload graph.
//! The paper harness separately compares terms, variant order and costs across modes.
//! For its equal-cost best-term tie policy, this helper also checks a supplied
//! comparison term against the root; it never rewrites returned terms or certificates.
//! Extractions inside included files are not intercepted.
use egglog::{
    CommandOutput, Context, Error, ResolvedCall, TermDag, TermId, TypedTerm,
    ast::{Action, Command, Expr, Fact, FunctionSubtype, Literal},
    extract::TreeCostModelFromDag,
    span,
    util::FreshGen,
};
use egglog_experimental::*;

pub struct CheckedRun {
    pub outputs: Vec<CommandOutput>,
    /// Per intercepted extraction, equality of the supplied comparison term to
    /// this run's requested root. Term-mode alternatives must be judged by the
    /// ordinary run; strict mode may use its independently checked source proof.
    pub comparison_in_root_class: Vec<Option<bool>>,
}

/// Validate top-level source extractions on pre-command clones. Included files
/// execute inside their include command; their extractions are not intercepted.
/// Ordinary graphs also cross-check tree/greedy extractors. Encoded graphs use
/// source checks over shared terms; strict graphs use the checked proof-DAG API.
pub fn run_program_with_extract_checks(
    egraph: &mut EGraph,
    program: Vec<Command>,
    proof_testing: bool,
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
            outputs.extend(command_outputs);
            continue;
        };

        let baseline = baseline_terms
            .get(comparison_in_root_class.len())
            .copied()
            .flatten()
            .filter(|baseline| {
                command_outputs.iter().any(|output| {
                    matches!(output, CommandOutput::ExtractBest(dag, _, term) if dag.to_string(*term) != *baseline)
                })
            });
        let equivalent = if proof_testing {
            validate_extract_proofs(
                validation_egraph.as_mut().unwrap(),
                &extract,
                &command_outputs,
                baseline,
            )?
        } else if validation_egraph
            .as_ref()
            .unwrap()
            .functions_iter()
            .any(|(_, function)| function.is_view())
        {
            validate_encoded_extract_outputs(
                validation_egraph.as_mut().unwrap(),
                &extract,
                &command_outputs,
                baseline,
            )?
        } else {
            validate_extract_outputs(
                validation_egraph.as_mut().unwrap(),
                &extract,
                &command_outputs,
                baseline,
            )?
        };
        comparison_in_root_class.push(equivalent);
        outputs.extend(command_outputs);
    }

    Ok(CheckedRun {
        outputs,
        comparison_in_root_class,
    })
}

fn validate_encoded_extract_outputs(
    graph: &mut EGraph,
    extract: &ExtractCheck,
    outputs: &[CommandOutput],
    baseline: Option<&str>,
) -> Result<Option<bool>, Error> {
    let root = validation_root(graph, &extract.root)?;
    for term in extracted_exprs(outputs)? {
        let mut terms = TermDag::default();
        let id = source_term(&mut terms, &term);
        let term = bind_dag(graph, &terms, id)?;
        check_source_equality(graph, root.clone(), term)?;
    }
    if let Some(baseline) = baseline {
        let baseline = graph.parser.get_expr_from_string(None, baseline)?;
        let mut terms = TermDag::default();
        let id = source_term(&mut terms, &baseline);
        let baseline = bind_dag(graph, &terms, id)?;
        Ok(Some(check_source_equality(graph, root, baseline).is_ok()))
    } else {
        Ok(None)
    }
}

/// Bind function outputs to a query-local variable before comparing them.
/// Encoded proof normal form permits function lookups in this position, while
/// nesting a function lookup inside an equality with a global is unsupported.
fn check_source_equality(graph: &mut EGraph, left: Expr, right: Expr) -> Result<(), Error> {
    let value = Expr::Var(
        span!(),
        graph.parser.symbol_gen.fresh("extract-validation-value"),
    );
    graph.run_program(vec![Command::Check(
        span!(),
        vec![
            Fact::Eq(span!(), left, value.clone()),
            Fact::Eq(span!(), value, right),
        ],
    )])?;
    Ok(())
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

/// Materialize a shared extracted DAG on the disposable clone. Each check then
/// has a small query instead of expanding thousands of repeated subterms into
/// a deeply recursive join plan. This adds definitions, never user rewrites.
fn bind_dag(graph: &mut EGraph, dag: &TermDag, root: TermId) -> Result<Expr, Error> {
    // Contextual typing separates overloaded container terms such as vec-empty.
    // Containers stay inline: encoded global bindings cannot hold containers.
    let (dag, roots) = graph
        .typecheck_term_dag(dag, &[(root, None)], Context::Read)
        .map_err(|error| Error::ExtractError(error.to_string()))?;
    let mut bound: Vec<Option<Expr>> = vec![None; dag.size()];
    let mut commands = Vec::new();
    for (id, term) in dag.nodes() {
        let expr = match term {
            TypedTerm::Lit(literal) => Expr::Lit(span!(), literal.clone()),
            TypedTerm::Var(never) => match *never {},
            TypedTerm::App(ResolvedCall::Func(func), children) if func.role.is_global() => {
                let [key] = children.as_slice() else {
                    unreachable!("typed global key")
                };
                let TypedTerm::Lit(Literal::String(name)) = dag.get(*key) else {
                    unreachable!("typed global name")
                };
                Expr::Var(span!(), name.clone())
            }
            TypedTerm::App(call, children) => Expr::Call(
                span!(),
                call.name().to_owned(),
                children
                    .iter()
                    .map(|&id| bound[id].clone().unwrap())
                    .collect(),
            ),
        };
        bound[id] = Some(if term.sort().is_eq_sort() {
            let name = graph.parser.symbol_gen.fresh("extract-validation-node");
            commands.push(Command::Action(Action::Let(span!(), name.clone(), expr)));
            Expr::Var(span!(), name)
        } else {
            expr
        });
    }
    graph.run_program(commands)?;
    Ok(bound[roots[0]].take().unwrap())
}

/// Preserve source extraction semantics: an existing zero-argument function is
/// read only through queries, while constructor/global expressions can be bound
/// once through the source pipeline. eval_expr is a native expression API and
/// cannot execute the encoded pipeline's batched actions.
fn validation_root(graph: &mut EGraph, root: &Expr) -> Result<Expr, Error> {
    if let Expr::Call(_, name, args) = root
        && args.is_empty()
        && graph.functions_iter().any(|(candidate, function)| {
            candidate == name
                && function.subtype() == FunctionSubtype::Custom
                && !function.func_type().role.is_constructor_view()
                && !function.is_let_binding()
        })
    {
        return Ok(root.clone());
    }
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
    egraph: &mut EGraph,
    extract: &ExtractCheck,
    requested_outputs: &[CommandOutput],
    baseline: Option<&str>,
) -> Result<Option<bool>, Error> {
    // Evaluate the potentially stateful root exactly once, then invoke the
    // opposite extractor directly so both algorithms see that same value.
    let (root_sort, root_value) = egraph.eval_expr(&extract.root)?;
    let nvariants = if let Some(variants) = &extract.variants {
        let (_, value) = egraph.eval_expr(variants)?;
        usize::try_from(egraph.value_to_base::<i64>(value)).map_err(|_| {
            Error::ExtractError("extract variant count must be nonnegative".to_owned())
        })?
    } else {
        0
    };

    let requested_exprs = extracted_exprs(requested_outputs)?;
    let roots = vec![(root_sort.clone(), root_value)];
    let paired_exprs = if nvariants == 0 {
        let extracted = if extract.use_greedy_dag {
            egraph.extract_best_with_cost_model(roots, TreeCostModelFromDag(DynamicCostModel))?
        } else {
            extract_best_greedy_dag(egraph, roots, DynamicCostModel)?
        };
        let root = extracted
            .terms
            .into_iter()
            .next()
            .expect("one root was requested")
            .ok_or_else(|| Error::ExtractError("paired extractor returned no term".to_owned()))?;
        vec![extracted.termdag.term_to_expr(&root.term, span!())]
    } else {
        let extracted = if extract.use_greedy_dag {
            egraph.extract_variants_with_cost_model(
                roots,
                nvariants,
                TreeCostModelFromDag(DynamicCostModel),
            )?
        } else {
            extract_variants_greedy_dag(egraph, roots, nvariants, DynamicCostModel)?
        };
        let variants = extracted
            .variants
            .into_iter()
            .next()
            .expect("one root was requested");
        variants
            .into_iter()
            .map(|variant| extracted.termdag.term_to_expr(&variant.term, span!()))
            .collect()
    };

    if requested_exprs.is_empty() != paired_exprs.is_empty() {
        return Err(Error::ExtractError(
            "only one extractor returned variants for the requested root".to_owned(),
        ));
    }

    for extracted_expr in requested_exprs.iter().chain(&paired_exprs) {
        let mut terms = TermDag::default();
        let id = source_term(&mut terms, extracted_expr);
        let extracted = bind_dag(egraph, &terms, id)?;
        let (extracted_sort, extracted_value) = egraph.eval_expr(&extracted)?;
        if root_sort.name() != extracted_sort.name() || root_value != extracted_value {
            return Err(Error::ExtractError(format!(
                "extractor returned a term unequal to the requested root: root {:?}, extracted {extracted_expr:?}",
                extract.root
            )));
        }
    }

    if let Some(baseline) = baseline {
        let expr = egraph.parser.get_expr_from_string(None, baseline)?;
        let mut terms = TermDag::default();
        let id = source_term(&mut terms, &expr);
        let expr = bind_dag(egraph, &terms, id)?;
        let (sort, value) = egraph.eval_expr(&expr)?;
        // Reuse the root value evaluated above; never evaluate a stateful root
        // a second time merely to compare an equal-cost alternative.
        Ok(Some(sort.name() == root_sort.name() && value == root_value))
    } else {
        Ok(None)
    }
}

fn extracted_exprs(outputs: &[CommandOutput]) -> Result<Vec<Expr>, Error> {
    let mut saw_extract = false;
    let mut extracted = Vec::new();
    for output in outputs {
        match output {
            CommandOutput::ExtractBest(termdag, _cost, term) => {
                extracted.push(termdag.term_to_expr(term, span!()));
                saw_extract = true;
            }
            CommandOutput::ExtractVariants(termdag, terms) => {
                for term in terms {
                    extracted.push(termdag.term_to_expr(term, span!()));
                }
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

/// Certify the actual extraction outputs in order, with an independently checked
/// connection from the requested source root to each certificate's left endpoint.
/// All supplementary checks run on the pre-command clone, never the real graph.
fn validate_extract_proofs(
    graph: &mut EGraph,
    extract: &ExtractCheck,
    outputs: &[CommandOutput],
    baseline: Option<&str>,
) -> Result<Option<bool>, Error> {
    let terms = extracted_exprs(outputs)?;
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
    if certificates.len() != 1 {
        return Err(Error::ExtractError(
            "strict extraction must return one ordered proof bundle".into(),
        ));
    }
    let (store, ids) = certificates[0];
    if ids.len() != terms.len() {
        return Err(Error::ExtractError(
            "extraction certificate count differs from returned terms".into(),
        ));
    }
    let mut dag = store.term_dag().clone();
    let root = source_term(&mut dag, &extract.root);
    let (typed, typed_roots) = graph
        .typecheck_term_dag(&dag, &[(root, None)], Context::Read)
        .map_err(|error| Error::ExtractError(error.to_string()))?;
    let sort = typed.get(typed_roots[0]).sort();
    let baseline = baseline
        .map(|baseline| graph.parser.get_expr_from_string(None, baseline))
        .transpose()?
        .map(|expr| source_term(&mut dag, &expr));
    let mut equivalent = None;
    for (id, term) in ids.iter().zip(&terms) {
        let proof = store.get(*id);
        let rhs = store.term_dag().to_string(proof.rhs());
        if rhs != term.to_string() {
            return Err(Error::ExtractError(format!(
                "certificate proves {rhs}, extractor returned {term}"
            )));
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
