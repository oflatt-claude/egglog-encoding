//! Constructor injectivity, lowered to ordinary rules before term/proof encoding.

use std::{collections::HashSet, sync::Arc};

use egglog::{
    CommandMacro, EGraph, Error, TypeError, TypeInfo,
    ast::{
        Action, Actions, Command, Expr, Fact, ParseError, Rule, RuleEvalMode, Span, Subdatatypes,
    },
    span,
    util::{FreshGen, SymbolGen},
};

pub(crate) fn add_injectivity_support(egraph: &mut EGraph) {
    // Install once, outside user push/pop scopes, even if no constructor is marked.
    egraph
        .run_program(vec![Command::AddRuleset(span!(), "injectivity".into())])
        .unwrap();
    egraph
        .command_macros_mut()
        .register(Arc::new(LowerInjectivity));
}

struct LowerInjectivity;

impl CommandMacro for LowerInjectivity {
    fn transform(
        &self,
        mut command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        // Datatype sorts are not in TypeInfo until this command has been lowered.
        let mut eq_sorts = HashSet::new();
        let mut containers = HashSet::new();
        match &command {
            Command::Datatype { name, .. } => {
                eq_sorts.insert(name.clone());
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, name, datatype) in datatypes {
                    match datatype {
                        Subdatatypes::Variants(_) => {
                            eq_sorts.insert(name.clone());
                        }
                        Subdatatypes::NewSort(..) => {
                            containers.insert(name.clone());
                        }
                    }
                }
            }
            _ => {}
        }

        let mut rules = Vec::new();
        match &mut command {
            Command::Constructor {
                span,
                name,
                schema,
                injective,
                ..
            } if *injective => {
                rules.extend(injectivity_rules(
                    span,
                    name,
                    &schema.input,
                    symbols,
                    types,
                    &eq_sorts,
                    &containers,
                )?);
                *injective = false;
            }
            Command::Datatype { variants, .. } => {
                for variant in variants.iter_mut().filter(|v| v.injective) {
                    rules.extend(injectivity_rules(
                        &variant.span,
                        &variant.name,
                        &variant.types,
                        symbols,
                        types,
                        &eq_sorts,
                        &containers,
                    )?);
                    variant.injective = false;
                }
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, _, datatype) in datatypes {
                    if let Subdatatypes::Variants(variants) = datatype {
                        for variant in variants.iter_mut().filter(|v| v.injective) {
                            rules.extend(injectivity_rules(
                                &variant.span,
                                &variant.name,
                                &variant.types,
                                symbols,
                                types,
                                &eq_sorts,
                                &containers,
                            )?);
                            variant.injective = false;
                        }
                    }
                }
            }
            _ => {}
        }
        // Validate every marked signature before installing the declaration.
        let mut commands = vec![command];
        commands.extend(rules);
        Ok(commands)
    }
}

fn injectivity_rules(
    span: &Span,
    name: &str,
    inputs: &[String],
    symbols: &mut SymbolGen,
    types: &TypeInfo,
    eq_sorts: &HashSet<String>,
    containers: &HashSet<String>,
) -> Result<Vec<Command>, Error> {
    let mut left = Vec::new();
    let mut right = Vec::new();
    let mut unions = Vec::new();
    let mut primitive_args = Vec::new();
    for (index, sort_name) in inputs.iter().enumerate() {
        let is_eq = if eq_sorts.contains(sort_name) {
            true
        } else if containers.contains(sort_name) {
            return Err(ParseError(
                span.clone(),
                format!(":injective constructor `{name}` does not support container argument {index} of sort `{sort_name}`"),
            ).into());
        } else {
            let sort = types
                .get_sort_by_name(sort_name)
                .ok_or_else(|| TypeError::UndefinedSort(sort_name.clone(), span.clone()))?;
            if sort.is_container_sort() {
                return Err(ParseError(
                    span.clone(),
                    format!(":injective constructor `{name}` does not support container argument {index} of sort `{sort_name}`"),
                ).into());
            }
            if sort.is_eq_sort() && !types.is_sort_unionable(sort) {
                return Err(TypeError::NonUnionableSort(sort.clone(), span.clone()).into());
            }
            sort.is_eq_sort()
        };
        let lhs = Expr::Var(span.clone(), symbols.fresh("injectivity-left"));
        let rhs = Expr::Var(span.clone(), symbols.fresh("injectivity-right"));
        if is_eq {
            unions.push(Action::Union(span.clone(), lhs.clone(), rhs.clone()));
        } else {
            primitive_args.push((index, lhs.clone(), rhs.clone()));
        }
        left.push(lhs);
        right.push(rhs);
    }
    let body = vec![Fact::Eq(
        span.clone(),
        Expr::Call(span.clone(), name.into(), left),
        Expr::Call(span.clone(), name.into(), right),
    )];
    let mut heads = Vec::new();
    if !unions.is_empty() {
        heads.push((body.clone(), unions));
    }
    for (index, lhs, rhs) in primitive_args {
        let mut guarded_body = body.clone();
        guarded_body.push(Fact::Fact(Expr::Call(
            span.clone(),
            "!=".into(),
            vec![lhs, rhs],
        )));
        heads.push((guarded_body, vec![Action::Panic(
            span.clone(),
            format!("injectivity violation in constructor `{name}`: unequal primitive argument {index}"),
        )]));
    }
    Ok(heads
        .into_iter()
        .map(|(body, head)| Command::Rule {
            rule: Rule {
                span: span.clone(),
                // Proof history retains rules after pop, so redeclarations need fresh names.
                name: symbols.fresh(&format!("injectivity-{name}")),
                ruleset: "injectivity".into(),
                body,
                head: Actions::new(head),
                eval_mode: RuleEvalMode::Seminaive,
                no_decomp: false,
                include_subsumed: true,
            },
        })
        .collect())
}
