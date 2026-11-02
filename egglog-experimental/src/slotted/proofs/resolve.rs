//! Parse and typecheck original slotted source before proof checking.

use super::checker::check_term_sort;
use super::guards::{GUARDS, GuardSignature};
use super::program::{ResolvedSlottedProgram, ground};
use super::source::{ColumnKind, SlottedProgram, SourceError};
use super::terms::FreshSlots;
use crate::slotted::frontend::{
    declarations, expand_includes, name_rewrite, source_constructor, source_rewrite,
};
use crate::slotted::syntax::{self, Form};
use crate::slotted::var_sort::VarSort;
use egglog::ast::{
    Action, Expr, Fact, FunctionDecl, GenericAction, GenericActions, ResolvedExpr, ResolvedFact,
    ResolvedNCommand, ResolvedRule, ResolvedVar, Rule, Schema, Sexp, Span,
};
use egglog::prelude::BaseSort;
use egglog::sort::{EqSort, UnitSort};
use egglog::util::{FreshGen, INTERNAL_SYMBOL_PREFIX, IndexMap, SymbolGen};
use egglog::{Context, EGraph, ResolvedCall, TermDag};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

impl SlottedProgram {
    fn source_types(&self, span: &Span) -> Result<EGraph, SourceError> {
        let err = |e: &dyn Display| SourceError(e.to_string());
        let mut graph = EGraph::default();
        egglog::prelude::add_base_sort(&mut graph, VarSort, span.clone()).map_err(|e| err(&e))?;
        let mut symbols = SymbolGen::new(format!("{INTERNAL_SYMBOL_PREFIX}slotted-types-"));
        for name in &self.sorts {
            graph
                .add_sort(EqSort { name: name.clone() }, span.clone())
                .map_err(|e| err(&e))?;
        }
        for op in self.constructors.values() {
            let decl = FunctionDecl::constructor(
                span.clone(),
                op.name.clone(),
                Schema {
                    input: op.input_sorts().map(str::to_owned).collect(),
                    outputs: vec![op.sort.clone()],
                },
                None,
                false,
                false,
            );
            graph
                .type_info()
                .typecheck_function(&mut symbols, &decl)
                .map_err(|e| err(&e))?;
        }

        Ok(graph)
    }

    fn resolve_action(
        &self,
        dag: &TermDag,
        span: &Span,
        action: Action,
    ) -> Result<GenericAction<ResolvedCall, ResolvedVar>, SourceError> {
        let mut graph = self.source_types(span)?;
        let mut names = BTreeSet::new();
        let action = action.visit_exprs(&mut |expr| {
            names.extend(expr.vars().filter(|name| name.starts_with('$')));
            expr
        });
        let mut bindings: IndexMap<_, _> = names
            .iter()
            .map(|name| (name.as_str(), (span.clone(), VarSort.to_arcsort())))
            .collect();
        for (name, &term) in &self.lets {
            let sort = self
                .sort_of(dag, term)
                .ok_or_else(|| SourceError(format!("unknown sort for global {name}")))?;
            bindings.insert(
                name.as_str(),
                (span.clone(), graph.get_sort_by_name(&sort).unwrap().clone()),
            );
        }
        let mut symbols = SymbolGen::new(format!("{INTERNAL_SYMBOL_PREFIX}slotted-actions-"));
        let resolved = graph
            .type_info()
            .typecheck_standalone_actions(
                &mut symbols,
                &GenericActions(vec![action]),
                &bindings,
                Context::Full,
            )
            .map_err(|e| SourceError(e.to_string()))?;
        let [action] = resolved.0.as_slice() else {
            unreachable!("one source action retains its syntax")
        };
        Ok(action.clone().visit_exprs(&mut |expr| match expr {
            ResolvedExpr::Var(span, mut var) if self.lets.contains_key(&var.name) => {
                var.is_global_ref = true;
                ResolvedExpr::Var(span, var)
            }
            other => other,
        }))
    }

    pub(super) fn resolve_rewrite(
        &self,
        dag: &TermDag,
        source: &egglog::ast::Rewrite,
    ) -> Result<ResolvedRule, SourceError> {
        let err = |e: &dyn Display| SourceError(e.to_string());
        let mut graph = self.source_types(&source.span)?;
        for name in GUARDS {
            if name != "!=" {
                graph.add_pure_primitive(GuardSignature(name), None);
            }
        }
        let source_terms: Vec<_> = std::iter::once(&source.lhs)
            .chain(std::iter::once(&source.rhs))
            .chain(source.conditions.iter().flat_map(|fact| match fact {
                Fact::Eq(_, a, b) => vec![a, b],
                Fact::Fact(Expr::Call(_, head, args)) if is_guard(head) => args.iter().collect(),
                Fact::Fact(expr) => vec![expr],
            }))
            .collect();
        let source_names: BTreeSet<_> = source_terms
            .iter()
            .flat_map(|expr| expr.vars())
            .chain(self.lets.keys().cloned())
            .collect();
        let mut prefix = format!("{INTERNAL_SYMBOL_PREFIX}slotted-resolve-");
        while source_names.iter().any(|name| name.starts_with(&prefix)) {
            prefix.push('-');
        }
        let mut symbols = SymbolGen::new(prefix);
        // Captured carrier globals and local payload variables have distinct scopes.
        let mut payload_vars = BTreeSet::new();
        for expr in &source_terms {
            expr.fold(&mut |expr, _: Vec<()>| {
                if let Expr::Call(_, head, args) = expr
                    && let Some(op) = self.constructors.get(head)
                {
                    for (arg, column) in args.iter().zip(&op.columns) {
                        if matches!(column, ColumnKind::Payload(_)) {
                            payload_vars.extend(arg.vars());
                        }
                    }
                }
            });
        }
        let aliases: BTreeMap<_, _> = self
            .lets
            .keys()
            .map(|name| {
                let alias = if payload_vars.contains(name) {
                    symbols.fresh(format!("captured-{name}").as_str())
                } else {
                    name.clone()
                };
                (name.clone(), alias)
            })
            .collect();
        let globals: IndexMap<_, _> = self
            .lets
            .iter()
            .map(|(name, &term)| (aliases[name].clone(), term))
            .collect();
        fn capture(
            program: &SlottedProgram,
            expr: &Expr,
            payload: bool,
            aliases: &BTreeMap<String, String>,
        ) -> Expr {
            match expr {
                Expr::Var(span, name) if !payload && aliases.contains_key(name) => {
                    Expr::Var(span.clone(), aliases[name].clone())
                }
                Expr::Call(span, head, args) => Expr::Call(
                    span.clone(),
                    head.clone(),
                    args.iter()
                        .enumerate()
                        .map(|(i, arg)| {
                            let payload = program.constructors.get(head).is_some_and(|op| {
                                matches!(op.columns.get(i), Some(ColumnKind::Payload(_)))
                            });
                            capture(program, arg, payload, aliases)
                        })
                        .collect(),
                ),
                _ => expr.clone(),
            }
        }
        let lhs = capture(self, &source.lhs, false, &aliases);
        let rhs = capture(self, &source.rhs, false, &aliases);
        let mut body = vec![Fact::Fact(lhs.clone())];
        body.extend(source.conditions.iter().map(|fact| {
            match fact {
                Fact::Eq(span, a, b) => Fact::Eq(
                    span.clone(),
                    capture(self, a, false, &aliases),
                    capture(self, b, false, &aliases),
                ),
                Fact::Fact(Expr::Call(span, head, args)) if is_guard(head) => {
                    Fact::Fact(Expr::Call(
                        span.clone(),
                        head.clone(),
                        args.iter()
                            .map(|arg| capture(self, arg, false, &aliases))
                            .collect(),
                    ))
                }
                Fact::Fact(expr) => Fact::Fact(capture(self, expr, false, &aliases)),
            }
        }));
        let mut rule = Rule {
            span: source.span.clone(),
            head: GenericActions(vec![GenericAction::Union(source.span.clone(), lhs, rhs)]),
            body,
            name: source.name.clone(),
            ruleset: String::new(),
            eval_mode: Default::default(),
            no_decomp: false,
            include_subsumed: false,
        };
        // Slot literals have the rigid Var sort. Captured globals retain the
        // sort of their source term; constructor signatures infer all other locals.
        let var_ty = VarSort.to_arcsort();
        let mut bindings: IndexMap<_, _> = source_terms
            .iter()
            .flat_map(|expr| expr.vars())
            .filter(|name| name.starts_with('$') && !payload_vars.contains(name))
            .map(|name| (name, (source.span.clone(), var_ty.clone())))
            .collect();
        for (name, &term) in &globals {
            let sort = self
                .sort_of(dag, term)
                .ok_or_else(|| SourceError(format!("unknown sort for global {name}")))?;
            let ty = graph
                .get_sort_by_name(&sort)
                .ok_or_else(|| SourceError(format!("unknown sort {sort}")))?
                .clone();
            bindings.insert(name.clone(), (source.span.clone(), ty));
        }
        let expression_sort = |expr: &Expr| match expr {
            Expr::Call(_, head, _) => self.constructors.get(head).map(|c| c.sort.clone()),
            Expr::Var(_, name) if name.starts_with('$') => Some("Var".into()),
            Expr::Var(_, name) => globals.get(name).and_then(|&t| self.sort_of(dag, t)),
            Expr::Lit(_, lit) => Some(egglog::sort::literal_sort(lit).name().to_owned()),
        };
        // Infer plain facts in their source context: guards return Unit, while
        // constructor patterns return the carrier. Remove these type constraints
        // after resolution; the checker sees the original facts.
        let plain_facts: Vec<_> = rule
            .body
            .iter_mut()
            .enumerate()
            .map(|(i, fact)| {
                let Fact::Fact(expr) = fact else { return false };
                let guard = i > 0 && matches!(expr, Expr::Call(_, head, _) if is_guard(head));
                let name = symbols.fresh("source-fact");
                let sort = if guard {
                    Some(UnitSort.to_arcsort())
                } else {
                    expression_sort(expr).map(|sort| {
                        graph
                            .get_sort_by_name(&sort)
                            .expect("source sort is registered")
                            .clone()
                    })
                };
                if let Some(sort) = sort {
                    bindings.insert(name.clone(), (expr.span(), sort));
                }
                *fact = Fact::Eq(expr.span(), Expr::Var(expr.span(), name), expr.clone());
                true
            })
            .collect();
        let bindings = bindings
            .iter()
            .map(|(name, value)| (name.as_str(), value.clone()))
            .collect();
        let mut rule = graph
            .type_info()
            .typecheck_rule_with_bindings(&mut symbols, &rule, false, &bindings)
            .map_err(|e| err(&e))?;
        for (fact, plain) in rule.body.iter_mut().zip(plain_facts) {
            if plain {
                let ResolvedFact::Eq(_, _, expr) = fact else {
                    unreachable!("resolved fact retains its syntax")
                };
                *fact = ResolvedFact::Fact(expr.clone());
            }
        }
        for fact in &rule.body {
            if let ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(head), args)) =
                fact
            {
                let head = head.name();
                if !is_guard(head) {
                    return Err(SourceError(format!("unsupported source guard {head}")));
                }
                let valid = match head {
                    "!=" | "renaming-=" | "renaming-!=" => args.len() == 2,
                    "free" | "not-free" => args.len() >= 2,
                    "free-names-are" => !args.is_empty(),
                    _ => true,
                };
                if !valid {
                    return Err(SourceError(format!("wrong arity for {head}")));
                }
            }
        }
        let originals: BTreeMap<_, _> = aliases
            .into_iter()
            .map(|(name, alias)| (alias, name))
            .collect();
        Ok(rule.visit_exprs(&mut |expr| match expr {
            ResolvedExpr::Var(span, mut var) if originals.contains_key(&var.name) => {
                var.name = originals[&var.name].clone();
                var.is_global_ref = true;
                ResolvedExpr::Var(span, var)
            }
            other => other,
        }))
    }
}

fn is_guard(name: &str) -> bool {
    GUARDS.contains(&name)
}

/// Resolve the original slotted source visible at a proof query.
/// Rewrites become typed rules with their original conditions and nested terms.
/// Includes resolve from the working directory; push/pop determines the visible scope.
pub fn resolve_program<'a>(
    source: impl IntoIterator<Item = &'a Sexp>,
) -> Result<ResolvedSlottedProgram, SourceError> {
    let forms = source
        .into_iter()
        .map(|s| (syntax::convert(s), s.span()))
        .collect();
    let forms =
        expand_includes(forms, &mut BTreeSet::new()).map_err(|e| SourceError(e.to_string()))?;
    let mut reader = Reader {
        program: SlottedProgram::default(),
        resolved: ResolvedSlottedProgram::default(),
        fresh: FreshSlots::new([]),
        rules: 0,
        rule_names: BTreeSet::new(),
    };
    let mut dag = TermDag::default();
    let mut scopes = Vec::new();
    let mut start = 0;
    for (i, (form, _)) in forms.iter().enumerate() {
        if let Ok((head @ ("push" | "pop"), args)) = form.call() {
            reader.region(&mut dag, &forms[start..i])?;
            if !args.is_empty() {
                return Err(SourceError(format!("slotted {head} takes no arguments")));
            }
            if head == "push" {
                scopes.push((reader.program.clone(), reader.resolved.clone()));
            } else {
                (reader.program, reader.resolved) = scopes
                    .pop()
                    .ok_or_else(|| SourceError("pop without a corresponding push".into()))?;
            }
            start = i + 1;
        }
    }
    reader.region(&mut dag, &forms[start..])?;
    Ok(reader.resolved)
}

struct Reader {
    program: SlottedProgram,
    resolved: ResolvedSlottedProgram,
    fresh: FreshSlots,
    rules: usize,
    rule_names: BTreeSet<String>,
}

impl Reader {
    fn region(&mut self, dag: &mut TermDag, forms: &[(Form, Span)]) -> Result<(), SourceError> {
        let mut sorts = Vec::new();
        let mut constructors = Vec::new();
        for (form, _) in forms {
            declarations(form, &mut sorts, &mut constructors).map_err(SourceError)?;
        }
        let span = forms
            .first()
            .map(|(_, s)| s.clone())
            .unwrap_or_else(|| egglog::span!());
        for sort in sorts {
            if ["Var", "i64", "String", "Unit"].contains(&sort.as_str())
                || !self.program.sorts.insert(sort.clone())
            {
                return Err(SourceError(format!(
                    "invalid or duplicate equality sort {sort}"
                )));
            }
            self.resolved.commands.push(ResolvedNCommand::Sort {
                span: span.clone(),
                name: sort,
                presort_and_args: None,
                uf: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
            });
        }
        for form in constructors {
            let op = source_constructor(
                &form,
                self.program.sorts.iter().map(String::as_str),
                self.program.constructors.values(),
            )
            .map_err(SourceError)?;
            let decl = FunctionDecl::constructor(
                span.clone(),
                op.name.clone(),
                Schema::new(
                    op.input_sorts().map(str::to_owned).collect(),
                    op.sort.clone(),
                ),
                None,
                false,
                false,
            );
            let mut graph = self.program.source_types(&span)?;
            let mut symbols =
                SymbolGen::new(format!("{INTERNAL_SYMBOL_PREFIX}slotted-declarations-"));
            let decl = graph
                .type_info()
                .typecheck_function(&mut symbols, &decl)
                .map_err(|e| SourceError(e.to_string()))?;
            let binders: Vec<_> = op
                .columns
                .iter()
                .enumerate()
                .filter_map(|(i, column)| (*column == ColumnKind::Binder).then_some(i))
                .collect();
            if !binders.is_empty() {
                self.resolved.binders.insert(op.name.clone(), binders);
            }
            self.resolved
                .commands
                .push(ResolvedNCommand::Function(decl));
            self.program.constructors.insert(op.name.clone(), op);
        }
        for (form, span) in forms {
            let (head, args) = form.call().map_err(SourceError)?;
            let command = match (head, args) {
                ("sort" | "constructor" | "datatype" | "datatype*", _) => continue,
                ("let", [name, value]) => {
                    let name = name.symbol().map_err(SourceError)?;
                    if name.starts_with('$') || self.program.lets.contains_key(name) {
                        return Err(SourceError(format!("invalid or duplicate global {name}")));
                    }
                    let value = value.expr().map_err(SourceError)?;
                    let term = ground(&mut self.program, dag, &mut self.fresh, &value)?;
                    let action = self.program.resolve_action(
                        dag,
                        span,
                        Action::Let(span.clone(), name.into(), value),
                    )?;
                    self.program.lets.insert(name.into(), term);
                    ResolvedNCommand::CoreAction(action)
                }
                ("union", [lhs, rhs]) => {
                    let lhs = lhs.expr().map_err(SourceError)?;
                    let rhs = rhs.expr().map_err(SourceError)?;
                    let a = ground(&mut self.program, dag, &mut self.fresh, &lhs)?;
                    let b = ground(&mut self.program, dag, &mut self.fresh, &rhs)?;
                    let sort = check_term_sort(&self.program, dag, a, None).map_err(SourceError)?;
                    check_term_sort(&self.program, dag, b, Some(&sort)).map_err(SourceError)?;
                    if !self.program.sorts.contains(&sort) {
                        return Err(SourceError(
                            "union requires terms in an equality sort".into(),
                        ));
                    }
                    ResolvedNCommand::CoreAction(self.program.resolve_action(
                        dag,
                        span,
                        Action::Union(span.clone(), lhs, rhs),
                    )?)
                }
                ("rewrite", _) => {
                    let mut rule = source_rewrite(args).map_err(SourceError)?;
                    name_rewrite(&mut rule, self.rules, Some(&mut self.rule_names));
                    self.rules += 1;
                    ResolvedNCommand::NormRule {
                        rule: self.program.resolve_rewrite(dag, &rule)?,
                    }
                }
                (
                    "run" | "check" | "fail" | "extract" | "print-size" | "print-function"
                    | "print-stats" | "slotted-export" | "set-option",
                    _,
                ) => continue,
                _ => return Err(SourceError(format!("unsupported source command {head}"))),
            };
            self.resolved.commands.push(command);
        }
        Ok(())
    }
}
