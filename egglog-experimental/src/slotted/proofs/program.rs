//! Resolve an original slotted program into the checker's scoped axioms.

use super::checker::check_term_sort;
use super::format::SlottedProofStore;
use super::source::{SlottedProgram, SourceError};
use super::terms::{FreshSlots, slot_of};
use crate::slotted::frontend::{
    declarations, expand_includes, name_rewrite, source_constructor, source_rewrite,
};
use crate::slotted::slots::Slots;
use crate::slotted::syntax::{self, Form};
use egglog::ast::{Sexp, Span};
use egglog::{TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn for_proof<'a>(
    source: impl IntoIterator<Item = &'a Sexp>,
    store: &mut SlottedProofStore,
) -> Result<SlottedProgram, SourceError> {
    let mut names = BTreeMap::new();
    for (&id, name) in &store.slot_names {
        let name = Slots::default().intern(name).map_err(SourceError)?;
        if names.insert(name.clone(), id).is_some() {
            return Err(SourceError(format!("ambiguous proof slot name {name}")));
        }
    }
    resolve(source, &mut store.term_dag, names)
}

pub(super) fn resolve<'a>(
    source: impl IntoIterator<Item = &'a Sexp>,
    dag: &mut TermDag,
    names: BTreeMap<String, i64>,
) -> Result<SlottedProgram, SourceError> {
    let forms = source
        .into_iter()
        .map(|source| (syntax::convert(source), source.span()))
        .collect();
    let forms =
        expand_includes(forms, &mut BTreeSet::new()).map_err(|e| SourceError(e.to_string()))?;
    let used = (0..dag.size())
        .filter_map(|t| slot_of(dag, t))
        .chain(names.values().copied());
    let fresh = FreshSlots::new(used);
    let mut reader = Reader {
        program: SlottedProgram {
            slot_names: names,
            ..Default::default()
        },
        fresh,
        rules: 0,
        rule_names: BTreeSet::new(),
    };
    let mut scopes = Vec::new();
    let mut start = 0;
    for (i, (form, _)) in forms.iter().enumerate() {
        if let Ok((head @ ("push" | "pop"), args)) = form.call() {
            reader.region(dag, &forms[start..i])?;
            if !args.is_empty() {
                return Err(SourceError(format!("slotted {head} takes no arguments")));
            }
            if head == "push" {
                scopes.push(reader.program.clone());
            } else {
                reader.program = scopes
                    .pop()
                    .ok_or_else(|| SourceError("pop without a corresponding push".into()))?;
            }
            start = i + 1;
        }
    }
    reader.region(dag, &forms[start..])?;
    Ok(reader.program)
}

struct Reader {
    program: SlottedProgram,
    fresh: FreshSlots,
    // Names remain unique even when a declaration is popped.
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
        for sort in sorts {
            if ["Var", "i64", "String", "Unit"].contains(&sort.as_str())
                || !self.program.sorts.insert(sort.clone())
            {
                return Err(SourceError(format!(
                    "invalid or duplicate equality sort {sort}"
                )));
            }
        }
        for form in constructors {
            let op = source_constructor(
                &form,
                self.program.sorts.iter().map(String::as_str),
                self.program.constructors.values(),
            )
            .map_err(SourceError)?;
            self.program.constructors.insert(op.name.clone(), op);
        }
        for (form, _) in forms {
            let (head, args) = form.call().map_err(SourceError)?;
            match (head, args) {
                ("sort" | "constructor" | "datatype" | "datatype*", _) => {}
                ("let", [name, value]) => {
                    let name = name.symbol().map_err(SourceError)?;
                    if name.starts_with('$') || self.program.lets.contains_key(name) {
                        return Err(SourceError(format!("invalid or duplicate global {name}")));
                    }
                    let term = self.ground(dag, value)?;
                    self.program.lets.insert(name.into(), term);
                }
                ("union", [lhs, rhs]) => {
                    let lhs = self.ground(dag, lhs)?;
                    let rhs = self.ground(dag, rhs)?;
                    let sort =
                        check_term_sort(&self.program, dag, lhs, None).map_err(SourceError)?;
                    check_term_sort(&self.program, dag, rhs, Some(&sort)).map_err(SourceError)?;
                    if !self.program.sorts.contains(&sort) {
                        return Err(SourceError(
                            "union requires terms in an equality sort".into(),
                        ));
                    }
                    self.program.unions.push(super::source::Union { lhs, rhs });
                }
                ("rewrite", _) => {
                    let mut rule = source_rewrite(args).map_err(SourceError)?;
                    name_rewrite(&mut rule, self.rules, Some(&mut self.rule_names));
                    self.rules += 1;
                    self.program.add_rewrite_ast(dag, &rule)?;
                }
                // Observations and execution schedules contribute no source axioms.
                (
                    "run" | "check" | "fail" | "extract" | "print-size" | "print-function"
                    | "print-stats" | "slotted-export" | "set-option",
                    _,
                ) => {}
                _ => return Err(SourceError(format!("unsupported source command {head}"))),
            }
        }
        Ok(())
    }

    fn ground(&mut self, dag: &mut TermDag, form: &Form) -> Result<TermId, SourceError> {
        let expr = form.expr().map_err(SourceError)?;
        for name in expr.vars().filter(|name| name.starts_with('$')) {
            let name = Slots::default().intern(&name).map_err(SourceError)?;
            if !self.program.slot_names.contains_key(&name) {
                let numeric = name[1..]
                    .parse::<i64>()
                    .ok()
                    .filter(|id| !self.program.slot_names.values().any(|other| other == id));
                let id = numeric.unwrap_or_else(|| self.fresh.fresh());
                self.fresh.reserve([id]);
                self.program.slot_names.insert(name, id);
            }
        }
        let term = self.program.ground_term(dag, &expr)?;
        check_term_sort(&self.program, dag, term, None).map_err(SourceError)?;
        Ok(term)
    }
}

#[cfg(test)]
#[path = "tests/program.rs"]
mod tests;
