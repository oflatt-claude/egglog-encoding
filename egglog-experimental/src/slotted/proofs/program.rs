//! Resolved source programs and their proof-checking contexts.

use super::checker::check_term_sort;
use super::format::SlottedProofStore;
use super::source::{ColumnKind, Constructor, SlottedProgram, SourceError, SourceRule, Union};
use super::terms::{FreshSlots, slot_of};
use crate::slotted::slots::Slots;
use egglog::ast::{Expr, FunctionSubtype, GenericAction, ResolvedNCommand};
use egglog::{TermDag, TermId};
use std::collections::BTreeMap;

/// An original slotted program after type resolution and rewrite desugaring.
/// Commands retain nested terms and original guards. Popped commands are absent.
/// This program is independent of any proof's term arena and slot IDs.
#[derive(Clone, Debug, Default)]
pub struct ResolvedSlottedProgram {
    /// Typechecked source declarations, top-level actions, and rewrite rules.
    pub commands: Vec<ResolvedNCommand>,
    /// Binder argument indices for each constructor that binds names.
    /// Indices count all arguments, including payloads.
    pub binders: BTreeMap<String, Vec<usize>>,
}

impl ResolvedSlottedProgram {
    pub(super) fn for_proof(
        &self,
        store: &mut SlottedProofStore,
    ) -> Result<SlottedProgram, SourceError> {
        let mut names = BTreeMap::new();
        for (&id, name) in &store.slot_names {
            let name = Slots::default().intern(name).map_err(SourceError)?;
            if names.insert(name.clone(), id).is_some() {
                return Err(SourceError(format!("ambiguous proof slot name {name}")));
            }
        }
        self.context(&mut store.term_dag, names)
    }

    pub(super) fn context(
        &self,
        dag: &mut TermDag,
        names: BTreeMap<String, i64>,
    ) -> Result<SlottedProgram, SourceError> {
        let mut fresh = FreshSlots::new(
            (0..dag.size())
                .filter_map(|t| slot_of(dag, t))
                .chain(names.values().copied()),
        );
        let mut program = SlottedProgram {
            slot_names: names,
            ..Default::default()
        };
        for command in &self.commands {
            match command {
                ResolvedNCommand::Sort { name, .. } => {
                    program.sorts.insert(name.clone());
                }
                ResolvedNCommand::Function(decl)
                    if decl.subtype == FunctionSubtype::Constructor =>
                {
                    let sort = decl.schema.output().to_owned();
                    let binders = self
                        .binders
                        .get(&decl.name)
                        .map(Vec::as_slice)
                        .unwrap_or_default();
                    let columns = decl
                        .schema
                        .input
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| {
                            if binders.contains(&i) {
                                ColumnKind::Binder
                            } else if ty == "Var" {
                                ColumnKind::Var
                            } else if ty == &sort {
                                ColumnKind::Child
                            } else {
                                ColumnKind::Payload(ty.clone())
                            }
                        })
                        .collect();
                    program.constructors.insert(
                        decl.name.clone(),
                        Constructor {
                            name: decl.name.clone(),
                            sort,
                            columns,
                        },
                    );
                }
                ResolvedNCommand::CoreAction(GenericAction::Let(_, name, expr)) => {
                    let term = ground(
                        &mut program,
                        dag,
                        &mut fresh,
                        &expr.clone().make_unresolved(),
                    )?;
                    program.lets.insert(name.name.clone(), term);
                }
                ResolvedNCommand::CoreAction(GenericAction::Union(_, lhs, rhs)) => {
                    let lhs = ground(
                        &mut program,
                        dag,
                        &mut fresh,
                        &lhs.clone().make_unresolved(),
                    )?;
                    let rhs = ground(
                        &mut program,
                        dag,
                        &mut fresh,
                        &rhs.clone().make_unresolved(),
                    )?;
                    program.unions.push(Union { lhs, rhs });
                }
                ResolvedNCommand::NormRule { rule } => {
                    let rule = SourceRule::capture(rule.clone(), &program.lets);
                    if program
                        .rewrites
                        .insert(rule.rule.name.clone(), rule)
                        .is_some()
                    {
                        return Err(SourceError("duplicate source rule name".into()));
                    }
                }
                _ => return Err(SourceError("unsupported resolved slotted command".into())),
            }
        }
        Ok(program)
    }
}

pub(super) fn ground(
    program: &mut SlottedProgram,
    dag: &mut TermDag,
    fresh: &mut FreshSlots,
    expr: &Expr,
) -> Result<TermId, SourceError> {
    for name in expr.vars().filter(|name| name.starts_with('$')) {
        let name = Slots::default().intern(&name).map_err(SourceError)?;
        if !program.slot_names.contains_key(&name) {
            let numeric = name[1..]
                .parse::<i64>()
                .ok()
                .filter(|id| !program.slot_names.values().any(|other| other == id));
            let id = numeric.unwrap_or_else(|| fresh.fresh());
            fresh.reserve([id]);
            program.slot_names.insert(name, id);
        }
    }
    let term = program.ground_term(dag, expr)?;
    check_term_sort(program, dag, term, None).map_err(SourceError)?;
    Ok(term)
}

#[cfg(test)]
#[path = "tests/program.rs"]
mod tests;
