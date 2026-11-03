//! Proof normal form and primitive validators for slotted source guards.

use super::HashMap;
use super::context::{ProofContext, SourceRule, pattern_term};
use super::terms::{instantiate, slot_of};
use crate::slotted::var_sort::VarSort;
use egglog::ast::{Literal, ResolvedExpr, ResolvedFact, Span};
use egglog::prelude::BaseSort;
use egglog::sort::UnitSort;
use egglog::util::{INTERNAL_SYMBOL_PREFIX, IndexMap, SymbolGen};
use egglog::{
    EGraph, Primitive, PurePrim, PureState, ResolvedCall, TermDag, TermId, TypeInfo, Value,
};
use std::collections::BTreeSet;
use std::sync::Arc;

pub(super) const GUARDS: [&str; 6] = [
    "renaming-=",
    "!=",
    "renaming-!=",
    "free",
    "not-free",
    "free-names-are",
];

pub(super) fn validator_name(name: &str) -> &str {
    match name {
        // The built-in != compares raw terms and cannot account for binders.
        "!=" => "slotted-proof-!=",
        other => other,
    }
}

/// Normalize ordinary guard operands and bind the lifted terms at their source spelling.
/// `renaming-=` retains one fact, with its representatives supplied by `RenamingEq`.
pub(in crate::slotted) fn proof_body(
    rule: &SourceRule,
    dag: &mut TermDag,
    bindings: &HashMap<String, TermId>,
) -> Result<(Vec<ResolvedFact>, IndexMap<String, TermId>), String> {
    let mut prefix = format!("{INTERNAL_SYMBOL_PREFIX}slotted-proof-");
    while bindings.keys().any(|name| name.starts_with(&prefix)) {
        prefix.push('-');
    }
    let mut symbols = SymbolGen::new(prefix);
    let mut bindings = bindings.clone();
    let mut auxiliary = IndexMap::default();
    let mut body = Vec::new();
    for fact in &rule.rule.body {
        if matches!(fact, ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(head), _)) if head.name() == "renaming-=")
        {
            body.push(fact.clone());
            continue;
        }
        let start = body.len();
        let fact = egglog::proof::proof_form_fact(fact.clone(), &mut body, &mut symbols);
        for binding in &body[start..] {
            let ResolvedFact::Eq(_, expr, ResolvedExpr::Var(_, var)) = binding else {
                unreachable!("normalizing slotted guards only lifts constructor operands")
            };
            let pattern = pattern_term(dag, expr);
            let term = instantiate(dag, pattern, &bindings)?;
            auxiliary.insert(var.name.clone(), term);
            bindings.insert(var.name.clone(), term);
        }
        body.push(fact);
    }
    Ok((body, auxiliary))
}

/// Register source guards with validators for the constructors visible at the query.
pub(super) fn register(graph: &mut EGraph, program: &Arc<ProofContext>) {
    for name in GUARDS {
        let program = program.clone();
        graph.add_pure_primitive(
            GuardSignature(validator_name(name)),
            Some(Arc::new(move |dag, args| {
                validate(&program, name, dag, args)?;
                Some(dag.lit(Literal::Unit))
            })),
        );
    }
}

fn validate(program: &ProofContext, name: &str, dag: &mut TermDag, args: &[TermId]) -> Option<()> {
    let holds = match (name, args) {
        ("renaming-=", [a, b]) => program.eq_modulo_renaming(dag, *a, *b),
        ("renaming-!=", [a, b]) => !program.eq_modulo_renaming(dag, *a, *b),
        ("!=", [a, b]) => !program.alpha_eq(dag, *a, *b),
        ("free" | "not-free", [slot, terms @ ..]) if !terms.is_empty() => {
            let slot = slot_of(dag, *slot)?;
            let free = terms
                .iter()
                .any(|&term| program.free_slots(dag, term).contains(&slot));
            free == (name == "free")
        }
        ("free-names-are", [term, slots @ ..]) => {
            let wanted = slots
                .iter()
                .map(|&slot| slot_of(dag, slot))
                .collect::<Option<BTreeSet<_>>>()?;
            program.free_slots(dag, *term) == wanted
        }
        _ => false,
    };
    holds.then_some(())
}

#[derive(Clone)]
struct GuardSignature(&'static str);

impl Primitive for GuardSignature {
    fn name(&self) -> &str {
        self.0
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn egglog::constraint::TypeConstraint> {
        Box::new(GuardTypeConstraint {
            name: self.0,
            span: span.clone(),
        })
    }
}

impl PurePrim for GuardSignature {
    fn apply(&self, _: PureState<'_, '_>, _: &[Value]) -> Option<Value> {
        None
    }
}

/// Source guards have rigid name operands and independently typed term operands.
struct GuardTypeConstraint {
    name: &'static str,
    span: Span,
}

impl egglog::constraint::TypeConstraint for GuardTypeConstraint {
    fn get(
        &self,
        arguments: &[egglog::AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn egglog::constraint::Constraint<egglog::AtomTerm, egglog::ArcSort>>> {
        use egglog::constraint::{AllEqualTypeConstraint, assign};
        let name = self.name;
        if !matches!(name, "free" | "not-free" | "free-names-are") {
            return AllEqualTypeConstraint::new(self.name, self.span.clone())
                .with_output_sort(UnitSort.to_arcsort())
                .get(arguments, typeinfo);
        }
        let Some((output, inputs)) = arguments.split_last() else {
            return vec![];
        };
        let mut constraints = vec![assign(output.clone(), UnitSort.to_arcsort())];
        let slots = if name == "free-names-are" {
            inputs.get(1..).unwrap_or_default()
        } else {
            inputs.get(..1).unwrap_or_default()
        };
        constraints.extend(
            slots
                .iter()
                .map(|arg| assign(arg.clone(), VarSort.to_arcsort())),
        );
        constraints
    }
}

#[cfg(test)]
#[path = "tests/guards.rs"]
mod tests;
