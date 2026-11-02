//! Prepare restricted constructor actions without effects; execute them through
//! the same command dispatch as resolved actions. Each action retains its own
//! commit and rebuild boundary.

use crate::*;

pub(super) struct GroundActions {
    pub(super) lookups: Vec<(egglog_bridge::TableAction, Vec<usize>)>,
    pub(super) union: Option<(usize, usize)>,
}

impl EGraph {
    /// Prepare one already-resolved constructor expression or union without
    /// allocating IDs or writing. Ordinary resolution has already checked types;
    /// this walk only admits closed calls supported by the physical native tables.
    /// Literals, variables, primitives, globals, views, indexes and custom sorts
    /// retain the ordinary compiler.
    pub(super) fn prepare_resolved_ground_action(
        &self,
        action: &ResolvedAction,
    ) -> Option<GroundActions> {
        fn prepare_expr(
            graph: &EGraph,
            expr: &ResolvedExpr,
            prepared: &mut GroundActions,
        ) -> Option<usize> {
            let GenericExpr::Call(_, ResolvedCall::Func(func), args) = expr else {
                return None;
            };
            let function = graph.functions.get(&func.name)?;
            if func.subtype != FunctionSubtype::Constructor
                || function.subtype() != FunctionSubtype::Constructor
                || func.num_outputs() != 1
                || func.role.is_global()
                || function.is_view()
                || function.is_let_binding()
                || graph.type_info.indexes.contains_key(&func.name)
                || !(func.output().as_ref() as &dyn Any).is::<EqSort>()
            {
                return None;
            }
            let table = egglog_bridge::TableAction::for_constructor_insertions(
                &graph.backend,
                function.backend_id,
            )?;
            if table.input_arity() != args.len() {
                return None;
            }
            let args = args
                .iter()
                .map(|arg| prepare_expr(graph, arg, prepared))
                .collect::<Option<Vec<_>>>()?;
            let index = prepared.lookups.len();
            prepared.lookups.push((table, args));
            Some(index)
        }

        if self.proof_state.original_typechecking.is_some() {
            return None;
        }
        let mut prepared = GroundActions {
            lookups: Vec::new(),
            union: None,
        };
        match action {
            ResolvedAction::Expr(_, expr) => {
                prepare_expr(self, expr, &mut prepared)?;
            }
            ResolvedAction::Union(_, left, right) => {
                let left = prepare_expr(self, left, &mut prepared)?;
                let right = prepare_expr(self, right, &mut prepared)?;
                prepared.union = Some((left, right));
            }
            _ => return None,
        }
        Some(prepared)
    }

    pub(super) fn eval_ground_actions(
        &mut self,
        prepared: Vec<GroundActions>,
    ) -> Result<(), Error> {
        #[cfg(test)]
        tests::GROUND_ACTIONS_EXECUTED.with(|count| count.set(count.get() + prepared.len()));
        let union = egglog_bridge::UnionAction::new(&self.backend);
        self.backend
            .run_actions(Some(&self.type_info), |state| {
                let mut values = Vec::new();
                for action in prepared {
                    values.clear();
                    for (table, args) in action.lookups {
                        let args: smallvec::SmallVec<[Value; 4]> =
                            args.iter().map(|index| values[*index]).collect();
                        values.push(table.lookup_or_insert(state, &args).unwrap());
                    }
                    if let Some((left, right)) = action.union {
                        union.union(state, values[left], values[right]);
                    }
                }
            })
            .map_err(|error| Error::BackendError(error.to_string()))
    }
}

#[cfg(test)]
mod tests;
