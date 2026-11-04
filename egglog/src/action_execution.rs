//! Prepare restricted constructor actions without effects; execute them through
//! the same command dispatch as resolved actions. Only insertion-only runs share
//! a commit. Unions retain an individual rebuild boundary. Constructor calls may
//! contain literal leaves, which are interned only after the whole action passes
//! admission; unsupported forms retain the ordinary compiler.

use crate::*;
use smallvec::SmallVec;
use std::rc::Rc;

// Semantic and physical metadata are acquired together, only during dispatch.
// Entries expire before any command can change a signature or table ID.
/// Constructor metadata keyed by function name; `None` records functions
/// that cannot use prepared constructor actions.
type GroundActionCache = HashMap<String, Option<(Arc<FuncType>, Rc<egglog_bridge::TableAction>)>>;

enum GroundExpr {
    Literal(Literal),
    Lookup(Rc<egglog_bridge::TableAction>, SmallVec<[usize; 4]>),
}

pub(super) struct GroundActions {
    // Postorder nodes; lookup arguments name earlier results. Literals are
    // interned only during execution, after the complete action is admitted.
    nodes: Vec<GroundExpr>,
    union: Option<(usize, usize)>,
}

#[derive(Default)]
pub(super) struct GroundActionBatch {
    pending: Vec<GroundActions>,
    nodes: usize,
    pub(super) calls: GroundActionCache,
}

impl EGraph {
    /// Commit insertions and invalidate metadata before ordinary resolution or
    /// command execution can replace signatures or table IDs.
    pub(super) fn commit_ground_actions(
        &mut self,
        pending: &mut GroundActionBatch,
    ) -> Result<(), Error> {
        self.flush_ground_actions(pending)?;
        pending.calls.clear();
        Ok(())
    }

    /// Cache only unambiguous constructor signatures. Resolved calls with a
    /// primitive alternative retain the compiler and cannot seed source typing.
    fn constructor_call(
        &self,
        head: &str,
        calls: &mut GroundActionCache,
    ) -> Option<(Arc<FuncType>, Rc<egglog_bridge::TableAction>)> {
        if let Some(cached) = calls.get(head) {
            return cached.clone();
        }
        let call = self
            .type_info
            .closed_constructor_type(head)
            .and_then(|func| {
                let function = self.functions.get(&func.name)?;
                if function.subtype() != FunctionSubtype::Constructor
                    || function.is_view()
                    || function.is_let_binding()
                {
                    return None;
                }
                let table = egglog_bridge::TableAction::for_constructor_insertions(
                    &self.backend,
                    function.backend_id,
                )?;

                (table.input_arity() == func.input.len()).then(|| (func.clone(), Rc::new(table)))
            });
        calls.insert(head.into(), call.clone());
        call
    }

    /// Check AST or resolved calls and select native tables in one pure walk.
    /// Preparation allocates no IDs or rows; a decline keeps the original form
    /// for ordinary typing and compilation.
    pub(super) fn prepare_ground_action<Node: typechecking::CallView>(
        &self,
        action: typechecking::ClosedAction<&Node>,
        calls: &mut GroundActionCache,
    ) -> Option<GroundActions> {
        fn prepare_expr<Node: typechecking::CallView>(
            graph: &EGraph,
            expr: &Node,
            prepared: &mut GroundActions,
            calls: &mut GroundActionCache,
        ) -> Option<(usize, ArcSort)> {
            let (node, sort) = match expr.view()? {
                typechecking::CallOrLiteral::Literal(literal) => (
                    GroundExpr::Literal(literal.clone()),
                    sort::literal_sort(literal),
                ),
                typechecking::CallOrLiteral::Call(head, args) => {
                    let (func, table) = graph.constructor_call(head, calls)?;
                    if func.input.len() != args.len() {
                        return None;
                    }
                    let mut checked_args = SmallVec::new();
                    for (arg, expected) in args.iter().zip(&func.input) {
                        let (value, sort) = prepare_expr(graph, arg, prepared, calls)?;
                        if !Arc::ptr_eq(&sort, expected) && sort.name() != expected.name() {
                            return None;
                        }
                        checked_args.push(value);
                    }
                    (
                        GroundExpr::Lookup(table, checked_args),
                        func.output().clone(),
                    )
                }
            };
            let index = prepared.nodes.len();
            prepared.nodes.push(node);
            Some((index, sort))
        }

        if self.proof_state.original_typechecking.is_some() {
            return None;
        }
        let mut prepared = GroundActions {
            nodes: Vec::new(),
            union: None,
        };
        match action {
            typechecking::ClosedAction::Expr(expr) => {
                if !matches!(expr.view()?, typechecking::CallOrLiteral::Call(..)) {
                    return None;
                }
                prepare_expr(self, expr, &mut prepared, calls)?;
            }
            typechecking::ClosedAction::Union(left, right) => {
                if !matches!(left.view()?, typechecking::CallOrLiteral::Call(..))
                    || !matches!(right.view()?, typechecking::CallOrLiteral::Call(..))
                {
                    return None;
                }
                let (left, left_sort) = prepare_expr(self, left, &mut prepared, calls)?;
                let (right, right_sort) = prepare_expr(self, right, &mut prepared, calls)?;
                if (!Arc::ptr_eq(&left_sort, &right_sort) && left_sort.name() != right_sort.name())
                    || !self.type_info.is_sort_unionable(&left_sort)
                {
                    return None;
                }
                prepared.union = Some((left, right));
            }
        }
        Some(prepared)
    }

    pub(super) fn eval_ground_actions(
        &mut self,
        prepared: Vec<GroundActions>,
    ) -> Result<(), Error> {
        #[cfg(test)]
        tests::GROUND_ACTIONS_EXECUTED.with(|count| count.set(count.get() + prepared.len()));
        #[cfg(test)]
        let batch_event = tests::BATCH_EVENTS.with(|slot| {
            slot.borrow().as_ref().map(|_| {
                (
                    prepared.len(),
                    prepared
                        .first()
                        .map(|action| {
                            action
                                .nodes
                                .iter()
                                .filter_map(|node| match node {
                                    GroundExpr::Lookup(table, _) => Some(table.clone()),
                                    GroundExpr::Literal(_) => None,
                                })
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_default(),
                )
            })
        });
        let union = egglog_bridge::UnionAction::new(&self.backend);
        let result = self
            .backend
            .run_actions(Some(&self.type_info), |state| {
                let mut values = Vec::new();
                let mut arguments = Vec::new();
                // Shared handles identify physical tables. Results remain valid
                // only within this backend transaction, until commit/rebuild.
                let mut constants = HashMap::default();
                for action in prepared {
                    values.clear();
                    for node in action.nodes {
                        let value = match node {
                            GroundExpr::Literal(literal) => {
                                literal_to_value(state.base_values(), &literal)
                            }
                            GroundExpr::Lookup(table, args) if args.is_empty() => {
                                *constants.entry(Rc::as_ptr(&table)).or_insert_with(|| {
                                    #[cfg(test)]
                                    tests::NULLARY_LOOKUPS.with(|count| count.set(count.get() + 1));
                                    table.lookup_or_insert(state, &[]).unwrap()
                                })
                            }
                            GroundExpr::Lookup(table, args) => {
                                arguments.clear();
                                arguments.extend(args.iter().map(|index| values[*index]));
                                table.lookup_or_insert(state, &arguments).unwrap()
                            }
                        };
                        values.push(value);
                    }
                    if let Some((left, right)) = action.union {
                        union.union(state, values[left], values[right]);
                    }
                }
            })
            .map_err(|error| Error::BackendError(error.to_string()));
        #[cfg(test)]
        if result.is_ok() {
            if let Some(batch_event) = batch_event {
                tests::BATCH_EVENTS.with(|slot| {
                    if let Some(events) = slot.borrow_mut().as_mut() {
                        events.push(batch_event);
                    }
                });
            }
            tests::ORDER_LOG.with(|slot| {
                if let Some(log) = slot.borrow().as_ref() {
                    log.lock().unwrap().push("commit");
                }
            });
        }
        result
    }

    /// Constructor insertion runs share a bounded transaction. A union retains
    /// its original commit/rebuild boundary, including container callbacks.
    pub(super) fn queue_ground_action(
        &mut self,
        prepared: GroundActions,
        pending: &mut GroundActionBatch,
    ) -> Result<(), Error> {
        if prepared.union.is_some() {
            self.flush_ground_actions(pending)?;
            self.eval_ground_actions(vec![prepared])
        } else {
            pending.nodes += prepared.nodes.len();
            pending.pending.push(prepared);
            if pending.pending.len() >= 256 || pending.nodes >= 16_384 {
                self.flush_ground_actions(pending)?;
            }
            Ok(())
        }
    }

    /// Drain exactly once; failed effects are never replayed.
    pub(super) fn flush_ground_actions(
        &mut self,
        pending: &mut GroundActionBatch,
    ) -> Result<(), Error> {
        pending.nodes = 0;
        if !pending.pending.is_empty() {
            let timer = Instant::now();
            let result = self.eval_ground_actions(std::mem::take(&mut pending.pending));
            self.overall_report.commands_actions += timer.elapsed();
            result?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
