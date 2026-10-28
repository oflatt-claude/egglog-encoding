//! Construct raw extraction certificates from typed ground terms.
//!
//! Lookup returns runtime values and existing proof references. Construction
//! composes those raw proofs without inspecting their conclusions. Deferred
//! primitive expressions and global connectors are resolved during final lifting.

use std::iter::once;

use super::proof_checker::{eval_expr_with_subst, gather_global_actions, process_actions};
use super::proof_container_rebuild::rebuild_container_value_rec;
use super::proof_extractor::RootExtractor;
use super::proof_format::{ProofId, ProofStore, Proposition, RawProof, RawProofId, RawProofStore};
use super::proof_head::ProofAlgebra;
use crate::extract::find_canonical;
use crate::*;

#[derive(Clone, Copy)]
enum RowKind {
    /// The row proves `representative = constructor(canonical children)`.
    Constructor,
    /// The row connects a global to its source definition.
    Global,
    /// Project this column from a custom function's row proof.
    Output(usize),
}

/// Existing row evidence and its optional connection to the current leader.
#[derive(Clone, Copy)]
struct Row {
    kind: RowKind,
    /// An e-graph value of the proof sort, to be materialized before use.
    proof: Value,
    /// Existing proof from the view representative to its current leader.
    to_leader: Option<Value>,
}

/// The lookup result for one node of the input typed DAG.
/// Its position in the returned vector is that node's `TermId`.
struct Node {
    /// Canonical at the input node's sort, including nested container elements.
    value: Value,
    /// Absent for literals, primitives, and globals without a proof-bearing view.
    /// Having a value alone does not establish a container's existence.
    row: Option<Row>,
}

fn fail(message: impl Into<String>) -> Error {
    Error::ExtractError(message.into())
}

/// Append an expression to `dag`, representing globals as zero-argument calls.
/// Errors if the expression contains a local variable.
fn ground_expr(dag: &mut TermDag, root: &ResolvedExpr) -> Result<TermId, Error> {
    let mut pending = vec![(root, false)];
    let mut values = Vec::new();
    while let Some((expr, visited)) = pending.pop() {
        match expr {
            ResolvedExpr::Lit(_, literal) => values.push(dag.lit(literal.clone())),
            ResolvedExpr::Var(_, var) if var.is_global_ref => {
                values.push(dag.app(var.name.clone(), vec![]));
            }
            ResolvedExpr::Var(_, var) => {
                return Err(fail(format!("unbound ground variable {}", var.name)));
            }
            ResolvedExpr::Call(_, call, children) if visited => {
                let children = values.split_off(values.len() - children.len());
                values.push(dag.app(call.name().to_owned(), children));
            }
            ResolvedExpr::Call(_, _, children) => {
                pending.push((expr, true));
                pending.extend(children.iter().rev().map(|child| (child, false)));
            }
        }
    }
    Ok(values[0])
}

impl EGraph {
    /// Look up `expr`, extract representatives, and certify each equality.
    /// Returns the extraction output followed by its proofs; adds no e-graph rows.
    pub(crate) fn run_prove_extract(
        &self,
        expr: &ResolvedExpr,
        variants: &ResolvedExpr,
    ) -> Result<Vec<CommandOutput>, Error> {
        let sort = expr.output_type();
        let value = self.lookup_ground_expr(expr)?;
        let count = self.lookup_ground_expr(variants)?;
        let count: i64 = self.backend.base_values().unwrap(count);
        if count < 0 {
            return Err(fail("cannot extract a negative number of variants"));
        }
        let (mut terms, outputs, extraction) = if count == 0 {
            let (dag, term, cost) = self.extract_value(&sort, value)?;
            let output = CommandOutput::ExtractBest(dag.clone(), cost, term);
            (dag, vec![term], output)
        } else {
            let mut extracted =
                self.extract_variants(vec![(sort.clone(), value)], count as usize)?;
            let outputs = extracted
                .variants
                .pop()
                .unwrap()
                .into_iter()
                .map(|term| term.term)
                .collect::<Vec<_>>();
            let output = CommandOutput::ExtractVariants(extracted.termdag.clone(), outputs.clone());
            (extracted.termdag, outputs, output)
        };
        let input = ground_expr(&mut terms, expr)?;
        let (proof_store, proof_ids) = self.prove_extracted_terms(&terms, input, &outputs, sort)?;
        Ok(vec![
            extraction,
            CommandOutput::ProveExtract {
                proof_store,
                proof_ids,
            },
        ])
    }

    /// Resolve a ground expression to its canonical runtime value without
    /// inserting rows. Container existence is checked later during certification.
    fn lookup_ground_expr(&self, expr: &ResolvedExpr) -> Result<Value, Error> {
        let mut terms = TermDag::default();
        let root = ground_expr(&mut terms, expr)?;
        let (typed, roots) = self
            .type_info
            .source_types()
            .typecheck_term_dag(&terms, &[(root, Some(expr.output_type()))], Context::Read)
            .map_err(|error| fail(error.to_string()))?;
        let values = lookup(self, &typed, &roots)?;
        Ok(values[roots[0]].value)
    }
    /// Prove equality of two existing ground terms without inserting them.
    /// See [`Self::prove_extracted_terms`] for input requirements and errors.
    pub fn prove_equal_terms(
        &self,
        terms: &TermDag,
        left: TermId,
        right: TermId,
        sort: ArcSort,
    ) -> Result<(ProofStore, ProofId), Error> {
        let (store, ids) = self.prove_extracted_terms(terms, left, &[right], sort)?;
        Ok((store, ids[0]))
    }

    /// Prove equality of `input` to each term in `outputs`, in that order.
    /// Root IDs refer to `terms`, and every root must have the supplied `sort`.
    /// Globals are zero-argument calls. Proof endpoints use their source definitions
    /// and the evaluated forms of primitive expressions.
    /// Primitives must support read-only evaluation and proof validation.
    ///
    /// Errors on invalid or ambiguous typings, unavailable terms or proof evidence,
    /// or unequal roots. Performs no extraction and writes no e-graph rows.
    /// An empty `outputs` slice still validates and proves `input` to its leader,
    /// but returns no equality proofs. Duplicate outputs retain their positions.
    ///
    /// # Example
    ///
    /// An extractor may return `F(B)` even though the source only inserted `F(A)`.
    /// Existing evidence for `A = B` and `F(A)` suffices to certify that result.
    ///
    /// ```
    /// use egglog::{EGraph, Error, TermDag};
    ///
    /// let mut graph = EGraph::new_with_proofs();
    /// graph.parse_and_run_program(None, "
    ///     (datatype E (A) (B) (F E))
    ///     (F (A)) (B) (union (A) (B)) (run 1)
    /// ")?;
    /// let mut terms = TermDag::default();
    /// let a = terms.app("A".into(), vec![]);
    /// let b = terms.app("B".into(), vec![]);
    /// let input = terms.app("F".into(), vec![a]);
    /// let output = terms.app("F".into(), vec![b]);
    /// let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    /// let (store, proofs) = graph.prove_extracted_terms(&terms, input, &[output], sort)?;
    /// let equality = store.get(proofs[0]);
    /// assert_eq!(store.term_dag().to_string(equality.lhs()), "(F (A))");
    /// assert_eq!(store.term_dag().to_string(equality.rhs()), "(F (B))");
    /// # Ok::<(), Error>(())
    /// ```
    pub fn prove_extracted_terms(
        &self,
        terms: &TermDag,
        input: TermId,
        outputs: &[TermId],
        sort: ArcSort,
    ) -> Result<(ProofStore, Vec<ProofId>), Error> {
        let roots = once(input)
            .chain(outputs.iter().copied())
            .map(|root| (root, Some(sort.clone())))
            .collect::<Vec<_>>();
        let (typed, roots) = self
            .type_info
            .source_types()
            .typecheck_term_dag(terms, &roots, Context::Read)
            .map_err(|error| fail(error.to_string()))?;
        let values = lookup(self, &typed, &roots)?;
        let mut builder = GroundProofs::new(self);
        let evidence = builder.build(&typed, &values)?;
        let input = builder.root(
            evidence[roots[0]],
            &sort,
            values[roots[0]].value,
            &typed.to_string(roots[0]),
            None,
        )?;
        let mut raw_proofs = vec![input];
        for &id in &roots[1..] {
            let right = builder.root(
                evidence[id],
                &sort,
                values[id].value,
                &typed.to_string(id),
                Some(input),
            )?;
            let back = builder.raw.sym(right);
            raw_proofs.push(builder.raw.trans(input, back));
        }
        let (mut store, mut proof_ids) = builder.lift(&raw_proofs)?;
        proof_ids.remove(0);
        store
            .remove_globals(&self.proof_check_program)
            .map_err(|error| fail(error.to_string()))?;
        let mut proofs = Vec::with_capacity(outputs.len());
        let mut simplified = Default::default();
        for proof in proof_ids {
            let expected = store.get(proof).proposition().clone();
            if self.proof_state.verify_proofs {
                store
                    .check_proof(proof, &self.proof_check_program)
                    .map_err(|error| fail(format!("invalid ground-term proof: {error}")))?;
            }
            let proof = store.simplify_with_cache(proof, &mut simplified);
            if store.get(proof).proposition() != &expected {
                return Err(fail("proof simplification changed the requested equality"));
            }
            if self.proof_state.verify_proofs {
                store
                    .check_proof(proof, &self.proof_check_program)
                    .map_err(|error| {
                        fail(format!("invalid simplified ground-term proof: {error}"))
                    })?;
            }
            proofs.push(proof);
        }
        Ok((store, proofs))
    }
}

/// Look up canonical values and available view evidence for every node in `terms`.
/// The result has `terms.size()` entries: entry `id` describes `terms.get(id)`,
/// including non-root children. It can be passed directly to [`GroundProofs::build`].
///
/// `terms` must have children before parents. `roots` must be nonempty, contain
/// valid IDs from this DAG, and refer to terms of the same sort. On success,
/// every root has the same canonical value. No e-graph rows are inserted.
///
/// Errors on missing rows or proof columns, unsupported or failed primitive
/// evaluation, or unequal root values. Container values may still lack an
/// existence witness; this is checked when their certificates are completed.
fn lookup(egraph: &EGraph, terms: &TypedTermDag, roots: &[TermId]) -> Result<Vec<Node>, Error> {
    if egraph
        .get_sort_by_name(&egraph.proof_state.proof_names.proof_datatype)
        .is_none()
    {
        return Err(fail("ground-term certification requires proof evidence"));
    }
    let mut nodes: Vec<Node> = Vec::with_capacity(terms.size());
    for (id, node) in terms.nodes() {
        let sort = node.sort();
        let (value, row) = match node {
            TypedTerm::Var(never) => match *never {},
            TypedTerm::Lit(literal) => {
                let value = egraph
                    .read(|mut state| {
                        state.eval_resolved_expr(
                            &ResolvedExpr::Lit(Span::Panic, literal.clone()),
                            &[],
                        )
                    })
                    .ok_or_else(|| fail("could not evaluate literal"))?;
                (value, None)
            }
            TypedTerm::App(ResolvedCall::Primitive(primitive), children) => {
                if primitive.validator().is_none() {
                    return Err(fail(format!(
                        "primitive {} has no proof validator",
                        primitive.name()
                    )));
                }
                let signature = primitive
                    .input()
                    .iter()
                    .cloned()
                    .chain(once(sort.clone()))
                    .collect::<Vec<_>>();
                let ResolvedCall::Primitive(runtime) = ResolvedCall::from_resolution(
                    primitive.name(),
                    &signature,
                    &egraph.type_info,
                    Context::Read,
                    &Span::Panic,
                )?
                else {
                    return Err(fail("expected a primitive registration"));
                };
                let inputs = children
                    .iter()
                    .map(|child| nodes[*child].value)
                    .collect::<Vec<_>>();
                let value = egraph
                    .read(|mut state| state.apply_primitive(&runtime, &inputs))
                    .ok_or_else(|| fail(format!("primitive {} failed", primitive.name())))?;
                (canonical(egraph, value, &sort)?, None)
            }
            TypedTerm::App(ResolvedCall::Func(function), children) => {
                let key = children
                    .iter()
                    .map(|child| nodes[*child].value)
                    .collect::<Vec<_>>();
                // A source alias `(let y x)` has the same written term as
                // x. Its value-only binding can carry a reflexive proof, so
                // read the original binding's connector as the evidence.
                let origin = global_origin(egraph, &function.name);
                let table = egraph
                    .functions
                    .get(&origin)
                    .ok_or_else(|| fail(format!("missing view {}", function.name)))?;
                let row = egraph
                    .backend
                    .lookup_row(table.backend_id, &key)
                    .ok_or_else(|| {
                        fail(format!(
                            "Could not find term {} in the e-graph",
                            terms.to_string(id)
                        ))
                    })?;
                let raw = row[key.len()];
                let value = canonical(egraph, raw, &sort)?;
                let proof_row = if table.decl.role.is_view() && table.func_type.outputs.len() == 2 {
                    let kind = if function.role.is_global() {
                        RowKind::Global
                    } else if table.decl.role == FunctionRole::FunctionView {
                        RowKind::Output(key.len())
                    } else {
                        RowKind::Constructor
                    };
                    let proof = row[key.len() + 1];
                    let to_leader = to_leader(egraph, raw, value, &sort)?;
                    Some(Row {
                        kind,
                        proof,
                        to_leader,
                    })
                } else if function.role.is_global() && !sort.is_eq_sort() {
                    None
                } else {
                    return Err(fail(format!("{} has no proof column", function.name)));
                };
                (value, proof_row)
            }
            TypedTerm::App(ResolvedCall::Values(_), _) => {
                return Err(fail("tuple terms cannot be certified"));
            }
        };
        nodes.push(Node { value, row });
    }
    let input = nodes[roots[0]].value;
    if roots[1..].iter().any(|root| nodes[*root].value != input) {
        return Err(fail("requested terms have different leaders"));
    }
    Ok(nodes)
}

/// Follow source global aliases to the binding that supplies their evidence.
/// A name with no source alias is returned unchanged.
fn global_origin(egraph: &EGraph, name: &str) -> String {
    let mut origin = name.to_owned();
    let mut seen = HashSet::default();
    while egraph.type_info.is_global(&origin) && seen.insert(origin.clone()) {
        let alias = gather_global_actions(&egraph.proof_check_program).find_map(|action| {
            let ResolvedAction::Let(_, var, expr) = action else {
                return None;
            };
            if var.name != origin {
                return None;
            }
            match expr {
                ResolvedExpr::Var(_, var) if var.is_global_ref => Some(var.name.clone()),
                ResolvedExpr::Call(_, call, args)
                    if args.is_empty() && egraph.type_info.is_global(call.name()) =>
                {
                    Some(call.name().to_owned())
                }
                _ => None,
            }
        });
        let Some(alias) = alias else { break };
        origin = alias;
    }
    origin
}

/// Return `value` with equality-sort elements replaced by their leaders,
/// including inside nested containers. Errors if a container cannot be rebuilt.
/// The value must belong to `sort`; no e-graph rows are inserted.
fn canonical(egraph: &EGraph, value: Value, sort: &ArcSort) -> Result<Value, Error> {
    if sort.is_eq_container_sort() {
        egraph
            .read(|mut state| {
                rebuild_container_value_rec(
                    &mut state,
                    sort,
                    value,
                    &egraph.proof_state.uf_parent,
                    true,
                )
            })
            .ok_or_else(|| fail("could not canonicalize container value"))
    } else {
        Ok(find_canonical(egraph, value, sort))
    }
}

/// Read the union-find proof connecting a view's output to `leader`.
/// Returns `None` when the values already agree or `sort` is not an equality sort.
/// Otherwise errors if the stored edge is missing or ends at a different value.
fn to_leader(
    egraph: &EGraph,
    raw: Value,
    leader: Value,
    sort: &ArcSort,
) -> Result<Option<Value>, Error> {
    if raw == leader || !sort.is_eq_sort() {
        return Ok(None);
    }
    let name = egraph
        .proof_state
        .uf_parent
        .get(sort.name())
        .ok_or_else(|| fail("missing union-find proof table"))?;
    let table = &egraph.functions[name];
    let row = egraph
        .backend
        .lookup_row(table.backend_id, &[raw])
        .ok_or_else(|| fail("missing equality to the leader"))?;
    if row[1] != leader {
        return Err(fail("union proof does not reach the leader"));
    }
    Ok(Some(row[2]))
}

/// Builds raw certificates using runtime values and existing proof references.
/// No proof is lifted until all requested roots have been assembled.
struct GroundProofs<'a> {
    egraph: &'a EGraph,
    raw: RawProofStore,
    extractor: RootExtractor,
}

impl<'a> GroundProofs<'a> {
    fn new(egraph: &'a EGraph) -> Self {
        Self {
            egraph,
            raw: RawProofStore::new(&egraph.proof_state.proof_names),
            extractor: RootExtractor::new(),
        }
    }

    /// Materialize an existing proof value without computing its conclusion.
    fn import(&mut self, value: Value) -> Result<RawProofId, Error> {
        let sort = self
            .egraph
            .get_sort_by_name(&self.egraph.proof_state.proof_names.proof_datatype)
            .ok_or_else(|| fail("missing proof sort"))?
            .clone();
        let term = self
            .extractor
            .extract(self.egraph, &mut self.raw.term_dag, value, &sort)
            .ok_or_else(|| fail("could not materialize existing proof evidence"))?;
        Ok(self.raw.parse(term))
    }

    /// Return raw certificates indexed by input `TermId`. `values` must be the
    /// complete result of lookup on this DAG. Container primitive nodes remain
    /// deferred until a parent or root supplies their existence witness.
    fn build(&mut self, terms: &TypedTermDag, values: &[Node]) -> Result<Vec<RawProofId>, Error> {
        let mut proofs: Vec<RawProofId> = Vec::with_capacity(terms.size());
        for ((_, term), value) in terms.nodes().zip(values) {
            let mut proof = match term {
                TypedTerm::Lit(literal) => {
                    let term = self.raw.term_dag.lit(literal.clone());
                    self.raw.add_proof(RawProof::Fiat(term, term))
                }
                TypedTerm::App(ResolvedCall::Primitive(primitive), children) => {
                    let arguments = children.iter().map(|&id| proofs[id]).collect();
                    self.raw
                        .add_proof(RawProof::Primitive(primitive.clone(), arguments, None))
                }
                TypedTerm::App(ResolvedCall::Func(function), children) => {
                    if let Some(row) = value.row {
                        let row_proof = self.import(row.proof)?;
                        match row.kind {
                            RowKind::Constructor => {
                                let mut proof = row_proof;
                                for (index, &child) in children.iter().enumerate() {
                                    let witness =
                                        self.raw.add_proof(RawProof::Proj(row_proof, index));
                                    proofs[child] = self.raw.anchored(proofs[child], witness);
                                    let back = self.raw.sym(proofs[child]);
                                    proof = self.raw.congr(proof, index, back);
                                }
                                self.raw.sym(proof)
                            }
                            RowKind::Output(column) => {
                                self.raw.add_proof(RawProof::Proj(row_proof, column))
                            }
                            RowKind::Global => self
                                .raw
                                .add_proof(RawProof::Global(function.name.clone(), row_proof)),
                        }
                    } else {
                        self.raw
                            .add_proof(RawProof::GlobalValue(function.name.clone()))
                    }
                }
                _ => return Err(fail("unsupported ground term")),
            };
            if let Some(edge) = value.row.and_then(|row| row.to_leader) {
                let edge = self.import(edge)?;
                proof = self.raw.trans(proof, edge);
            }
            proofs.push(proof);
        }
        Ok(proofs)
    }

    /// Supply a deferred container root with evidence at its requested sort.
    /// `equal_root` must already certify the same sort and canonical runtime value.
    fn root(
        &mut self,
        proof: RawProofId,
        sort: &ArcSort,
        value: Value,
        written: &str,
        equal_root: Option<RawProofId>,
    ) -> Result<RawProofId, Error> {
        if !sort.is_container_sort()
            || !matches!(self.raw.get(proof), RawProof::Primitive(_, _, None))
        {
            return Ok(proof);
        }
        let witness = if let Some(root) = equal_root {
            root
        } else if let Some(row) = self.container_row(sort, value) {
            self.import(row)?
        } else {
            self.source_container(sort, value)?
                .ok_or_else(|| fail(format!("Could not find term {written} in the e-graph")))?
        };
        Ok(self.raw.anchored(proof, witness))
    }

    /// Find an existing view containing this typed container value, possibly nested.
    fn container_row(&self, wanted: &ArcSort, value: Value) -> Option<Value> {
        let mut found = None;
        let mut tables = self.egraph.functions.values().collect::<Vec<_>>();
        tables.sort_by_key(|table| table.name());
        for table in tables {
            if !table.decl.role.is_view() || table.func_type.outputs.len() != 2 {
                continue;
            }
            let mut sorts = table.func_type.input.clone();
            if table.decl.role == FunctionRole::FunctionView {
                sorts.push(table.func_type.output().clone());
            }
            self.egraph.backend.for_each(table.backend_id, |row| {
                if found.is_some() {
                    return;
                }
                let mut pending = sorts
                    .iter()
                    .cloned()
                    .zip(row.vals.iter().copied())
                    .collect::<Vec<_>>();
                let mut seen = HashSet::default();
                while let Some((sort, held)) = pending.pop() {
                    if !sort.is_container_sort() || !seen.insert((sort.name().to_owned(), held)) {
                        continue;
                    }
                    if sort.name() == wanted.name() && held == value {
                        found = Some(row.vals[table.func_type.input.len() + 1]);
                        break;
                    }
                    pending.extend(sort.inner_values(self.egraph.backend.container_values(), held));
                }
            });
            if found.is_some() {
                break;
            }
        }
        found
    }

    /// Find a source action establishing the requested typed container.
    /// Only terms actually established by those actions receive a Fiat proof.
    fn source_container(
        &mut self,
        sort: &ArcSort,
        value: Value,
    ) -> Result<Option<RawProofId>, Error> {
        let actions = gather_global_actions(&self.egraph.proof_check_program).collect::<Vec<_>>();
        let source = process_actions(
            "global_actions",
            HashMap::default(),
            &actions,
            &mut self.raw.term_dag,
        )
        .map_err(|error| fail(error.to_string()))?;
        let mut found = None;
        for action in actions {
            action.clone().visit_exprs(&mut |expr| {
                if found.is_none()
                    && expr.output_type().name() == sort.name()
                    && self.egraph.lookup_ground_expr(&expr).ok() == Some(value)
                    && let Ok((term, _)) = eval_expr_with_subst(
                        "global_actions",
                        &expr,
                        &mut self.raw.term_dag,
                        &source.var_bindings,
                    )
                    && source.propositions.contains(&Proposition::new(term, term))
                {
                    found = Some(term);
                }
                expr
            });
        }
        Ok(found.map(|term| self.raw.add_proof(RawProof::Fiat(term, term))))
    }

    /// Lift the finished raw proof DAG through the ordinary proof conversion.
    fn lift(self, roots: &[RawProofId]) -> Result<(ProofStore, Vec<ProofId>), Error> {
        let normalizers = self
            .egraph
            .type_info
            .sorts
            .values()
            .filter_map(|sort| sort.rebuild_container_normalizer())
            .collect();
        let mut value_heads = HashSet::default();
        for sort in self.egraph.type_info.sorts.values() {
            if let Some(head) = sort.prim_value_constructor() {
                if self.egraph.type_info.get_prims(&head).map_or(0, <[_]>::len) != 1 {
                    return Err(fail(format!(
                        "ambiguous primitive value constructor {head}"
                    )));
                }
                value_heads.insert(head);
            }
        }
        self.raw
            .lift(
                &self.egraph.proof_check_program,
                roots,
                normalizers,
                value_heads,
            )
            .map_err(fail)
    }
}
