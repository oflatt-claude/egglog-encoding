//! Equality proofs for existing ground terms, independent of the extractor.

use std::iter::once;

use super::proof_checker::{eval_expr_with_subst, gather_global_actions, process_actions};
use super::proof_container_rebuild::rebuild_container_value_rec;
use super::proof_extractor::RootExtractor;
use super::proof_format::{
    Justification, Proof, ProofId, ProofStore, Proposition, SynthKey, proof_store_from_terms,
};
use super::proof_head::ProofAlgebra;
use crate::extract::find_canonical;
use crate::*;

#[derive(Clone, Copy)]
enum RowKind {
    Constructor,
    Global,
    Output(usize),
}

#[derive(Clone, Copy)]
struct Row {
    kind: RowKind,
    proof: usize,
    union: Option<usize>,
}

struct Node {
    value: Value,
    row: Option<Row>,
}

struct Lookup<'a> {
    egraph: &'a EGraph,
    terms: &'a TypedTermDag,
    roots: &'a [TermId],
    nodes: HashMap<TermId, Node>,
    evidence: IndexSet<Value>,
    unanchored_container_roots: Vec<TermId>,
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

    fn lookup_ground_expr(&self, expr: &ResolvedExpr) -> Result<Value, Error> {
        let mut terms = TermDag::default();
        let root = ground_expr(&mut terms, expr)?;
        let (typed, roots) = self
            .type_info
            .source_types()
            .typecheck_term_dag(&terms, &[(root, Some(expr.output_type()))], Context::Read)
            .map_err(|error| fail(error.to_string()))?;
        let lookup = Lookup::new(self, &typed, &roots)?;
        Ok(lookup.nodes[&roots[0]].value)
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
        let mut lookup = Lookup::new(self, &typed, &roots)?;
        lookup.find_root_container_anchors()?;
        let (mut store, certificates) = lookup.compose()?;
        let input = roots[0];
        let mut proofs = Vec::with_capacity(outputs.len());
        let mut simplified = Default::default();
        for &output in &roots[1..] {
            let left = certificates[&input];
            let right = certificates[&output];
            if store.get(left).rhs() != store.get(right).rhs() {
                return Err(fail("requested terms have different leaders"));
            }
            let back = store.sym(right);
            let proof = store.trans(left, back);
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

impl<'a> Lookup<'a> {
    fn new(
        egraph: &'a EGraph,
        terms: &'a TypedTermDag,
        roots: &'a [TermId],
    ) -> Result<Self, Error> {
        if egraph
            .get_sort_by_name(&egraph.proof_state.proof_names.proof_datatype)
            .is_none()
        {
            return Err(fail("ground-term certification requires proof evidence"));
        }
        let mut this = Self {
            egraph,
            terms,
            roots,
            nodes: HashMap::default(),
            evidence: IndexSet::default(),
            unanchored_container_roots: vec![],
        };
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
                        .map(|child| this.nodes[child].value)
                        .collect::<Vec<_>>();
                    let value = egraph
                        .read(|mut state| state.apply_primitive(&runtime, &inputs))
                        .ok_or_else(|| fail(format!("primitive {} failed", primitive.name())))?;
                    (this.canonical(value, &sort)?, None)
                }
                TypedTerm::App(ResolvedCall::Func(function), children) => {
                    let key = children
                        .iter()
                        .map(|child| this.nodes[child].value)
                        .collect::<Vec<_>>();
                    // A source alias `(let y x)` has the same written term as
                    // x. Its value-only binding can carry a reflexive proof, so
                    // read the original binding's connector as the evidence.
                    let origin = this.global_origin(&function.name);
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
                    let value = this.canonical(raw, &sort)?;
                    let proof_row =
                        if table.decl.role.is_view() && table.func_type.outputs.len() == 2 {
                            let kind = if function.role.is_global() {
                                RowKind::Global
                            } else if table.decl.role == FunctionRole::FunctionView {
                                RowKind::Output(key.len())
                            } else {
                                RowKind::Constructor
                            };
                            let proof = this.evidence.insert_full(row[key.len() + 1]).0;
                            let union = this.union(raw, value, &sort)?;
                            Some(Row { kind, proof, union })
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
            this.nodes.insert(id, Node { value, row });
        }
        let input = this.nodes[&roots[0]].value;
        if roots[1..]
            .iter()
            .any(|root| this.nodes[root].value != input)
        {
            return Err(fail("requested terms have different leaders"));
        }
        Ok(this)
    }

    fn global_origin(&self, name: &str) -> String {
        let mut origin = name.to_owned();
        let mut seen = HashSet::default();
        while self.egraph.type_info.is_global(&origin) && seen.insert(origin.clone()) {
            let alias =
                gather_global_actions(&self.egraph.proof_check_program).find_map(|action| {
                    let ResolvedAction::Let(_, var, expr) = action else {
                        return None;
                    };
                    if var.name != origin {
                        return None;
                    }
                    match expr {
                        ResolvedExpr::Var(_, var) if var.is_global_ref => Some(var.name.clone()),
                        ResolvedExpr::Call(_, call, args)
                            if args.is_empty() && self.egraph.type_info.is_global(call.name()) =>
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

    fn canonical(&self, value: Value, sort: &ArcSort) -> Result<Value, Error> {
        if sort.is_eq_container_sort() {
            self.egraph
                .read(|mut state| {
                    rebuild_container_value_rec(
                        &mut state,
                        sort,
                        value,
                        &self.egraph.proof_state.uf_parent,
                        true,
                    )
                })
                .ok_or_else(|| fail("could not canonicalize container value"))
        } else {
            Ok(find_canonical(self.egraph, value, sort))
        }
    }

    fn union(&mut self, raw: Value, leader: Value, sort: &ArcSort) -> Result<Option<usize>, Error> {
        if raw == leader || !sort.is_eq_sort() {
            return Ok(None);
        }
        let name = self
            .egraph
            .proof_state
            .uf_parent
            .get(sort.name())
            .ok_or_else(|| fail("missing union-find proof table"))?;
        let table = &self.egraph.functions[name];
        let row = self
            .egraph
            .backend
            .lookup_row(table.backend_id, &[raw])
            .ok_or_else(|| fail("missing equality to the leader"))?;
        if row[1] != leader {
            return Err(fail("union proof does not reach the leader"));
        }
        Ok(Some(self.evidence.insert_full(row[2]).0))
    }

    // A root container has no parent to prove its existence. Find a source view
    // column containing the same value and sort.
    fn find_root_container_anchors(&mut self) -> Result<(), Error> {
        let mut wanted = self
            .roots
            .iter()
            .filter_map(|id| {
                let sort = self.terms.get(*id).sort();
                sort.is_container_sort()
                    .then(|| (sort.name().to_owned(), self.nodes[id].value))
            })
            .collect::<HashSet<_>>();
        if wanted.is_empty() {
            return Ok(());
        }
        let mut tables = self.egraph.functions.values().collect::<Vec<_>>();
        tables.sort_by_key(|table| table.name());
        for table in tables {
            if wanted.is_empty() {
                break;
            }
            if !table.decl.role.is_view() || table.func_type.outputs.len() != 2 {
                continue;
            }
            let mut sorts = table.func_type.input.clone();
            if table.decl.role == FunctionRole::FunctionView {
                sorts.push(table.func_type.output().clone());
            }
            let mut proofs = vec![];
            self.egraph.backend.for_each(table.backend_id, |row| {
                let mut pending = sorts
                    .iter()
                    .cloned()
                    .zip(row.vals.iter().copied())
                    .collect::<Vec<_>>();
                let mut seen = HashSet::default();
                while let Some((sort, value)) = pending.pop() {
                    if !sort.is_container_sort() || !seen.insert((sort.name().to_owned(), value)) {
                        continue;
                    }
                    if wanted.remove(&(sort.name().to_owned(), value)) {
                        proofs.push(row.vals[table.func_type.input.len() + 1]);
                    }
                    pending
                        .extend(sort.inner_values(self.egraph.backend.container_values(), value));
                }
            });
            for proof in proofs {
                self.evidence.insert(proof);
            }
        }
        self.unanchored_container_roots = self
            .roots
            .iter()
            .copied()
            .filter(|id| {
                wanted.contains(&(
                    self.terms.get(*id).sort().name().to_owned(),
                    self.nodes[id].value,
                ))
            })
            .collect();
        Ok(())
    }

    fn compose(self) -> Result<(ProofStore, HashMap<TermId, ProofId>), Error> {
        let mut dag = TermDag::default();
        let sort = self
            .egraph
            .get_sort_by_name(&self.egraph.proof_state.proof_names.proof_datatype)
            .ok_or_else(|| fail("missing proof sort"))?
            .clone();
        let mut extractor = RootExtractor::new();
        let roots = self
            .evidence
            .iter()
            .map(|&value| {
                extractor
                    .extract(self.egraph, &mut dag, value, &sort)
                    .ok_or_else(|| fail("could not materialize existing proof evidence"))
            })
            .collect::<Result<Vec<_>, _>>()?;
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
        let (mut store, evidence) = proof_store_from_terms(
            &self.egraph.proof_state.proof_names,
            dag,
            &roots,
            &self.egraph.proof_check_program,
            normalizers,
            value_heads,
        );
        store
            .remove_globals(&self.egraph.proof_check_program)
            .map_err(|error| fail(error.to_string()))?;
        let actions = gather_global_actions(&self.egraph.proof_check_program).collect::<Vec<_>>();
        let globals = process_actions(
            "global_actions",
            HashMap::default(),
            &actions,
            &mut store.term_dag,
        )
        .map_err(|error| fail(error.to_string()))?;
        let mut composition = Composition {
            lookup: self,
            store,
            evidence,
            row_proofs: HashMap::default(),
            selected: HashMap::default(),
            canonical: HashMap::default(),
            witnesses: HashMap::default(),
            proofs: HashMap::default(),
            certificates_by_terms: HashMap::default(),
            typed_certificates: HashMap::default(),
            container_elements: HashMap::default(),
        };
        composition.name_endpoints(&globals.var_bindings)?;
        composition.type_container_elements()?;
        // Proof syntax is untyped. In particular `(vec-empty)` at one sort is
        // not evidence that the value exists at every other vector sort. Roots
        // with no matching typed view column need a typed source witness.
        if !composition.lookup.unanchored_container_roots.is_empty() {
            let mut source_containers = HashSet::default();
            let mut error = None;
            for action in &actions {
                (*action).clone().visit_exprs(&mut |expr| {
                    if expr.output_type().is_container_sort() {
                        match eval_expr_with_subst(
                            "global_actions",
                            &expr,
                            &mut composition.store.term_dag,
                            &globals.var_bindings,
                        ) {
                            Ok((term, _)) => {
                                source_containers
                                    .insert((expr.output_type().name().to_owned(), term));
                            }
                            Err(err) => error = Some(err),
                        }
                    }
                    expr
                });
            }
            if let Some(error) = error {
                return Err(fail(error.to_string()));
            }
            for &id in &composition.lookup.unanchored_container_roots {
                let node = composition.lookup.terms.get(id);
                let sort = node.sort().name().to_owned();
                if !composition.lookup.roots.iter().any(|root| {
                    composition.lookup.terms.get(*root).sort().name() == sort
                        && (source_containers.contains(&(sort.clone(), composition.selected[root]))
                            || source_containers
                                .contains(&(sort.clone(), composition.canonical[root])))
                }) {
                    return Err(fail(format!(
                        "Could not find term {} in the e-graph",
                        composition.lookup.terms.to_string(id)
                    )));
                }
            }
        }
        composition.collect_anchors();
        // A bare container action can have no enclosing view row. Reuse only
        // propositions actually established by the original source actions.
        for &term in composition
            .selected
            .values()
            .chain(composition.canonical.values())
        {
            if !composition.witnesses.contains_key(&term)
                && globals.propositions.contains(&Proposition::new(term, term))
            {
                let proof = composition.store.push_shared_proof(
                    SynthKey::Fiat(term, term),
                    Proof {
                        proposition: Proposition::new(term, term),
                        justification: Justification::Fiat,
                    },
                );
                composition.witnesses.insert(term, proof);
            }
        }
        // Primitive validators evaluate expressions to proof terms. Their
        // temporary arguments need not themselves be existence claims (for
        // example vec-length(vec-of(a)) proves a literal, not a fresh vector).
        let mut needed = HashSet::default();
        let mut pending = composition.lookup.roots.to_vec();
        pending.extend(composition.lookup.terms.nodes().filter_map(|(id, _)| {
            matches!(
                composition.lookup.nodes[&id].row.map(|r| r.kind),
                Some(RowKind::Constructor)
            )
            .then_some(id)
        }));
        while let Some(id) = pending.pop() {
            if !needed.insert(id) {
                continue;
            }
            let typed = composition.lookup.terms.get(id);
            let constructor = matches!(
                composition.lookup.nodes[&id].row.map(|r| r.kind),
                Some(RowKind::Constructor)
            );
            let rewrite_container = composition.lookup.nodes[&id].row.is_none()
                && typed.sort().is_container_sort()
                && composition.selected[&id] != composition.canonical[&id];
            if (constructor || rewrite_container)
                && let TypedTerm::App(_, children) = typed
            {
                pending.extend(children);
            }
        }
        // Visit the input before the extracted results. Its container proof
        // can provide a canonical witness for a result without an enclosing row.
        let mut order = vec![];
        let mut seen = HashSet::default();
        let mut pending = composition
            .lookup
            .roots
            .iter()
            .rev()
            .map(|&id| (id, false))
            .collect::<Vec<_>>();
        while let Some((id, ready)) = pending.pop() {
            if ready {
                order.push(id);
                continue;
            }
            if !seen.insert(id) {
                continue;
            }
            pending.push((id, true));
            if let TypedTerm::App(_, children) = composition.lookup.terms.get(id) {
                pending.extend(children.iter().rev().map(|&child| (child, false)));
            }
        }
        for id in order {
            if !needed.contains(&id) {
                continue;
            }
            let proof = composition.prove_node(id)?;
            if composition.store.get(proof).lhs() != composition.selected[&id]
                || composition.store.get(proof).rhs() != composition.canonical[&id]
            {
                return Err(fail(
                    "certificate does not connect the requested term to its leader",
                ));
            }
            composition.proofs.insert(id, proof);
            composition.typed_certificates.insert(
                (
                    composition.lookup.terms.get(id).sort().name().to_owned(),
                    composition.selected[&id],
                ),
                proof,
            );
            composition
                .witnesses
                .entry(composition.canonical[&id])
                .or_insert(proof);
            composition.certificates_by_terms.insert(
                (composition.selected[&id], composition.canonical[&id]),
                proof,
            );
        }
        Ok((composition.store, composition.proofs))
    }
}

struct Composition<'a> {
    lookup: Lookup<'a>,
    store: ProofStore,
    evidence: Vec<ProofId>,
    row_proofs: HashMap<TermId, ProofId>,
    selected: HashMap<TermId, TermId>,
    canonical: HashMap<TermId, TermId>,
    witnesses: HashMap<TermId, ProofId>,
    proofs: HashMap<TermId, ProofId>,
    certificates_by_terms: HashMap<(TermId, TermId), ProofId>,
    typed_certificates: HashMap<(String, TermId), ProofId>,
    container_elements: HashMap<TermId, Vec<(String, TermId)>>,
}

impl Composition<'_> {
    // These are names for proof endpoints, not new e-graph terms. Constructor
    // leaders are named by existing view/UF proofs; container leaders are the
    // normalized containers of those same element witnesses.
    fn name_endpoints(&mut self, globals: &HashMap<String, TermId>) -> Result<(), Error> {
        for (id, typed) in self.lookup.terms.nodes() {
            let node = &self.lookup.nodes[&id];
            let row_proof = node.row.as_ref().map(|row| {
                let proof = self.evidence[row.proof];
                match row.kind {
                    RowKind::Output(column) => self.store.push_projection(proof, column),
                    _ => proof,
                }
            });
            if let Some(proof) = row_proof {
                self.row_proofs.insert(id, proof);
            }
            let children = match typed {
                TypedTerm::Var(never) => match *never {},
                TypedTerm::Lit(_) => &[][..],
                TypedTerm::App(_, children) => children.as_slice(),
            };
            let selected_children = children
                .iter()
                .map(|child| self.selected[child])
                .collect::<Vec<_>>();
            let canonical_children = children
                .iter()
                .map(|child| self.canonical[child])
                .collect::<Vec<_>>();
            let (selected, fallback_canonical) = match typed {
                TypedTerm::Lit(literal) => {
                    let term = self.store.term_dag.lit(literal.clone());
                    (term, term)
                }
                TypedTerm::App(ResolvedCall::Primitive(primitive), _) => {
                    let validator = primitive.validator().unwrap();
                    let selected = validator(&mut self.store.term_dag, &selected_children)
                        .ok_or_else(|| fail(format!("cannot validate {}", primitive.name())))?;
                    let canonical = validator(&mut self.store.term_dag, &canonical_children)
                        .ok_or_else(|| {
                            fail(format!(
                                "cannot validate {} at leader arguments",
                                primitive.name()
                            ))
                        })?;
                    (selected, canonical)
                }
                TypedTerm::App(ResolvedCall::Func(function), _) => {
                    let selected = if function.role.is_global() {
                        *globals.get(&function.name).ok_or_else(|| {
                            fail(format!("missing source definition for {}", function.name))
                        })?
                    } else if matches!(
                        node.row.as_ref().map(|row| row.kind),
                        Some(RowKind::Output(_))
                    ) {
                        self.store.get(row_proof.unwrap()).rhs()
                    } else {
                        self.store
                            .term_dag
                            .app(function.name.clone(), selected_children)
                    };
                    let canonical = match row_proof {
                        Some(proof) => self.store.get(proof).lhs(),
                        None if !typed.sort().is_eq_sort() && !typed.sort().is_container_sort() => {
                            typed.sort().reconstruct_termdag_base(
                                self.lookup.egraph.backend.base_values(),
                                node.value,
                                &mut self.store.term_dag,
                            )
                        }
                        _ => return Err(fail("a nonliteral value needs existing proof evidence")),
                    };
                    (selected, canonical)
                }
                _ => return Err(fail("unsupported ground term")),
            };
            let canonical = node
                .row
                .as_ref()
                .and_then(|row| row.union)
                .map(|union| self.store.get(self.evidence[union]).rhs())
                .unwrap_or(fallback_canonical);
            self.selected.insert(id, selected);
            self.canonical.insert(id, canonical);
        }
        Ok(())
    }

    /// Record the element sorts of the evaluated container terms.
    fn type_container_elements(&mut self) -> Result<(), Error> {
        let containers = self
            .lookup
            .terms
            .nodes()
            .filter_map(|(id, node)| node.sort().is_container_sort().then_some(id))
            .collect::<Vec<_>>();
        if containers.is_empty() {
            return Ok(());
        }
        let roots = containers
            .iter()
            .map(|id| (self.selected[id], Some(self.lookup.terms.get(*id).sort())))
            .collect::<Vec<_>>();
        let (forms, typed_roots) = self
            .lookup
            .egraph
            .type_info
            .source_types()
            .typecheck_term_dag(&self.store.term_dag, &roots, Context::Read)
            .map_err(|error| fail(error.to_string()))?;
        for (&id, &root) in containers.iter().zip(&typed_roots) {
            let (TypedTerm::App(_, typed_children), Term::App(_, children)) =
                (forms.get(root), self.store.term_dag.get(self.selected[&id]))
            else {
                return Err(fail("container result is not an application"));
            };
            self.container_elements.insert(
                id,
                typed_children
                    .iter()
                    .zip(children)
                    .map(|(&typed, &term)| (forms.get(typed).sort().name().to_owned(), term))
                    .collect(),
            );
        }
        Ok(())
    }

    fn collect_anchors(&mut self) {
        // Every endpoint of an existing proof, and every subterm projected
        // from it, is an existence witness. Include the dependencies too: a
        // container rebuild may have normalized away part of the original term.
        // Eval is only a side-condition marker and proves no proposition alone.
        let existing = self
            .store
            .id_to_proof
            .iter()
            .filter(|(_, proof)| !matches!(proof.justification, Justification::Eval))
            .map(|(id, proof)| (id, proof.lhs(), proof.rhs()))
            .collect::<Vec<_>>();
        let mut pending = vec![];
        for (proof, left, right) in existing {
            self.certificates_by_terms
                .entry((left, right))
                .or_insert(proof);
            pending.push((right, proof));
            if left != right {
                let back = self.store.sym(proof);
                self.certificates_by_terms
                    .entry((right, left))
                    .or_insert(back);
                pending.push((left, back));
            }
        }
        while let Some((term, proof)) = pending.pop() {
            if self.witnesses.contains_key(&term) {
                continue;
            }
            self.witnesses.insert(term, proof);
            if let Term::App(_, children) = self.store.term_dag.get(term).clone() {
                for (index, child) in children.into_iter().enumerate() {
                    let projected = self.store.push_projection(proof, index);
                    pending.push((child, projected));
                }
            }
        }
    }

    fn prove_node(&mut self, id: TermId) -> Result<ProofId, Error> {
        let typed = self.lookup.terms.get(id);
        if let Some(row) = self.lookup.nodes[&id].row {
            let mut proof = self.row_proofs[&id];
            match row.kind {
                RowKind::Constructor => {
                    let TypedTerm::App(_, children) = typed else {
                        unreachable!()
                    };
                    for (index, child) in children.iter().enumerate() {
                        let step = self.store.sym(self.proofs[child]);
                        proof = self.congr(proof, index, step)?;
                    }
                    proof = self.store.sym(proof);
                }
                RowKind::Global => {
                    if self.store.get(proof).rhs() == self.selected[&id] {
                        proof = self.store.sym(proof);
                    } else if self.store.get(proof).lhs() == self.selected[&id] {
                        let back = self.store.sym(proof);
                        proof = self.store.trans(proof, back);
                    } else if let Some(&connector) = self
                        .certificates_by_terms
                        .get(&(self.selected[&id], self.store.get(proof).lhs()))
                    {
                        proof = connector;
                    } else {
                        return Err(fail(
                            "global evidence no longer names its source definition",
                        ));
                    }
                }
                RowKind::Output(_) => {}
            }
            if let Some(union) = row.union {
                let edge = self.evidence[union];
                if self.store.get(proof).rhs() != self.store.get(edge).lhs() {
                    return Err(fail("union evidence does not connect to the view witness"));
                }
                proof = self.store.trans(proof, edge);
            }
            return Ok(proof);
        }
        let endpoints = (self.selected[&id], self.canonical[&id]);
        if let Some(&proof) = self.certificates_by_terms.get(&endpoints) {
            return Ok(proof);
        }
        if endpoints.0 == endpoints.1
            && let Some(&witness) = self.witnesses.get(&endpoints.0)
        {
            return Ok(self.store.reflexive(witness));
        }
        if typed.sort().is_container_sort() {
            return self.prove_container(id);
        }
        if typed.sort().is_eq_sort() {
            return Err(fail(
                "internal proof lookup error: no proof for an existing element",
            ));
        }
        let term = self.selected[&id];
        if term != self.canonical[&id] || !self.store.reflexive_value_term(term) {
            return Err(fail("primitive value has no valid reflexive proof"));
        }
        Ok(self.store.push_shared_proof(
            SynthKey::Fiat(term, term),
            Proof {
                proposition: Proposition::new(term, term),
                justification: Justification::Fiat,
            },
        ))
    }

    fn prove_container(&mut self, id: TermId) -> Result<ProofId, Error> {
        let forward = self.witnesses.get(&self.selected[&id]).copied();
        let anchor = forward
            .or_else(|| self.witnesses.get(&self.canonical[&id]).copied())
            .ok_or_else(|| {
                fail(format!(
                    "Could not find term {} in the e-graph",
                    self.lookup.terms.to_string(id)
                ))
            })?;
        let mut proof = self.store.reflexive(anchor);
        let Term::App(_, actual) = self.store.term_dag.get(self.store.get(proof).rhs()).clone()
        else {
            return Err(fail("container witness is not an application"));
        };
        let mut targets = self.container_elements[&id]
            .iter()
            .map(|key| {
                let wanted = key.1;
                let certificate = self.typed_certificates.get(key).copied();
                let canonical = certificate
                    .map(|proof| self.store.get(proof).rhs())
                    .unwrap_or(wanted);
                Some((wanted, canonical, certificate))
            })
            .collect::<Vec<_>>();
        for (index, term) in actual.into_iter().enumerate() {
            let target = targets
                .iter_mut()
                .find(|target| {
                    target.is_some_and(|(wanted, canonical, _)| {
                        (if forward.is_some() { wanted } else { canonical }) == term
                    })
                })
                .ok_or_else(|| fail("container witness has incompatible elements"))?;
            let (_, _, certificate) = target.take().unwrap();
            if let Some(step) = certificate {
                let step = if forward.is_some() {
                    step
                } else {
                    self.store.sym(step)
                };
                proof = self.congr(proof, index, step)?;
            }
        }
        proof = self.store.normalize_step(proof);
        Ok(if forward.is_some() {
            proof
        } else {
            self.store.sym(proof)
        })
    }

    fn congr(&mut self, base: ProofId, index: usize, child: ProofId) -> Result<ProofId, Error> {
        if !matches!(self.store.term_dag.get(self.store.get(base).rhs()), Term::App(_, args)
            if args.get(index) == Some(&self.store.get(child).lhs()))
        {
            return Err(fail(
                "view evidence does not match the child's leader witness",
            ));
        }
        Ok(self.store.congr(base, index, child))
    }
}
