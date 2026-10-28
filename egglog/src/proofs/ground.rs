//! Certify ground terms using shared raw proofs and deferred container proofs.
//!
//! Value lookup establishes the existing e-graph values. The evidence builder
//! returns a proof immediately or a container recipe awaiting an existence
//! witness. Parent rows supply those witnesses by projection; container roots
//! use typed view columns or actual source actions.

use std::{cell::OnceCell, iter::once, rc::Rc};

use super::proof_checker::gather_global_actions;
use super::proof_container_rebuild::rebuild_container_value_rec;
use super::proof_extractor::RootExtractor;
use super::proof_format::{ProofId, ProofLifter, ProofStore, Proposition, RawProof, RawProofId};
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
    proof: Value,
    to_leader: Option<Value>,
}

/// A canonical runtime value and the view evidence found by lookup.
struct Node {
    value: Value,
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
        let mut builder = GroundProofs::new(self)?;
        let evidence = builder.build(&typed, values)?;
        let input = builder.root(&evidence[roots[0]], None)?;
        let mut raw_proofs = Vec::with_capacity(outputs.len());
        for &id in &roots[1..] {
            // Lookup has established that all roots have the same sort and value.
            let right = builder.root(&evidence[id], Some(input))?;
            let back = builder.proofs.sym(right);
            raw_proofs.push(builder.trans(input, back)?);
        }
        let proof_ids = raw_proofs
            .into_iter()
            .map(|proof| builder.proofs.lift(proof))
            .collect::<Vec<_>>();
        let mut store = builder.proofs.finish();
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

/// One source term's evaluated meaning and its certificate to the leader.
/// Term IDs belong to the lifter's DAG, not the typed input DAG.
struct TermProof {
    sort: ArcSort,
    term: TermId,
    leader: TermId,
    proof: ProofResult,
}

enum ProofResult {
    /// Proves the enclosing `TermProof`'s `term = leader` equality.
    Ready(RawProofId),
    /// Needs evidence at the container's sort before it can prove that equality.
    NeedsWitness(ContainerProof),
}

/// A container equality waiting for evidence that one of its endpoints exists.
/// Element occurrences are retained individually, including equal elements.
struct ContainerProof {
    elements: Vec<Rc<TermProof>>,
    completed: OnceCell<RawProofId>,
}

impl TermProof {
    fn ready(&self) -> Option<RawProofId> {
        match &self.proof {
            ProofResult::Ready(proof) => Some(*proof),
            ProofResult::NeedsWitness(recipe) => recipe.completed.get().copied(),
        }
    }
}

struct TermEvidence {
    value: Value,
    proof: Rc<TermProof>,
}

/// Certifies ground terms using existing rows and source actions.
struct GroundProofs<'a> {
    egraph: &'a EGraph,
    proofs: ProofLifter<'a>,
    extractor: RootExtractor,
    /// Memoized evidence for evaluated terms, with sorts distinguishing overloads.
    terms: HashMap<(String, TermId), Rc<TermProof>>,
}

impl<'a> GroundProofs<'a> {
    fn new(egraph: &'a EGraph) -> Result<Self, Error> {
        let normalizers = egraph
            .type_info
            .sorts
            .values()
            .filter_map(|sort| sort.rebuild_container_normalizer())
            .collect();
        let mut value_heads = HashSet::default();
        for sort in egraph.type_info.sorts.values() {
            if let Some(head) = sort.prim_value_constructor() {
                if egraph.type_info.get_prims(&head).map_or(0, <[_]>::len) != 1 {
                    return Err(fail(format!(
                        "ambiguous primitive value constructor {head}"
                    )));
                }
                value_heads.insert(head);
            }
        }
        Ok(Self {
            egraph,
            proofs: ProofLifter::new(
                &egraph.proof_state.proof_names,
                &egraph.proof_check_program,
                normalizers,
                value_heads,
            ),
            extractor: RootExtractor::new(),
            terms: HashMap::default(),
        })
    }

    fn import(&mut self, value: Value) -> Result<RawProofId, Error> {
        let sort = self
            .egraph
            .get_sort_by_name(&self.egraph.proof_state.proof_names.proof_datatype)
            .ok_or_else(|| fail("missing proof sort"))?
            .clone();
        let term = self
            .extractor
            .extract(self.egraph, self.proofs.terms_mut(), value, &sort)
            .ok_or_else(|| fail("could not materialize existing proof evidence"))?;
        Ok(self.proofs.parse(term))
    }

    /// Return evidence in typed-node order. `values` must come from lookup of
    /// the same DAG. Container evidence may still need an existence witness.
    fn build(
        &mut self,
        terms: &TypedTermDag,
        values: Vec<Node>,
    ) -> Result<Vec<TermEvidence>, Error> {
        let mut results: Vec<TermEvidence> = Vec::with_capacity(terms.size());
        for ((_, typed), value) in terms.nodes().zip(values) {
            let sort = typed.sort();
            let children = match typed {
                TypedTerm::App(_, children) => children
                    .iter()
                    .map(|&id| results[id].proof.clone())
                    .collect::<Vec<_>>(),
                _ => vec![],
            };
            let selected = match typed {
                TypedTerm::Lit(literal) => self.proofs.terms_mut().lit(literal.clone()),
                TypedTerm::App(ResolvedCall::Primitive(primitive), _) => {
                    let arguments = children.iter().map(|child| child.term).collect::<Vec<_>>();
                    primitive.validator().unwrap()(self.proofs.terms_mut(), &arguments)
                        .ok_or_else(|| fail(format!("cannot validate {}", primitive.name())))?
                }
                TypedTerm::App(ResolvedCall::Func(function), _) if function.role.is_global() => {
                    *self
                        .proofs
                        .source
                        .var_bindings
                        .get(&function.name)
                        .ok_or_else(|| {
                            fail(format!("missing source definition for {}", function.name))
                        })?
                }
                TypedTerm::App(ResolvedCall::Func(function), _) => self.proofs.terms_mut().app(
                    function.name.clone(),
                    children.iter().map(|child| child.term).collect(),
                ),
                _ => return Err(fail("unsupported ground term")),
            };
            let proof = if let Some(row) = value.row {
                let row_proof = self.import(row.proof)?;
                let mut proof = match row.kind {
                    RowKind::Constructor => {
                        let mut proof = row_proof;
                        for (index, child) in children.iter().enumerate() {
                            let witness = self.proofs.project(row_proof, index);
                            let child = self.complete(child, Some(witness))?;
                            let back = self.proofs.sym(child);
                            proof = self.congr(proof, index, back)?;
                        }
                        self.proofs.sym(proof)
                    }
                    RowKind::Output(column) => self.proofs.project(row_proof, column),
                    RowKind::Global => {
                        let prop = self.proofs.proposition(row_proof);
                        if prop.rhs() == selected {
                            self.proofs.sym(row_proof)
                        } else if prop.lhs() == selected {
                            let back = self.proofs.sym(row_proof);
                            self.proofs.trans(row_proof, back)
                        } else {
                            self.proofs
                                .equality(&Proposition::new(selected, prop.lhs()))
                                .ok_or_else(|| {
                                    fail("global evidence no longer names its source definition")
                                })?
                        }
                    }
                };
                if let Some(to_leader) = row.to_leader {
                    let edge = self.import(to_leader)?;
                    proof = self.trans(proof, edge)?;
                }
                let prop = self.proofs.proposition(proof);
                if !matches!(row.kind, RowKind::Output(_)) && prop.lhs() != selected {
                    return Err(fail("view evidence does not prove the requested term"));
                }
                Rc::new(TermProof {
                    sort,
                    term: prop.lhs(),
                    leader: prop.rhs(),
                    proof: ProofResult::Ready(proof),
                })
            } else {
                self.for_term(selected, sort)?
            };
            if let TypedTerm::App(ResolvedCall::Primitive(primitive), _) = typed {
                let arguments = children
                    .iter()
                    .map(|child| child.leader)
                    .collect::<Vec<_>>();
                let leader = primitive.validator().unwrap()(self.proofs.terms_mut(), &arguments)
                    .ok_or_else(|| {
                        fail(format!(
                            "cannot validate {} at leader arguments",
                            primitive.name()
                        ))
                    })?;
                if proof.leader != leader {
                    return Err(fail("primitive certificate does not reach its leader"));
                }
            }
            self.terms
                .insert((proof.sort.name().to_owned(), proof.term), proof.clone());
            results.push(TermEvidence {
                value: value.value,
                proof,
            });
        }
        Ok(results)
    }

    /// Resolve the evaluated result of a primitive. Its elements need not be
    /// the primitive's syntactic arguments, as with set-intersect or vec-get.
    fn for_term(&mut self, term: TermId, sort: ArcSort) -> Result<Rc<TermProof>, Error> {
        let key = (sort.name().to_owned(), term);
        if let Some(proof) = self.terms.get(&key) {
            return Ok(proof.clone());
        }
        let (leader, proof) = if sort.is_container_sort() {
            let (typed, roots) = self
                .egraph
                .type_info
                .source_types()
                .typecheck_term_dag(
                    self.proofs.terms(),
                    &[(term, Some(sort.clone()))],
                    Context::Read,
                )
                .map_err(|error| fail(error.to_string()))?;
            let TypedTerm::App(ResolvedCall::Primitive(constructor), typed_children) =
                typed.get(roots[0])
            else {
                return Err(fail("container result is not an application"));
            };
            let Term::App(_, children) = self.proofs.terms().get(term).clone() else {
                unreachable!()
            };
            let elements = children
                .iter()
                .zip(typed_children)
                .map(|(&term, &typed_child)| self.for_term(term, typed.get(typed_child).sort()))
                .collect::<Result<Vec<_>, _>>()?;
            let canonical = elements
                .iter()
                .map(|child| child.leader)
                .collect::<Vec<_>>();
            let leader = constructor.validator().unwrap()(self.proofs.terms_mut(), &canonical)
                .ok_or_else(|| fail("cannot normalize container elements"))?;
            (
                leader,
                ProofResult::NeedsWitness(ContainerProof {
                    elements,
                    completed: OnceCell::new(),
                }),
            )
        } else if self.proofs.is_value(term) {
            (
                term,
                ProofResult::Ready(self.proofs.add(RawProof::Fiat(term, term))),
            )
        } else {
            let witness = self.proofs.witness(term).ok_or_else(|| {
                fail("internal proof lookup error: no proof for an existing element")
            })?;
            (term, ProofResult::Ready(self.proofs.reflexive(witness)))
        };
        let result = Rc::new(TermProof {
            sort,
            term,
            leader,
            proof,
        });
        self.terms.insert(key, result.clone());
        Ok(result)
    }

    /// Complete a container recipe using a witness from its parent or root lookup.
    /// The caller must establish existence at the requested sort.
    /// Only successful completions are memoized, so missing context is not cached.
    fn complete(
        &mut self,
        term: &TermProof,
        witness: Option<RawProofId>,
    ) -> Result<RawProofId, Error> {
        if let Some(proof) = term.ready() {
            return Ok(proof);
        }
        let ProofResult::NeedsWitness(recipe) = &term.proof else {
            unreachable!()
        };
        let mut anchor = witness.filter(|&proof| {
            let endpoint = self.proofs.proposition(proof).rhs();
            endpoint == term.term || endpoint == term.leader
        });
        // Normalization can discard set elements. Reversing a proof from the
        // smaller canonical container cannot recover those occurrences; use
        // the original container recorded in the row's proof dependencies.
        if anchor.is_some_and(|proof| {
            let endpoint = self.proofs.proposition(proof).rhs();
            endpoint != term.term
                && matches!(self.proofs.terms().get(endpoint), Term::App(_, children)
                    if children.len() != recipe.elements.len())
        }) {
            anchor = self.proofs.witness(term.term);
        }
        if anchor.is_none() {
            anchor = self
                .proofs
                .witness(term.term)
                .or_else(|| self.proofs.witness(term.leader));
        }
        let anchor = anchor.ok_or_else(|| self.missing(term.term))?;
        let endpoint = self.proofs.proposition(anchor).rhs();
        let forward = endpoint == term.term;
        if term.term == term.leader {
            let proof = self.proofs.reflexive(anchor);
            let _ = recipe.completed.set(proof);
            return Ok(proof);
        }
        let Term::App(_, actual) = self.proofs.terms().get(endpoint).clone() else {
            return Err(fail("container witness is not an application"));
        };
        let mut targets = recipe.elements.iter().map(Some).collect::<Vec<_>>();
        let mut proof = self.proofs.reflexive(anchor);
        for (index, actual) in actual.into_iter().enumerate() {
            let target = targets
                .iter_mut()
                .find(|candidate| {
                    candidate.is_some_and(|child| {
                        (if forward { child.term } else { child.leader }) == actual
                    })
                })
                .ok_or_else(|| fail("container witness has incompatible elements"))?;
            let child = target.take().unwrap();
            let witness = self.proofs.project(anchor, index);
            let child_proof = self.complete(child, Some(witness))?;
            let step = if forward {
                child_proof
            } else {
                self.proofs.sym(child_proof)
            };
            proof = self.congr(proof, index, step)?;
        }
        proof = self.proofs.normalize(proof);
        if !forward {
            proof = self.proofs.sym(proof);
        }
        if self.proofs.proposition(proof) != Proposition::new(term.term, term.leader) {
            return Err(fail(
                "certificate does not connect the requested term to its leader",
            ));
        }
        let _ = recipe.completed.set(proof);
        Ok(proof)
    }

    fn missing(&self, term: TermId) -> Error {
        fail(format!(
            "Could not find term {} in the e-graph",
            self.proofs.terms().to_string(term)
        ))
    }

    /// Certify a root, looking up typed container evidence when needed.
    /// `equal_root`, if supplied, must certify the same sort and runtime value.
    fn root(
        &mut self,
        evidence: &TermEvidence,
        equal_root: Option<RawProofId>,
    ) -> Result<RawProofId, Error> {
        let term = &evidence.proof;
        if let Some(proof) = term.ready() {
            return Ok(proof);
        }
        if let Some(witness) = equal_root {
            return self.complete(term, Some(witness));
        }
        // A root has no parent row to supply the container's existence. Check
        // typed view columns, including nested containers, before using a witness.
        let mut row_proof = None;
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
                if row_proof.is_some() {
                    return;
                }
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
                    if sort.name() == term.sort.name() && value == evidence.value {
                        row_proof = Some(row.vals[table.func_type.input.len() + 1]);
                        break;
                    }
                    pending
                        .extend(sort.inner_values(self.egraph.backend.container_values(), value));
                }
            });
            if row_proof.is_some() {
                break;
            }
        }
        if let Some(proof) = row_proof {
            self.import(proof)?;
        } else {
            let actions =
                gather_global_actions(&self.egraph.proof_check_program).collect::<Vec<_>>();
            let mut exists = false;
            for action in actions {
                (*action).clone().visit_exprs(&mut |expr| {
                    if expr.output_type().name() == term.sort.name()
                        && let Ok(source) = self.proofs.source_expr(&expr)
                    {
                        exists |= source == term.term || source == term.leader;
                    }
                    expr
                });
            }
            if !exists {
                return Err(self.missing(term.term));
            }
            for endpoint in [term.term, term.leader] {
                if self
                    .proofs
                    .source
                    .propositions
                    .contains(&Proposition::new(endpoint, endpoint))
                {
                    self.proofs.add(RawProof::Fiat(endpoint, endpoint));
                }
            }
        }
        self.complete(term, None)
    }

    fn trans(&mut self, left: RawProofId, right: RawProofId) -> Result<RawProofId, Error> {
        if self.proofs.proposition(left).rhs() != self.proofs.proposition(right).lhs() {
            return Err(fail("proof evidence does not connect at the leader"));
        }
        Ok(self.proofs.trans(left, right))
    }

    fn congr(
        &mut self,
        proof: RawProofId,
        index: usize,
        child: RawProofId,
    ) -> Result<RawProofId, Error> {
        let endpoint = self.proofs.proposition(proof).rhs();
        let child_term = self.proofs.proposition(child).lhs();
        if !matches!(self.proofs.terms().get(endpoint), Term::App(_, args)
            if args.get(index) == Some(&child_term))
        {
            return Err(fail(
                "view evidence does not match the child's leader witness",
            ));
        }
        Ok(self.proofs.congr(proof, index, child))
    }
}
