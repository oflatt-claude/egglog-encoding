//! Typechecking ground syntax without expanding its shared subterms into trees.
//!
//! Sharing in a [`TermDag`] is syntactic: `(vec-empty)` may occur at several
//! sorts. Inference therefore keeps a set of possible result sorts for each
//! term, working from children to parents. A parent selects its children's
//! typings through the ordinary application constraints. Only the selected,
//! unambiguous typings become nodes in the returned [`TypedTermDag`].

use crate::constraint::{Problem, assign};
use crate::core::StringOrEq;
use crate::sort::literal_sort;
use crate::util::{HashMap, HashSet, IndexMap};
use crate::{
    ArcSort, Atom, AtomTerm, Context, ResolvedCall, Term, TermDag, TermId, TypeError, TypeInfo,
};
use egglog_ast::{generic_ast::Literal, span::Span};

/// An index into one [`TypedTermDag`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypedTermId(usize);

/// Ground syntax with each application resolved to a concrete signature.
#[derive(Clone, Debug)]
pub enum TypedTerm {
    Lit(Literal),
    App(ResolvedCall, Vec<TypedTermId>),
}

/// One typing of a syntactic term. Different nodes may have the same
/// [`TermId`], but different sorts or application signatures.
#[derive(Clone, Debug)]
pub struct TypedTermNode {
    term: TermId,
    expression: TypedTerm,
}

impl TypedTermNode {
    pub fn term(&self) -> TermId {
        self.term
    }

    pub fn expression(&self) -> &TypedTerm {
        &self.expression
    }

    pub fn sort(&self) -> ArcSort {
        match &self.expression {
            TypedTerm::Lit(lit) => literal_sort(lit),
            TypedTerm::App(call, _) => call.output().clone(),
        }
    }
}

/// A ground term DAG whose applications have been typechecked in one scope
/// and primitive execution context. Nodes are stored in children-first order.
///
/// Typechecking neither evaluates primitives nor reads or writes function
/// tables. It establishes types, not the existence of the terms in an e-graph.
#[derive(Clone, Debug)]
pub struct TypedTermDag {
    terms: TermDag,
    nodes: Vec<TypedTermNode>,
    roots: Vec<TypedTermId>,
    context: Context,
}

impl TypedTermDag {
    /// Typecheck the reachable ground terms, optionally constraining each
    /// root's sort. The same syntax may be requested at several root sorts.
    /// Unreachable terms do not participate in inference.
    pub fn new(
        types: &TypeInfo,
        terms: &TermDag,
        roots: &[(TermId, Option<ArcSort>)],
        context: Context,
    ) -> Result<Self, GroundTypeError> {
        let order = reachable_terms(terms, roots.iter().map(|(term, _)| *term))?;
        let mut inference = Inference {
            types,
            terms,
            context,
            candidates: HashMap::default(),
            nodes: vec![],
        };
        for term in order {
            let candidates = inference.infer(term)?;
            inference.candidates.insert(term, candidates);
        }
        let mut selected = Vec::with_capacity(roots.len());
        for (term, expected) in roots {
            let candidates = &inference.candidates[term];
            let candidate = match expected {
                Some(sort) => {
                    candidates
                        .get(sort.name())
                        .ok_or_else(|| GroundTypeError::WrongSort {
                            term: *term,
                            expected: sort.name().to_owned(),
                            inferred: candidates.keys().cloned().collect(),
                        })?
                }
                None if candidates.len() == 1 => candidates.values().next().unwrap(),
                None => {
                    return Err(GroundTypeError::Ambiguous {
                        term: *term,
                        sorts: candidates.keys().cloned().collect(),
                    });
                }
            };
            selected.push(candidate.node.clone()?);
        }

        // Inference may have explored unused overloads. Retain only typings
        // selected by the roots, preserving sharing and topological order.
        let mut reachable = HashSet::default();
        let mut pending = selected.clone();
        while let Some(id) = pending.pop() {
            if reachable.insert(id)
                && let TypedTerm::App(_, children) = &inference.nodes[id.0].expression
            {
                pending.extend(children.iter().copied());
            }
        }
        let mut remap = HashMap::default();
        let mut nodes = Vec::with_capacity(reachable.len());
        for (index, mut node) in inference.nodes.into_iter().enumerate() {
            let old = TypedTermId(index);
            if !reachable.contains(&old) {
                continue;
            }
            if let TypedTerm::App(_, children) = &mut node.expression {
                for child in children {
                    *child = remap[child];
                }
            }
            remap.insert(old, TypedTermId(nodes.len()));
            nodes.push(node);
        }
        Ok(Self {
            terms: terms.clone(),
            nodes,
            roots: selected.into_iter().map(|id| remap[&id]).collect(),
            context,
        })
    }

    pub fn terms(&self) -> &TermDag {
        &self.terms
    }

    pub fn get(&self, id: TypedTermId) -> &TypedTermNode {
        &self.nodes[id.0]
    }

    pub fn roots(&self) -> &[TypedTermId] {
        &self.roots
    }

    pub fn context(&self) -> Context {
        self.context
    }

    /// Visit nodes in children-first order.
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = (TypedTermId, &TypedTermNode)> {
        self.nodes
            .iter()
            .enumerate()
            .map(|(i, node)| (TypedTermId(i), node))
    }
}

/// A failure to typecheck ground DAG syntax. Term IDs refer to the input DAG.
#[derive(Clone, Debug, thiserror::Error)]
pub enum GroundTypeError {
    #[error("term {term} is outside the term DAG")]
    InvalidTerm { term: TermId },
    #[error("term {term} contains the variable {name}; expected a ground term")]
    Variable { term: TermId, name: String },
    #[error("term {term} has no valid typing")]
    NoTyping { term: TermId },
    #[error("term {term} has ambiguous typings at sorts {sorts:?}")]
    Ambiguous { term: TermId, sorts: Vec<String> },
    #[error("term {term} must have sort {expected}, but has possible sorts {inferred:?}")]
    WrongSort {
        term: TermId,
        expected: String,
        inferred: Vec<String>,
    },
    #[error("cannot typecheck term {term}: {source}")]
    Type { term: TermId, source: TypeError },
}

struct Candidate {
    sort: ArcSort,
    node: Result<TypedTermId, GroundTypeError>,
}

struct Inference<'a> {
    types: &'a TypeInfo,
    terms: &'a TermDag,
    context: Context,
    candidates: HashMap<TermId, IndexMap<String, Candidate>>,
    nodes: Vec<TypedTermNode>,
}

impl Inference<'_> {
    fn infer(&mut self, term: TermId) -> Result<IndexMap<String, Candidate>, GroundTypeError> {
        let mut result = IndexMap::default();
        let (head, children) = match self.terms.get(term) {
            Term::Lit(lit) => {
                let sort = literal_sort(lit);
                let node = self.push(term, TypedTerm::Lit(lit.clone()));
                result.insert(
                    sort.name().to_owned(),
                    Candidate {
                        sort,
                        node: Ok(node),
                    },
                );
                return Ok(result);
            }
            Term::Var(name) => {
                return Err(GroundTypeError::Variable {
                    term,
                    name: name.clone(),
                });
            }
            Term::App(head, children) => (head, children),
        };
        if self
            .types
            .get_func_type(head)
            .is_some_and(|f| f.is_tuple_output())
        {
            return Err(GroundTypeError::Type {
                term,
                source: TypeError::CannotExtractTupleOutput(head.clone(), Span::Panic),
            });
        }

        // Each argument position has its own variable, even when two positions
        // contain the same TermId. Syntactic sharing does not equate their types.
        let args: Vec<_> = children
            .iter()
            .enumerate()
            .map(|(i, child)| match self.terms.get(*child) {
                Term::Lit(lit) => AtomTerm::Literal(Span::Panic, lit.clone()),
                _ => AtomTerm::Var(Span::Panic, format!("arg-{i}")),
            })
            .chain(std::iter::once(AtomTerm::Var(Span::Panic, "result".into())))
            .collect();
        let atom = Atom {
            span: Span::Panic,
            head: StringOrEq::Head(head.clone()),
            args,
        };
        let constraints = atom
            .get_constraints(self.types, self.context)
            .map_err(|source| GroundTypeError::Type { term, source })?;
        let mut domains: Vec<Vec<ArcSort>> = children
            .iter()
            .map(|child| {
                self.candidates[child]
                    .values()
                    .map(|c| c.sort.clone())
                    .collect()
            })
            .collect();
        let mut outputs: Vec<_> = self.types.sorts.values().cloned().collect();
        outputs.sort_by(|a, b| a.name().cmp(b.name()));
        domains.push(outputs);

        // Reuse the normal solver to propagate each partial signature before
        // branching. Fixed constructor/primitive signatures usually settle the
        // entire application immediately, including polymorphic child syntax.
        let mut pending = vec![constraints];
        let mut signatures = HashSet::default();
        let mut last_error = None;
        while let Some(constraints) = pending.pop() {
            let assignment = match (Problem {
                constraints: constraints.clone(),
                range: HashSet::default(),
            })
            .solve(|sort: &ArcSort| sort.name())
            {
                Ok(assignment) => assignment,
                Err(error) => {
                    last_error = Some(error.to_type_error());
                    continue;
                }
            };
            if atom.args.iter().zip(&domains).any(|(arg, domain)| {
                assignment
                    .get(arg)
                    .is_some_and(|sort| !domain.iter().any(|s| s.name() == sort.name()))
            }) {
                continue;
            }
            if let Some((arg, domain)) = atom
                .args
                .iter()
                .zip(&domains)
                .filter(|(arg, _)| assignment.get(arg).is_none())
                .min_by_key(|(_, domain)| domain.len())
            {
                for sort in domain.iter().rev() {
                    let mut branch = constraints.clone();
                    branch.push(assign(arg.clone(), sort.clone()));
                    pending.push(branch);
                }
                continue;
            }
            let signature: Vec<_> = atom
                .args
                .iter()
                .map(|arg| assignment.get(arg).unwrap().clone())
                .collect();
            if !signatures.insert(
                signature
                    .iter()
                    .map(|s| s.name().to_owned())
                    .collect::<Vec<_>>(),
            ) {
                continue;
            }
            let sort = signature.last().unwrap().clone();
            if let Some(previous) = result.get_mut(sort.name()) {
                previous.node = Err(GroundTypeError::Ambiguous {
                    term,
                    sorts: vec![sort.name().to_owned()],
                });
                continue;
            }
            let node = ResolvedCall::from_resolution(
                head,
                &signature,
                self.types,
                self.context,
                &Span::Panic,
            )
            .map_err(|source| GroundTypeError::Type { term, source })
            .and_then(|call| {
                let children = children
                    .iter()
                    .zip(&signature)
                    .map(|(child, sort)| self.candidates[child][sort.name()].node.clone())
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.push(term, TypedTerm::App(call, children)))
            });
            result.insert(sort.name().to_owned(), Candidate { sort, node });
        }
        if result.is_empty() {
            return Err(match last_error {
                Some(source) => GroundTypeError::Type { term, source },
                None => GroundTypeError::NoTyping { term },
            });
        }
        Ok(result)
    }

    fn push(&mut self, term: TermId, expression: TypedTerm) -> TypedTermId {
        let id = TypedTermId(self.nodes.len());
        self.nodes.push(TypedTermNode { term, expression });
        id
    }
}

fn reachable_terms(
    terms: &TermDag,
    roots: impl Iterator<Item = TermId>,
) -> Result<Vec<TermId>, GroundTypeError> {
    let mut seen = HashSet::default();
    let mut pending: Vec<_> = roots.collect();
    while let Some(term) = pending.pop() {
        if term >= terms.size() {
            return Err(GroundTypeError::InvalidTerm { term });
        }
        if seen.insert(term)
            && let Term::App(_, children) = terms.get(term)
        {
            // TermDag normally interns children before parents. Validate this
            // here because its public app method also accepts arbitrary IDs.
            for &child in children {
                if child >= term {
                    return Err(GroundTypeError::InvalidTerm { term: child });
                }
                pending.push(child);
            }
        }
    }
    let mut order: Vec<_> = seen.into_iter().collect();
    order.sort_unstable();
    Ok(order)
}
