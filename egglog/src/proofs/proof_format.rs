use crate::{
    ResolvedCall, Term, TermDag, TermId,
    ast::{
        FunctionSubtype, GenericNCommand, ResolvedExpr, ResolvedFact, ResolvedNCommand,
        ResolvedRule,
    },
    proofs::{
        proof_checker::{
            ProofCheckError, ProofCheckErrorKind, eval_expr_with_subst, gather_globals,
            process_actions, run_merge,
        },
        proof_encoding_helpers::{EncodingNames, SharedEnd},
        proof_head::{Firing, HeadPlan, congr, sites_needed, sym, trans},
        proof_sites::{SiteIndex, SiteRef},
    },
    typechecking::{FuncType, PrimitiveValidator},
    util::{HashMap, HashSet, IEntry, IndexMap, IndexSet, SymbolGen},
};
use egglog_ast::generic_ast::Literal;
use egglog_numeric_id::{DenseIdMap, NumericId, define_id};
use std::{fmt, rc::Rc};

/// The rule the proof names, which the encoder guarantees is in the program.
fn rule_named<'a>(prog: &'a [ResolvedNCommand], rule_name: &str) -> &'a ResolvedRule {
    prog.iter()
        .find_map(|cmd| match cmd {
            ResolvedNCommand::NormRule { rule } if rule.name == rule_name => Some(rule),
            _ => None,
        })
        .unwrap_or_else(|| panic!("could not find rule with name {rule_name}"))
}

define_id!(
    RawProofId,
    u32,
    "An identifier for a proof in a RawProofStore"
);
define_id!(pub ProofId, u32, "An identifier for a proof in a ProofStore");

impl fmt::Display for ProofId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.index())
    }
}

/// Find the subexpression at pre-order position `idx` in `expr`'s tree (index 0
/// is `expr` itself). Must mirror the indexing the proof encoder uses to tag
/// `MergeFnIdx` proofs.
fn subexpr_at_index(expr: &ResolvedExpr, idx: usize) -> Option<&ResolvedExpr> {
    let mut counter = 0;
    fn walk<'a>(
        expr: &'a ResolvedExpr,
        target: usize,
        counter: &mut usize,
    ) -> Option<&'a ResolvedExpr> {
        if *counter == target {
            return Some(expr);
        }
        *counter += 1;
        if let ResolvedExpr::Call(_, _, args) = expr {
            for arg in args {
                if let Some(found) = walk(arg, target, counter) {
                    return Some(found);
                }
            }
        }
        None
    }
    walk(expr, idx, &mut counter)
}

/// Run subexpression `idx` of a function's merge body with `old`/`new` bound to
/// `old_term`/`new_term`, returning the resulting term. `idx` is a pre-order
/// index over the merge body tree (see [`subexpr_at_index`]); `idx == 0` is the
/// whole body. Evaluating the subexpression reconstructs the term the FD
/// custom-function view merge minted at that position, so each nested
/// merge-body subexpression yields its own conclusion. Used when converting a
/// `MergeFnIdx` raw proof into its `MergeFn` conclusion.
fn run_merge_subexpr(
    term_dag: &mut TermDag,
    func_name: &str,
    prog: &[ResolvedNCommand],
    old_term: TermId,
    new_term: TermId,
    idx: usize,
) -> Result<(TermId, HashSet<Proposition>), ProofCheckError> {
    let mut subst = HashMap::default();
    subst.insert("old".to_string(), old_term);
    subst.insert("new".to_string(), new_term);
    for cmd in prog {
        if let GenericNCommand::Function(func_decl) = cmd
            && func_decl.name == func_name
        {
            let merge = func_decl.merge.as_ref().ok_or_else(|| {
                ProofCheckError::from(ProofCheckErrorKind::FunctionNotFound {
                    function_name: func_name.to_string(),
                })
            })?;
            let subexpr = subexpr_at_index(&merge.result, idx).ok_or_else(|| {
                ProofCheckError::from(ProofCheckErrorKind::FunctionNotFound {
                    function_name: format!("{func_name} (merge subexpr index {idx} out of range)"),
                })
            })?;
            return eval_expr_with_subst("merge_function", subexpr, term_dag, &subst);
        }
    }
    Err(ProofCheckErrorKind::FunctionNotFound {
        function_name: func_name.to_string(),
    }
    .into())
}

/// A rule proof's columns, gathered across the chain of conclusion sites it is
/// the last of.
struct RuleColumns {
    name: String,
    /// One per body fact of the rule.
    premises: Vec<TermId>,
    /// One per subterm the head interned before this site, in construction order.
    bridges: Vec<TermId>,
    /// The conclusion site of the row asked about, as an `i64` term
    /// ([`SiteRef::encode`]); the rows further down the chain state earlier sites.
    site: TermId,
}

/// A proof straight from the e-graph, not exposed to users.
struct RawProofStore {
    term_dag: TermDag,
    /// The proof constructor names, used to recognize each extracted proof
    /// term's head by exact match (rather than substring guessing).
    names: EncodingNames,
    /// Bidirectional map between proof terms and their ids.
    store: IndexSet<RawProof>,
    term_to_proof: HashMap<TermId, RawProofId>,
    proof_to_term: HashMap<RawProofId, TermId>,
}

pub(crate) fn proof_store_from_term(
    encoding_names: &EncodingNames,
    term_dag: TermDag,
    proof_term: TermId,
    prog: &Vec<ResolvedNCommand>,
    container_normalizers: HashMap<String, PrimitiveValidator>,
    prim_value_constructors: HashSet<String>,
) -> (ProofStore, ProofId) {
    let (raw_store, raw_proof_id) =
        RawProofStore::from_extracted(encoding_names, term_dag, proof_term);
    ProofStore::from_raw(
        prog,
        raw_store,
        raw_proof_id,
        container_normalizers,
        prim_value_constructors,
    )
}

/// Justifies a single grounded equality t1 = t2.
/// Corresponds closely to the proof header in [`proof_encoding_helpers.rs`](crate::proofs::proof_encoding_helpers).
/// Compared to [`Proof`], a [`RawProof`] leaves out the implicit [`Proposition`] being proven (in some cases) and
/// leaves off the implicit rule substitution.
/// Converting to a [`Proof`] with [`ProofStore::from_raw`] fills in these details.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum RawProof {
    /// Equalities added at the top level are justified by fiat.
    Fiat(TermId, TermId),
    /// Given a rule name and proofs for each premise, produces a proof of a
    /// grounded equality from the head of the rule. The substitution is implicit —
    /// in [`Justification::Rule`] it is explicit.
    ///
    /// The second list holds one *bridge* premise per subterm the head interned —
    /// the view-row proof that says which e-class it landed in — in construction
    /// order. The site names which of the head's conclusions the proof is about
    /// and which of that site's propositions it states ([`SiteRef::encode`]);
    /// conversion derives the equality from those and the bridges, so the row
    /// stores no terms.
    Rule(String, Vec<RawProofId>, Vec<RawProofId>, i64),
    /// A term-free merge proof: given proofs `f(…, old) = f(…, old)` and
    /// `f(…, new) = f(…, new)`, the index `idx` identifies which subexpression of the
    /// merge body this justifies (a pre-order index over the body tree). The
    /// conclusion is reconstructed during conversion by evaluating subexpression
    /// `idx` on the premise outputs; the index distinguishes nested subexpressions
    /// that share the same premises. Used by the FD custom-function view merge, which
    /// runs without access to children.
    MergeFnIdx(String, RawProofId, RawProofId, usize),
    /// Like [`RawProof::MergeFnIdx`] but for the FD view row (no index). The conclusion
    /// `f(children) = eval(whole merge body)` is reconstructed during conversion by
    /// running the whole body on the two premise outputs. Used as the proof column of
    /// every FD pair-valued view's `:merge`.
    MergeFnRow(String, RawProofId, RawProofId),
    Trans(RawProofId, RawProofId),
    Sym(RawProofId),
    /// given a proof that t1 = f(..., ci, ...)
    /// and the child index i of ci in the term f(..., ci, ...)
    /// and a proof that ci = c2,
    /// produces a justification that t1 = f(..., c2, ...)
    Congr(RawProofId, usize, RawProofId),
    /// Given a proof that `t1 = c` and a child proof `a = b`, produces a
    /// justification that `t1 = c'` where every child of `c` equal to `a` is
    /// replaced by `b`. Minted by container rebuilds, which see elements in
    /// value order rather than the term form's canonical child order.
    /// Desugared by [`ProofStore::from_raw`] into positional
    /// [`Justification::Congr`] steps computed against the actual term.
    CongrAll(RawProofId, RawProofId),
    /// One firing of a view's rebuild rule, packing the composition it justifies
    /// into a single row. Expanded by [`ProofStore::expand_rebuild`].
    Rebuild {
        /// The view row as it stood, `old_eclass = f(old_0 … old_{n-1})`.
        row: RawProofId,
        /// Per canonicalized child column, its position in the row's term and a
        /// proof `old_j = new_j`, in ascending position.
        steps: Vec<(usize, RawProofId)>,
        /// `old_eclass = new_eclass`, when the view's output is an e-class. It
        /// composes on the left rather than at a child position, so it is a
        /// field of its own: an e-class can legitimately equal one of its own
        /// children's terms.
        eclass: Option<RawProofId>,
    },
    /// The `@UF` edge one merge collision displaces, packing the composition it
    /// justifies into a single row. Expanded by
    /// [`ProofStore::expand_displaced`].
    Displaced {
        /// The larger side's carried proof.
        hi: RawProofId,
        /// The smaller side's carried proof, the side the edge now points at.
        lo: RawProofId,
        /// Which endpoint the two carried proofs have in common, hence which of
        /// them the composition reverses.
        shared: SharedEnd,
    },
    /// Given a proof that `t1 = c` for a container term `c`, produces a proof of
    /// `t1 = normalize(c)` — the container's canonicalization (reorder/dedup/
    /// merge), which a structural `Congr` chain can't express.
    ContainerNormalize(RawProofId),
    /// Marks the proof of a container side condition (a container-producing
    /// primitive applied in a rule body). It carries nothing: the side condition
    /// is re-evaluated against the rule body when checked (see
    /// `check_side_condition`), so the proof needs no term.
    Eval,
}

/// A [`ProofStore`] is similar to a [`TermDag`].
/// It's a hash-consed arena enabling proofs to share sub-proofs.
/// We refer to proofs with a [`ProofId`] which is an index into the store, used with [`ProofStore::get`] to retrieve the proof.
#[derive(Clone)]
pub struct ProofStore {
    pub(super) term_dag: TermDag,
    proof_id: HashMap<RawProof, ProofId>,
    pub(super) id_to_proof: DenseIdMap<ProofId, Proof>,
    /// Container constructor head -> its validator (the container's term
    /// normalizer), used by [`ProofStore::normalize_container`].
    container_normalizers: HashMap<String, PrimitiveValidator>,
    /// Canonical value-term heads for base sorts whose values termify as
    /// applications (see `Sort::prim_value_constructor`). A term built from one of
    /// these heads over literals is a self-evident value, so the checker accepts a
    /// reflexive `Fiat` over it ([`ProofStore::reflexive_value_term`]).
    pub(super) prim_value_constructors: HashSet<String>,
    /// Rule name -> how its head lowers.
    head_plans: HashMap<String, Rc<HeadPlan>>,
    /// Structural sharing for the proofs conversion synthesizes.
    synthesized: HashMap<SynthKey, ProofId>,
}

/// What a synthesized proof is, for sharing one node per distinct value.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum SynthKey {
    /// A rule head's own conclusion: the rule, which of its sites, and the
    /// premises that fix the substitution.
    Rule(String, SiteRef, Vec<ProofId>),
    Sym(ProofId),
    Trans(ProofId, ProofId),
    Congr(ProofId, usize, ProofId),
}

impl fmt::Debug for ProofStore {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `container_normalizers` holds closures (not `Debug`); show its heads.
        f.debug_struct("ProofStore")
            .field("term_dag", &self.term_dag)
            .field("proof_id", &self.proof_id)
            .field("id_to_proof", &self.id_to_proof)
            .field(
                "container_normalizers",
                &self.container_normalizers.keys().collect::<Vec<_>>(),
            )
            .finish()
    }
}

/// In egglog, all proofs prove a [`Proposition`], which is an equality between two terms.
/// An egglog e-graph is a partial equality relation, closed under symmetry, transitivity, and congruence.
///
/// Note that egglog does not assume reflexivity! For a term t, it's not assumed that t = t.
/// Once an egglog action adds a term, for example (Add 1 2), then the equality (Add 1 2) = (Add 1 2) can be proven.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Proposition {
    pub lhs: TermId,
    pub rhs: TermId,
}

impl Proposition {
    /// Create a new proposition representing the equality lhs = rhs.
    pub fn new(lhs: TermId, rhs: TermId) -> Self {
        Proposition { lhs, rhs }
    }

    /// Get the left-hand side of the equality
    pub fn lhs(&self) -> TermId {
        self.lhs
    }

    /// Get the right-hand side of the equality
    pub fn rhs(&self) -> TermId {
        self.rhs
    }
}

/// A proof shows that a [`Proposition`] is true, justified by a [`Justification`].
#[derive(Clone, Debug)]
pub struct Proof {
    pub(super) proposition: Proposition,
    pub(super) justification: Justification,
}

/// Justifies a [`Proposition`] using one of several proof rules.
/// Some justifications are axioms of egglog, like Sym, Trans, and Congr.
/// Other justifications are based on user input, like Fiat, Rule, and MergeFn.
///
/// Compared to [`RawProof`], a [`Justification`] is always paired with the [`Proposition`] being proven (in a [`Proof`]).
/// Additionally, [`Justification::Rule`] includes the explicit substitution mapping variable names to terms,
/// while [`RawProof::Rule`] leaves this implicit.
#[derive(Clone, Debug)]
pub enum Justification {
    /// Equalities added at the top level are justified by fiat.
    /// Primitive reflexive equalities like 2 = 2 are also justified by Fiat.
    /// Reflexivity of equality is not assumed: a proof of `t = t`` must correspond to some `t` added at the top level.
    Fiat,
    /// Proves a grounded equality `t1 = t2` which appears
    /// in the body of a rule given a substitution given proofs
    /// for each premise ([`Fact`]) of the rule.
    /// If the [`Propostion`] proven is a term like `t = t`,
    /// t may be a subexpression of the body of the rule under the substitution.
    ///
    /// A proof for a premise is an equality t1 = t2 that matches the premise under some substitution.
    /// A proof for a premise that doesn't involve equality (i.e. (Add a b)) gives a proof of t1 = t2 where t2 matches the premise.
    /// A proof for a premise about a funciton (= (f a b ...) c) gives a proof (f a b ... c) = (f a b ... c).
    Rule {
        name: String,
        premise_proofs: Vec<ProofId>,
        /// Ordered by where each variable first occurs in the rule body.
        substitution: IndexMap<String, TermId>,
        /// The head conclusion site the [`Proposition`] comes from: replaying the
        /// head under `substitution` and reading this site reproduces it.
        site: SiteRef,
    },
    /// Given two proofs f(c1, c2, ..., old) = f(c1, c2, ..., old) and f(c1, c2, ..., new) = f(c1, c2, ..., new),
    /// proves either:
    /// 1. f(c1, c2, ..., merge_fn) = f(c1, c2, ..., merge_fn) where merge_fn is the merge function of function f applied to old and new, or
    /// 2. t = t where t is a subexpression of the merge function applied to old and new.
    MergeFn {
        function: String,
        old_proof: ProofId,
        new_proof: ProofId,
    },
    /// Given proofs of t1 = t2 and t2 = t3, produces a proof of t1 = t3.
    /// An axiom egglog assumes.
    Trans(ProofId, ProofId),
    /// Given a proof of t1 = t2, produces a proof of t2 = t1.
    /// An axiom egglog assumes.
    Sym(ProofId),
    /// Extends an equality proof with a congruence step.
    /// Given
    /// 1) a `proof` with proposition `t1 = f(..., ci, ...)`
    /// 2) and the `child_index` of `ci` in the term `f(..., ci, ...)`
    /// 3) and a child_proof with proposition ci = c2,
    ///
    /// proves `t1 = f(..., c2, ...)`.
    ///
    /// An axiom egglog assumes.
    Congr {
        proof: ProofId,
        child_index: usize,
        child_proof: ProofId,
    },
    /// Given a `proof` of `t1 = c` for a container term `c`, proves
    /// `t1 = normalize(c)` — the container's canonicalization (sort by
    /// [`TermDag::ast_cmp`]; dedup for sets; last-write-wins for maps). Sound by
    /// the assumption that normalization preserves the container's value; the
    /// checker recomputes it.
    ContainerNormalize { proof: ProofId },
    /// Marks the proof of a container side condition. It proves nothing on its
    /// own; the side condition is re-evaluated against the rule body when the
    /// rule is checked (see `check_side_condition`), which is what establishes
    /// the container's value. The `Proof`'s proposition is a placeholder.
    Eval,
}

impl RawProofStore {
    /// After extracting a proof from the e-graph, convert it to a [`RawProof`].
    pub(crate) fn from_extracted(
        encoding_names: &EncodingNames,
        term_dag: TermDag,
        term: TermId,
    ) -> (Self, RawProofId) {
        let mut store = RawProofStore {
            term_dag: term_dag.clone(),
            names: encoding_names.clone(),
            store: IndexSet::default(),
            term_to_proof: HashMap::default(),
            proof_to_term: HashMap::default(),
        };
        store.parse_nested_first(term);
        let parsed = store.parse_proof(term);
        (store, parsed)
    }

    /// Parse the proofs nested in `term_id` deepest first, on an explicit stack,
    /// visiting them in the order [`Self::parse_proof`] would. It then finds each
    /// one already parsed, so a deep proof does not need a deep call stack.
    fn parse_nested_first(&mut self, term_id: TermId) {
        // `false` means the term's nested proofs still have to be pushed.
        let mut stack = vec![(term_id, false)];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some((id, nested_pushed)) = stack.pop() {
            if nested_pushed {
                self.parse_proof(id);
                continue;
            }
            if !seen.insert(id) {
                continue;
            }
            stack.push((id, true));
            // Reversed, so popping visits them in `parse_proof_inner`'s order.
            stack.extend(
                self.nested_proofs(id)
                    .into_iter()
                    .rev()
                    .map(|nested| (nested, false)),
            );
        }
    }

    /// The proof terms [`Self::parse_proof_inner`] recurses into, in order. A
    /// malformed term reports none, leaving the diagnostic to the parse itself.
    fn nested_proofs(&self, term_id: TermId) -> Vec<TermId> {
        let Term::App(head, args) = self.term_dag.get(term_id) else {
            return vec![];
        };
        let names = &self.names;
        if names.fused_rule_arity(head).is_some() || *head == names.rule_link_constructor {
            let RuleColumns {
                premises, bridges, ..
            } = self.rule_columns(term_id);
            return premises.into_iter().chain(bridges).collect();
        }
        if let Some(shape) = names.rebuild_proof_shape(head)
            && args.len() == shape.columns()
        {
            return std::iter::once(args[0])
                .chain((0..shape.steps).map(|step| args[2 + 2 * step]))
                .chain(shape.eclass.then(|| args[shape.columns() - 1]))
                .collect();
        }
        match args.len() {
            4 if *head == names.merge_fn_idx_constructor => vec![args[1], args[2]],
            3 if *head == names.merge_fn_row_constructor => vec![args[1], args[2]],
            3 if *head == names.congr_constructor => vec![args[0], args[2]],
            2 if *head == names.eq_trans_constructor || *head == names.congr_all_constructor => {
                vec![args[0], args[1]]
            }
            2 if names.displaced_shared_end(head).is_some() => vec![args[0], args[1]],
            1 if *head == names.eq_sym_constructor
                || *head == names.container_normalize_constructor =>
            {
                vec![args[0]]
            }
            _ => vec![],
        }
    }

    /// Read a rule proof's columns, walking the chain of later-site links with a
    /// loop rather than recursion: a head chains one link per conclusion site.
    ///
    /// The premises and the bridges are told apart structurally rather than by
    /// counting: the row ending the chain carries every premise inline, and each
    /// link adds exactly one bridge. The site returned is the outermost row's,
    /// read at the index that row's own asserted arity fixes.
    fn rule_columns(&self, term_id: TermId) -> RuleColumns {
        let mut bridges = vec![];
        let mut site = None;
        let mut cell = term_id;
        loop {
            let Term::App(head, args) = self.term_dag.get(cell) else {
                panic!("expected a rule proof term. Proof parsing assumes valid proofs.");
            };
            if *head == self.names.rule_link_constructor {
                assert!(args.len() == 3, "{head} should have 3 args");
                site.get_or_insert(args[2]);
                bridges.push(args[1]);
                cell = args[0];
                continue;
            }
            let Some(arity) = self.names.fused_rule_arity(head) else {
                panic!(
                    "expected a rule proof constructor, got {head}. Proof parsing assumes valid proofs."
                );
            };
            assert!(
                args.len() == arity + 2,
                "{head} should have {} args",
                arity + 2
            );
            // Recorded newest first, since a subterm's view-row proof is only
            // readable once the subterm is interned.
            bridges.reverse();
            return RuleColumns {
                name: self.parse_string(args[0]),
                premises: args[1..arity + 1].to_vec(),
                bridges,
                site: *site.get_or_insert(args[arity + 1]),
            };
        }
    }

    fn parse_proof(&mut self, term_id: TermId) -> RawProofId {
        if let Some(&proof_id) = self.term_to_proof.get(&term_id) {
            return proof_id;
        }

        let proof_id = self.parse_proof_inner(term_id);
        self.term_to_proof.insert(term_id, proof_id);
        self.proof_to_term.insert(proof_id, term_id);
        proof_id
    }

    fn parse_proof_inner(&mut self, term_id: TermId) -> RawProofId {
        let term = self.term_dag.get(term_id).clone();
        let Term::App(head, args) = term else {
            panic!(
                "Expected proof term to be an app, got {term:?}. Proof parsing assumes valid proofs."
            );
        };

        let proof = if head == self.names.fiat_constructor {
            assert!(args.len() == 2, "fiat constructor should have 2 args");
            RawProof::Fiat(args[0], args[1])
        } else if self.names.fused_rule_arity(&head).is_some()
            || head == self.names.rule_link_constructor
        {
            let RuleColumns {
                name,
                premises,
                bridges,
                site,
            } = self.rule_columns(term_id);
            let premises = premises.iter().map(|arg| self.parse_proof(*arg)).collect();
            let bridges = bridges.iter().map(|arg| self.parse_proof(*arg)).collect();
            RawProof::Rule(name, premises, bridges, self.parse_int(site))
        } else if let Some(shape) = self.names.rebuild_proof_shape(&head) {
            assert!(
                args.len() == shape.columns(),
                "{head} should have {} args",
                shape.columns()
            );
            let row = self.parse_proof(args[0]);
            let steps = (0..shape.steps)
                .map(|step| {
                    (
                        self.parse_index(args[1 + 2 * step]),
                        self.parse_proof(args[2 + 2 * step]),
                    )
                })
                .collect();
            let eclass = shape
                .eclass
                .then(|| self.parse_proof(args[shape.columns() - 1]));
            RawProof::Rebuild { row, steps, eclass }
        } else if head == self.names.merge_fn_idx_constructor {
            assert!(args.len() == 4, "merge-idx constructor should have 4 args");
            let function = self.parse_string(args[0]);
            let old_proof = self.parse_proof(args[1]);
            let new_proof = self.parse_proof(args[2]);
            let idx = self.parse_index(args[3]);
            RawProof::MergeFnIdx(function, old_proof, new_proof, idx)
        } else if head == self.names.merge_fn_row_constructor {
            assert!(args.len() == 3, "merge-row constructor should have 3 args");
            let function = self.parse_string(args[0]);
            let old_proof = self.parse_proof(args[1]);
            let new_proof = self.parse_proof(args[2]);
            RawProof::MergeFnRow(function, old_proof, new_proof)
        } else if let Some(shared) = self.names.displaced_shared_end(&head) {
            assert!(args.len() == 2, "{head} should have 2 args");
            let hi = self.parse_proof(args[0]);
            let lo = self.parse_proof(args[1]);
            RawProof::Displaced { hi, lo, shared }
        } else if head == self.names.eq_trans_constructor {
            assert!(args.len() == 2, "trans constructor should have 2 args");
            let left = self.parse_proof(args[0]);
            let right = self.parse_proof(args[1]);
            RawProof::Trans(left, right)
        } else if head == self.names.eq_sym_constructor {
            assert!(args.len() == 1, "sym constructor should have 1 arg");
            let inner = self.parse_proof(args[0]);
            RawProof::Sym(inner)
        } else if head == self.names.container_normalize_constructor {
            assert!(
                args.len() == 1,
                "container-normalize constructor should have 1 arg"
            );
            let inner = self.parse_proof(args[0]);
            RawProof::ContainerNormalize(inner)
        } else if head == self.names.congr_constructor {
            assert!(args.len() == 3, "congr constructor should have 3 args");
            let proof = self.parse_proof(args[0]);
            let child_index = self.parse_index(args[1]);
            let child_proof = self.parse_proof(args[2]);
            RawProof::Congr(proof, child_index, child_proof)
        } else if head == self.names.congr_all_constructor {
            assert!(args.len() == 2, "congr-all constructor should have 2 args");
            let proof = self.parse_proof(args[0]);
            let child_proof = self.parse_proof(args[1]);
            RawProof::CongrAll(proof, child_proof)
        } else if head == self.names.eval_constructor {
            assert!(args.is_empty(), "eval constructor should have no args");
            RawProof::Eval
        } else {
            panic!("Unrecognized proof term head: {head}. Proof parsing assumes valid proofs.");
        };

        self.add_proof(proof)
    }

    fn parse_string(&self, term_id: TermId) -> String {
        match self.term_dag.get(term_id) {
            Term::Lit(Literal::String(s)) => s.clone(),
            other => panic!(
                "expected string literal in proof term, got {other:?}. Proof parsing expects valid proofs."
            ),
        }
    }

    fn parse_index(&self, term_id: TermId) -> usize {
        match self.term_dag.get(term_id) {
            Term::Lit(Literal::Int(i)) if *i >= 0 => *i as usize,
            other => {
                panic!("expected non-negative integer literal for congruence index, got {other:?}")
            }
        }
    }

    fn parse_int(&self, term_id: TermId) -> i64 {
        match self.term_dag.get(term_id) {
            Term::Lit(Literal::Int(i)) => *i,
            other => panic!("expected integer literal in proof term, got {other:?}"),
        }
    }

    fn add_proof(&mut self, proof: RawProof) -> RawProofId {
        if let Some(id) = self.store.get_index_of(&proof) {
            return RawProofId::from_usize(id);
        }
        self.store.insert(proof);
        RawProofId::from_usize(self.store.len() - 1)
    }

    fn unwrap_ast(&self, term_id: TermId) -> TermId {
        let term = self.term_dag.get(term_id).clone();
        let Term::App(_, args) = term else {
            panic!("expected ast wrapper application");
        };
        assert!(
            args.len() == 1,
            "ast wrapper should have exactly one child, got {}",
            args.len()
        );
        args[0]
    }
}

/// True iff `fact` is a custom-function application fact `(= (f args) v)` (either
/// argument order), for which the checker's proof normal form expects a *reflexive*
/// premise proof. Constructor and plain equality facts are excluded.
fn is_custom_func_fact(fact: &ResolvedFact) -> bool {
    let call = match fact {
        ResolvedFact::Eq(_, ResolvedExpr::Call(_, c, _), ResolvedExpr::Var(..))
        | ResolvedFact::Eq(_, ResolvedExpr::Var(..), ResolvedExpr::Call(_, c, _)) => c,
        _ => return false,
    };
    matches!(call, ResolvedCall::Func(ft) if ft.subtype == FunctionSubtype::Custom)
}

impl ProofStore {
    /// Get the term DAG used by this proof store.
    pub fn term_dag(&self) -> &TermDag {
        &self.term_dag
    }

    /// Recompute a container term's canonical form by applying the constructor
    /// validator registered for its head (the container's own term normalizer).
    /// Non-container terms, and heads with no validator, are returned unchanged.
    pub(super) fn normalize_container(&mut self, term_id: TermId) -> TermId {
        let Term::App(head, args) = self.term_dag.get(term_id).clone() else {
            return term_id;
        };
        let Some(validator) = self.container_normalizers.get(&head).cloned() else {
            return term_id;
        };
        validator(&mut self.term_dag, &args).unwrap_or(term_id)
    }

    /// Get the [`Proof`] with the given id.
    /// Panics if the id is invalid (if it came from another proof store, for example).
    pub fn get(&self, proof_id: ProofId) -> &Proof {
        &self.id_to_proof[proof_id]
    }

    /// Add a proof, sharing one node per distinct `key`. The e-graph
    /// hash-conses its own proof rows, so the proofs conversion rebuilds in their
    /// place must be shared too — otherwise a subproof reached along several paths
    /// becomes a fresh copy per path, and the proof unfolds into a tree.
    pub(super) fn push_shared_proof(&mut self, key: SynthKey, proof: Proof) -> ProofId {
        if let Some(&id) = self.synthesized.get(&key) {
            return id;
        }
        let id = self.id_to_proof.push(proof);
        self.synthesized.insert(key, id);
        id
    }

    /// Get a string representation of the proof with the given id.
    /// The string representation is a pretty-printed s-expression block with
    /// let bindings for sub-proofs and sub-terms.
    pub fn proof_to_string(&self, proof_id: ProofId) -> String {
        let symbol_gen = &mut crate::util::SymbolGen::new("".to_string());
        let mut buffer = String::new();
        symbol_gen.include_zero(true);
        let res = self.print_to_buffer(symbol_gen, proof_id, &mut buffer);
        buffer.push_str(&res);
        buffer
    }

    /// An empty store over `term_dag`.
    fn new(
        term_dag: TermDag,
        container_normalizers: HashMap<String, PrimitiveValidator>,
        prim_value_constructors: HashSet<String>,
    ) -> ProofStore {
        ProofStore {
            term_dag,
            proof_id: HashMap::default(),
            id_to_proof: DenseIdMap::new(),
            container_normalizers,
            prim_value_constructors,
            head_plans: HashMap::default(),
            synthesized: HashMap::default(),
        }
    }

    fn from_raw(
        prog: &Vec<ResolvedNCommand>,
        raw_store: RawProofStore,
        raw_proof_id: RawProofId,
        container_normalizers: HashMap<String, PrimitiveValidator>,
        prim_value_constructors: HashSet<String>,
    ) -> (ProofStore, ProofId) {
        let mut store = ProofStore::new(
            raw_store.term_dag.clone(),
            container_normalizers,
            prim_value_constructors,
        );
        let globals = gather_globals(prog, &mut store.term_dag)
            .unwrap_or_else(|_| panic!("failed to gather globals from program"));

        let proof_id = store.convert_raw_proof(prog, &globals, &raw_store, raw_proof_id);
        (store, proof_id)
    }

    /// Reflexivize a (possibly non-reflexive) proof for use where the checker
    /// requires a reflexive premise (`lhs == rhs`), e.g. a `MergeFn` premise. For
    /// `p : A = B` returns a proof of `B = B` as `Trans(Sym(p), p)`; an already-
    /// reflexive `p` is returned unchanged.
    ///
    /// This handles eq-sort inputs to FD custom functions: rebuild rewrites the
    /// view row's proof into a congruence proof `f(orig) = f(canon)`, and
    /// reflexivizing to its RHS lands both premises on the same canonical view row
    /// so the checker's input-match succeeds.
    fn reflexivize_premise(&mut self, premise_id: ProofId) -> ProofId {
        let prop = self.id_to_proof[premise_id].proposition.clone();
        if prop.lhs == prop.rhs {
            return premise_id;
        }
        // Sym(p) : rhs = lhs
        let sym_id = self.id_to_proof.push(Proof {
            proposition: Proposition::new(prop.rhs, prop.lhs),
            justification: Justification::Sym(premise_id),
        });
        // Trans(Sym(p), p) : rhs = rhs
        self.id_to_proof.push(Proof {
            proposition: Proposition::new(prop.rhs, prop.rhs),
            justification: Justification::Trans(sym_id, premise_id),
        })
    }

    /// The two `MergeFn*` premise proofs end (rhs) at the colliding view terms
    /// `f(inputs.., output)`. Extract the view head, the shared input args,
    /// and the two output values from the premises' rhs (read before reflexivizing).
    fn merge_premise_view(
        &self,
        old_proof_id: ProofId,
        new_proof_id: ProofId,
    ) -> (String, Vec<TermId>, TermId, TermId) {
        let old_view = self.id_to_proof[old_proof_id].rhs();
        let new_view = self.id_to_proof[new_proof_id].rhs();
        match (self.term_dag.get(old_view), self.term_dag.get(new_view)) {
            (Term::App(old_head, old_args), Term::App(_new_head, new_args)) => {
                let head = old_head.clone();
                let old_output = *old_args.last().expect("merge view term has no args");
                let new_output = *new_args.last().expect("merge view term has no args");
                let inputs = old_args[..old_args.len() - 1].to_vec();
                (head, inputs, old_output, new_output)
            }
            _ => panic!(
                "MergeFn premise proofs should prove function application terms, got {:?} and {:?}",
                self.term_dag.get(old_view),
                self.term_dag.get(new_view)
            ),
        }
    }

    /// Build a `MergeFn` proof of `to_prove = to_prove` from the two premises,
    /// reflexivizing each ([`ProofStore::reflexivize_premise`]).
    fn merge_fn_proof(
        &mut self,
        function: &str,
        old_proof_id: ProofId,
        new_proof_id: ProofId,
        to_prove: TermId,
    ) -> Proof {
        let old_proof = self.reflexivize_premise(old_proof_id);
        let new_proof = self.reflexivize_premise(new_proof_id);
        Proof {
            proposition: Proposition::new(to_prove, to_prove),
            justification: Justification::MergeFn {
                function: function.to_string(),
                old_proof,
                new_proof,
            },
        }
    }

    /// Converts a raw proof into a user-facing proof, recursively converting sub-proofs as needed.
    /// This adds new metadata to the proof, such as the substitution for rules.
    ///
    /// Panics if the raw proof is invalid with respect to the program.
    fn convert_raw_proof(
        &mut self,
        prog: &Vec<ResolvedNCommand>,
        globals: &HashMap<String, TermId>,
        raw_store: &RawProofStore,
        raw_proof_id: RawProofId,
    ) -> ProofId {
        if let Some(&id) = self.proof_id.get(&raw_store.store[raw_proof_id.index()]) {
            return id;
        }
        let raw_proof = &raw_store.store[raw_proof_id.index()];

        let proof = match raw_proof {
            RawProof::Fiat(lhs, rhs) => Proof {
                proposition: Proposition::new(
                    raw_store.unwrap_ast(*lhs),
                    raw_store.unwrap_ast(*rhs),
                ),
                justification: Justification::Fiat,
            },
            RawProof::Rule(name, premise_proofs, bridge_proofs, raw_site) => {
                let site = SiteRef::decode(*raw_site);
                let converted_premises: Vec<ProofId> = premise_proofs
                    .iter()
                    .map(|pid| self.convert_raw_proof(prog, globals, raw_store, *pid))
                    .collect();
                // The bridges are in the order the head builds, which is the order
                // `bridge_position` numbers them; a site built after this proof's
                // row has no bridge recorded yet. Only the ones the requested proof
                // is composed from are read: converting the rest would pull in
                // every proof the firing happened to pass over.
                let planned = self.head_plan(prog, name);
                let mut bridges: HashMap<SiteIndex, ProofId> = HashMap::default();
                for needed in sites_needed(&planned, site) {
                    let Some(position) = planned.bridge_position(needed) else {
                        continue;
                    };
                    let Some(raw) = bridge_proofs.get(position) else {
                        continue;
                    };
                    let converted = self.convert_raw_proof(prog, globals, raw_store, *raw);
                    bridges.insert(needed, converted);
                }

                // Rebuild/canonicalization can rewrite a matched custom-function-fact
                // premise `(= (f args) v)` into a non-reflexive natural->canonical
                // `Congr` proof `(f nat) = (f canon)` (e.g. when an argument's e-class
                // has several equivalent shapes from commutativity/associativity
                // rewrites). The checker's function-fact normal form expects a
                // reflexive premise at the matched (canonical) shape, so reflexivize
                // those. Equality-fact premises `(= a b)` must stay non-reflexive.
                let reflex_mask: Vec<bool> = {
                    let rule = prog
                        .iter()
                        .find_map(|cmd| match cmd {
                            ResolvedNCommand::NormRule { rule } if rule.name == *name => Some(rule),
                            _ => None,
                        })
                        .unwrap_or_else(|| panic!("could not find rule with name {name}"));
                    rule.body.iter().map(is_custom_func_fact).collect()
                };
                // Premises are in body-fact order, so each pairs with its own fact's
                // decision. There may be more premises than facts: `remove_globals`
                // appends a lookup fact per global the rule mentions, and the encoder
                // records a premise for each, while `prog` is the program from before
                // that pass. Those extras are exactly the trailing ones, so dropping
                // them is what pairs the rest correctly — but a *shorter* premise list
                // would misalign the mask silently, so require the encoder's count to
                // cover the body.
                assert!(
                    converted_premises.len() >= reflex_mask.len(),
                    "rule {name} recorded {} premises for a body of {} facts",
                    converted_premises.len(),
                    reflex_mask.len()
                );
                let converted_premises: Vec<ProofId> = converted_premises
                    .into_iter()
                    .zip(reflex_mask)
                    .map(|(pid, reflex)| {
                        if reflex {
                            self.reflexivize_premise(pid)
                        } else {
                            pid
                        }
                    })
                    .collect();

                let substitution = self.compute_rule_substitution(prog, name, &converted_premises);
                let site_props = self.replay_head(prog, globals, name, &substitution);
                // A global's value is in every substitution, so recording it in the
                // proof would only repeat the program.
                let mut recorded = substitution.clone();
                recorded.retain(|var, _term| globals.get(var).is_none());
                let mut firing = Firing::new(
                    name,
                    &planned,
                    site_props,
                    converted_premises,
                    bridges,
                    recorded,
                );
                let proof_id = firing.role(self, site);
                self.proof_id.insert(raw_proof.clone(), proof_id);
                return proof_id;
            }
            RawProof::MergeFnIdx(function, old_raw, new_raw, idx) => {
                let old_proof_id = self.convert_raw_proof(prog, globals, raw_store, *old_raw);
                let new_proof_id = self.convert_raw_proof(prog, globals, raw_store, *new_raw);
                // `idx` indexes all body nodes (pre-order, top node included). The
                // conclusion is that node's own minted term, i.e. its existence proof in
                // its FD view. The whole-view-row conclusion comes from `MergeFnRow`.
                let (_head, _inputs, old_output, new_output) =
                    self.merge_premise_view(old_proof_id, new_proof_id);
                let (to_prove, _props) = run_merge_subexpr(
                    &mut self.term_dag,
                    function,
                    prog,
                    old_output,
                    new_output,
                    *idx,
                )
                .unwrap_or_else(|e| {
                    panic!("failed to run merge subexpr {idx} for {function}: {e}")
                });
                self.merge_fn_proof(function, old_proof_id, new_proof_id, to_prove)
            }
            RawProof::MergeFnRow(function, old_raw, new_raw) => {
                let old_proof_id = self.convert_raw_proof(prog, globals, raw_store, *old_raw);
                let new_proof_id = self.convert_raw_proof(prog, globals, raw_store, *new_raw);
                // The conclusion is the whole view row `f(inputs..., merged)`, where
                // `merged` is the whole merge body evaluated on the two premise outputs.
                let (view_head, input_args, old_output, new_output) =
                    self.merge_premise_view(old_proof_id, new_proof_id);
                let (merged_child, _props) =
                    run_merge(&mut self.term_dag, function, prog, old_output, new_output)
                        .unwrap_or_else(|e| panic!("failed to run merge for {function}: {e}"));
                let mut merged_args = input_args;
                merged_args.push(merged_child);
                let to_prove = self.term_dag.app(view_head, merged_args);
                self.merge_fn_proof(function, old_proof_id, new_proof_id, to_prove)
            }
            RawProof::Trans(left_raw, right_raw) => {
                let left_id = self.convert_raw_proof(prog, globals, raw_store, *left_raw);
                let right_id = self.convert_raw_proof(prog, globals, raw_store, *right_raw);
                let left = &self.id_to_proof[left_id];
                let right = &self.id_to_proof[right_id];
                assert_eq!(
                    left.rhs(),
                    right.lhs(),
                    "transitivity requires matching middle terms"
                );
                Proof {
                    proposition: Proposition::new(left.lhs(), right.rhs()),
                    justification: Justification::Trans(left_id, right_id),
                }
            }
            RawProof::Sym(inner_raw) => {
                let inner_id = self.convert_raw_proof(prog, globals, raw_store, *inner_raw);
                let inner = &self.id_to_proof[inner_id];
                Proof {
                    proposition: Proposition::new(inner.rhs(), inner.lhs()),
                    justification: Justification::Sym(inner_id),
                }
            }
            RawProof::Congr(proof_raw, child_index, child_raw) => {
                let base_id = self.convert_raw_proof(prog, globals, raw_store, *proof_raw);
                let child_id = self.convert_raw_proof(prog, globals, raw_store, *child_raw);
                let base_lhs = self.id_to_proof[base_id].lhs();
                let base_rhs = self.id_to_proof[base_id].rhs();
                let child_rhs = self.id_to_proof[child_id].rhs();
                let rhs = self.replace_term_child(base_rhs, *child_index, child_rhs);

                Proof {
                    proposition: Proposition::new(base_lhs, rhs),
                    justification: Justification::Congr {
                        proof: base_id,
                        child_index: *child_index,
                        child_proof: child_id,
                    },
                }
            }
            RawProof::CongrAll(proof_raw, child_raw) => {
                let base_id = self.convert_raw_proof(prog, globals, raw_store, *proof_raw);
                let child_id = self.convert_raw_proof(prog, globals, raw_store, *child_raw);
                let expanded_id = self.expand_congr_all(base_id, child_id);
                self.proof_id.insert(raw_proof.clone(), expanded_id);
                return expanded_id;
            }
            RawProof::Rebuild { row, steps, eclass } => {
                let row_id = self.convert_raw_proof(prog, globals, raw_store, *row);
                let step_ids: Vec<(usize, ProofId)> = steps
                    .iter()
                    .map(|(position, step)| {
                        (
                            *position,
                            self.convert_raw_proof(prog, globals, raw_store, *step),
                        )
                    })
                    .collect();
                let eclass_id =
                    (*eclass).map(|e| self.convert_raw_proof(prog, globals, raw_store, e));
                let expanded_id = self.expand_rebuild(row_id, &step_ids, eclass_id);
                self.proof_id.insert(raw_proof.clone(), expanded_id);
                return expanded_id;
            }
            RawProof::Displaced { hi, lo, shared } => {
                let hi_id = self.convert_raw_proof(prog, globals, raw_store, *hi);
                let lo_id = self.convert_raw_proof(prog, globals, raw_store, *lo);
                let expanded_id = self.expand_displaced(hi_id, lo_id, *shared);
                self.proof_id.insert(raw_proof.clone(), expanded_id);
                return expanded_id;
            }
            RawProof::ContainerNormalize(inner_raw) => {
                let inner_id = self.convert_raw_proof(prog, globals, raw_store, *inner_raw);
                let inner_lhs = self.id_to_proof[inner_id].lhs();
                let inner_rhs = self.id_to_proof[inner_id].rhs();
                let normalized = self.normalize_container(inner_rhs);
                Proof {
                    proposition: Proposition::new(inner_lhs, normalized),
                    justification: Justification::ContainerNormalize { proof: inner_id },
                }
            }
            RawProof::Eval => {
                // The marker proves nothing on its own; `check_side_condition`
                // re-evaluates the side condition against the rule body. Give it
                // a placeholder proposition (the `Proof` struct requires one).
                let placeholder = self.term_dag.app("@side-condition".to_string(), vec![]);
                Proof {
                    proposition: Proposition::new(placeholder, placeholder),
                    justification: Justification::Eval,
                }
            }
        };

        let proof_id = self.id_to_proof.push(proof);
        self.proof_id.insert(raw_proof.clone(), proof_id);
        proof_id
    }

    /// How `rule_name`'s head lowers. A property of the rule text, so it is
    /// computed once per rule.
    fn head_plan(&mut self, prog: &[ResolvedNCommand], rule_name: &str) -> Rc<HeadPlan> {
        if let Some(plan) = self.head_plans.get(rule_name) {
            return plan.clone();
        }
        let rule = rule_named(prog, rule_name);
        let mut minted = 0usize;
        let mut fresh = || {
            minted += 1;
            format!("@union-operand-{minted}")
        };
        let plan = Rc::new(HeadPlan::new(&rule.head.0, &mut fresh));
        self.head_plans.insert(rule_name.to_string(), plan.clone());
        plan
    }

    /// What each conclusion site of `rule_name`'s head concludes under
    /// `substitution`, in `conclusion_sites` order.
    ///
    /// Panics if the rule is not in `prog` or if its head does not replay.
    fn replay_head(
        &mut self,
        prog: &[ResolvedNCommand],
        globals: &HashMap<String, TermId>,
        rule_name: &str,
        substitution: &IndexMap<String, TermId>,
    ) -> Vec<(SiteIndex, Proposition)> {
        let rule = rule_named(prog, rule_name);
        let actions: Vec<_> = rule.head.0.iter().collect();
        let mut bindings = globals.clone();
        bindings.extend(substitution.iter().map(|(var, term)| (var.clone(), *term)));
        process_actions(rule_name, bindings, &actions, &mut self.term_dag)
            .unwrap_or_else(|err| panic!("rule {rule_name}'s head did not replay: {err}"))
            .site_propositions
    }

    /// For a given rule and premise proofs, compute the substitution used in the rule application.
    /// The proof has enough information to compute the substitution, we do it here
    /// for convenience.
    ///
    /// Entries come out in the order the variables first occur in the rule body.
    fn compute_rule_substitution(
        &self,
        prog: &[ResolvedNCommand],
        rule_name: &str,
        premise_proofs: &[ProofId],
    ) -> IndexMap<String, TermId> {
        let substitution = IndexMap::default();

        let Some(rule) = prog.iter().find_map(|cmd| match cmd {
            ResolvedNCommand::NormRule { rule } if rule.name == rule_name => Some(rule),
            _ => None,
        }) else {
            panic!("could not find rule with name {rule_name}");
        };

        if rule.body.len() != premise_proofs.len() {
            panic!(
                "rule {} has {} premises, but got {} premise proofs",
                rule_name,
                rule.body.len(),
                premise_proofs.len()
            );
        }

        let mut current_subst = substitution;
        for (fact, proof_id) in rule.body.iter().zip(premise_proofs.iter()) {
            // Container side conditions carry only an `Eval` marker (no value);
            // their bindings are generated by `check_side_condition` at check
            // time, so there is nothing to unify here.
            if crate::proofs::proof_checker::is_container_side_condition(fact) {
                continue;
            }
            self.unify_fact(fact, *proof_id, &mut current_subst);
        }

        current_subst
    }

    /// Bind the fact's variables from the term its premise proof proves. A
    /// primitive call contributes no bindings of its own — the value it computes
    /// is read off the proof instead.
    pub(super) fn unify_fact(
        &self,
        fact: &ResolvedFact,
        proof_id: ProofId,
        subst: &mut IndexMap<String, TermId>,
    ) {
        let proof = &self.id_to_proof[proof_id];
        match fact {
            // In proof normal form, this is the only way that function calls apppear.
            ResolvedFact::Eq(
                _span,
                ResolvedExpr::Call(
                    _span2,
                    head @ ResolvedCall::Func(FuncType {
                        subtype: FunctionSubtype::Custom,
                        ..
                    }),
                    args,
                ),
                ResolvedExpr::Var(_span3, v),
            ) => {
                let term = proof.rhs();
                let children = match self.term_dag.get(term) {
                    Term::App(head_name, children) if head_name == head.name() => children.clone(),
                    _ => panic!("expected function application term in proof rhs"),
                };
                // assert children length matches args length + 1 for bound var
                if children.len() != args.len() + 1 {
                    panic!(
                        "function call arity mismatch for {}: expected {}, got {}",
                        head.name(),
                        args.len() + 1,
                        children.len()
                    );
                }

                // unify the arguments before binding v to the last child, so the
                // substitution records the variables in the order the fact writes them
                for (arg_expr, child_term) in args.iter().zip(children.iter()) {
                    self.unify_expr(arg_expr, *child_term, subst);
                }
                let var_child_term = children.last().unwrap();
                self.add_to_subst(subst, &v.name, *var_child_term);
            }
            ResolvedFact::Eq(_, lhs_expr, rhs_expr) => {
                self.unify_expr(lhs_expr, proof.lhs(), subst);
                self.unify_expr(rhs_expr, proof.rhs(), subst);
            }
            ResolvedFact::Fact(expr) => {
                self.unify_expr(expr, proof.rhs(), subst);
            }
        }
    }

    fn add_to_subst(&self, subst: &mut IndexMap<String, TermId>, var: &str, term_id: TermId) {
        match subst.entry(var.to_string()) {
            IEntry::Vacant(entry) => {
                entry.insert(term_id);
            }
            IEntry::Occupied(entry) => {
                if *entry.get() != term_id {
                    panic!(
                        "conflicting substitutions for variable {}: {:?} vs {:?}",
                        var,
                        self.term_dag.get(*entry.get()),
                        self.term_dag.get(term_id)
                    );
                }
            }
        }
    }

    fn unify_expr(
        &self,
        expr: &ResolvedExpr,
        term_id: TermId,
        substitution: &mut IndexMap<String, TermId>,
    ) {
        match expr {
            ResolvedExpr::Lit(_, _lit) => (),
            ResolvedExpr::Var(_, var) => {
                self.add_to_subst(substitution, &var.name, term_id);
            }
            ResolvedExpr::Call(_, call, args) => {
                // if the call is a primitive we don't need to do anything
                // because proofs don't support primitves with children applications that are not primitives
                if let ResolvedCall::Primitive(_) = call {
                    return;
                }
                let Term::App(head, children) = self.term_dag.get(term_id) else {
                    panic!(
                        "expected function application term for call {}, got {:?}. Conversion from raw proofs assumes valid proofs with respect to the program.",
                        call.name(),
                        self.term_dag.get(term_id)
                    );
                };
                if head != call.name() {
                    panic!(
                        "function call head mismatch: expected {}, got {head}",
                        call.name(),
                    );
                }

                if children.len() != args.len() {
                    panic!(
                        "function call arity mismatch for {}: expected {}, got {}",
                        call.name(),
                        args.len(),
                        children.len()
                    );
                }
                for (arg_expr, child_term) in args.iter().zip(children.iter()) {
                    self.unify_expr(arg_expr, *child_term, substitution);
                }
            }
        }
    }

    /// Expand an element-matching congruence ([`RawProof::CongrAll`]) into a
    /// chain of positional [`Justification::Congr`] steps, one per child of
    /// the base proof's rhs equal to the child proof's lhs, so the user-facing
    /// proof needs no new justification kind.
    ///
    /// A `CongrAll` may be the identity at the term level, expanding to zero
    /// steps: distinct element *values* can share one term shape (a natural id
    /// and its dedup id), so the child proof's endpoints may coincide, and a
    /// prior `CongrAll` whose lhs is that shared term already rewrote every
    /// occurrence.
    fn expand_congr_all(&mut self, base_id: ProofId, child_id: ProofId) -> ProofId {
        let child_lhs = self.id_to_proof[child_id].lhs();
        let child_rhs = self.id_to_proof[child_id].rhs();
        let mut current = base_id;
        if child_lhs == child_rhs {
            return current;
        }
        loop {
            let lhs = self.id_to_proof[current].lhs();
            let rhs = self.id_to_proof[current].rhs();
            let Term::App(_, children) = self.term_dag.get(rhs) else {
                panic!("congr-all requires an application term. Conversion assumes valid proofs.");
            };
            let Some(child_index) = children.iter().position(|c| *c == child_lhs) else {
                break;
            };
            let new_rhs = self.replace_term_child(rhs, child_index, child_rhs);
            current = self.id_to_proof.push(Proof {
                proposition: Proposition::new(lhs, new_rhs),
                justification: Justification::Congr {
                    proof: current,
                    child_index,
                    child_proof: child_id,
                },
            });
        }
        current
    }

    /// Expand a rebuild ([`RawProof::Rebuild`]) into the composition it packs: a
    /// [`Justification::Congr`] per step, folded onto the row proof in ascending
    /// child position, then `Trans(Sym(eclass), …)` when the row's e-class moved
    /// as well.
    ///
    /// Panics if the steps are not in ascending position, if a step does not
    /// start at the child it names, or if the e-class proof does not meet the
    /// row's left-hand side.
    fn expand_rebuild(
        &mut self,
        row: ProofId,
        steps: &[(usize, ProofId)],
        eclass: Option<ProofId>,
    ) -> ProofId {
        let mut current = row;
        let mut previous: Option<usize> = None;
        for &(position, step) in steps {
            if let Some(previous) = previous {
                assert!(
                    previous < position,
                    "rebuild steps must be in ascending child position, got {previous} then {position}"
                );
            }
            previous = Some(position);
            let base = self.id_to_proof[current].rhs();
            let child_lhs = self.id_to_proof[step].lhs();
            let base_child = match self.term_dag.get(base) {
                Term::App(_, children) => children.get(position).copied(),
                other => panic!("a rebuild's row proof should prove an application, got {other:?}"),
            };
            assert_eq!(
                base_child,
                Some(child_lhs),
                "rebuild step {position} does not start at that child of the row"
            );
            current = congr(self, current, position, step);
        }
        let Some(eclass) = eclass else {
            return current;
        };
        let back = sym(self, eclass);
        trans(self, back, current)
    }

    /// Expand a displaced edge ([`RawProof::Displaced`]) into the composition it
    /// packs: the two carried proofs joined at the endpoint they share, with the
    /// one pointing the wrong way reversed, proving `hi = lo`.
    ///
    /// Panics unless they do share that endpoint.
    fn expand_displaced(&mut self, hi: ProofId, lo: ProofId, shared: SharedEnd) -> ProofId {
        match shared {
            SharedEnd::Lhs => {
                let back = sym(self, hi);
                trans(self, back, lo)
            }
            SharedEnd::Rhs => {
                let back = sym(self, lo);
                trans(self, hi, back)
            }
        }
    }

    pub(super) fn replace_term_child(
        &mut self,
        term_id: TermId,
        child_index: usize,
        new_child: TermId,
    ) -> TermId {
        let term = self.term_dag.get(term_id).clone();
        let Term::App(head, args) = term else {
            panic!("congruence requires an application term");
        };
        assert!(
            child_index < args.len(),
            "congruence child index {child_index} out of bounds for term with {} children",
            args.len()
        );

        let updated_children: Vec<TermId> = args
            .iter()
            .enumerate()
            .map(|(idx, child_id)| {
                if idx == child_index {
                    new_child
                } else {
                    *child_id
                }
            })
            .collect();

        self.term_dag.app(head.clone(), updated_children)
    }

    /// Print a proof with the given id, with subproofs and terms
    /// added as let bindings in `buffer`.
    /// Returns the printed proof string.
    fn print_to_buffer(
        &self,
        symbol_gen: &mut SymbolGen,
        proof_id: ProofId,
        buffer: &mut String,
    ) -> String {
        let mut dag = self.term_dag.clone();
        let mut cache = HashMap::default();
        let proof_term_id = self.proof_to_term_for_printing(&mut dag, proof_id, &mut cache);
        dag.to_string_with_let_internal(symbol_gen, proof_term_id, buffer, |constructor| {
            match constructor {
                "=" => "prop".to_string(),
                "Fiat" | "Rule" | "Merge" | "Trans" | "Sym" | "Congr" | "ContainerNormalize"
                | "Eval" => "prf".to_string(),
                _ => "t".to_string(),
            }
        })
    }

    fn proof_to_term_for_printing(
        &self,
        dag: &mut TermDag,
        proof_id: ProofId,
        cache: &mut HashMap<ProofId, TermId>,
    ) -> TermId {
        if let Some(&term_id) = cache.get(&proof_id) {
            return term_id;
        }

        let proof = &self.id_to_proof[proof_id];

        // Helper to create (= lhs rhs) term
        let make_equality = |dag: &mut TermDag, lhs: TermId, rhs: TermId| -> TermId {
            dag.app("=".to_string(), vec![lhs, rhs])
        };

        let term_id = match &proof.justification {
            Justification::Fiat => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                dag.app("Fiat".to_string(), vec![equality])
            }
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
                site: _,
            } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let name_literal = dag.lit(Literal::String(name.clone()));
                let name_term = dag.app("name".to_string(), vec![name_literal]);

                let premise_terms: Vec<TermId> = premise_proofs
                    .iter()
                    .map(|pid| self.proof_to_term_for_printing(dag, *pid, cache))
                    .collect();
                let premises_term = dag.app("premises".to_string(), premise_terms);

                let substitution_terms: Vec<TermId> = substitution
                    .iter()
                    .map(|(var, term_id)| dag.app(var.clone(), vec![*term_id]))
                    .collect();
                let substitution_term = dag.app("substitution".to_string(), substitution_terms);

                dag.app(
                    "Rule".to_string(),
                    vec![equality, name_term, premises_term, substitution_term],
                )
            }
            Justification::MergeFn {
                function,
                old_proof,
                new_proof,
            } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let old_term_id = self.proof_to_term_for_printing(dag, *old_proof, cache);
                let new_term_id = self.proof_to_term_for_printing(dag, *new_proof, cache);
                let function_term = dag.var(function.clone());
                dag.app(
                    "Merge".to_string(),
                    vec![equality, function_term, old_term_id, new_term_id],
                )
            }
            Justification::Trans(left, right) => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let left_term_id = self.proof_to_term_for_printing(dag, *left, cache);
                let right_term_id = self.proof_to_term_for_printing(dag, *right, cache);
                dag.app(
                    "Trans".to_string(),
                    vec![equality, left_term_id, right_term_id],
                )
            }
            Justification::Sym(inner) => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let inner_term_id = self.proof_to_term_for_printing(dag, *inner, cache);
                dag.app("Sym".to_string(), vec![equality, inner_term_id])
            }
            Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let base_term_id = self.proof_to_term_for_printing(dag, *base, cache);
                let child_term_id = self.proof_to_term_for_printing(dag, *child_proof, cache);
                let index_term = dag.lit(Literal::Int(*child_index as i64));
                dag.app(
                    "Congr".to_string(),
                    vec![equality, base_term_id, child_term_id, index_term],
                )
            }
            Justification::ContainerNormalize { proof: inner } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let inner_term_id = self.proof_to_term_for_printing(dag, *inner, cache);
                dag.app(
                    "ContainerNormalize".to_string(),
                    vec![equality, inner_term_id],
                )
            }
            Justification::Eval => dag.app("Eval".to_string(), vec![]),
        };

        cache.insert(proof_id, term_id);
        term_id
    }
}

impl Proof {
    /// Get the proposition the proof proves
    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    /// Get the left-hand side of the proven equality
    pub fn lhs(&self) -> TermId {
        self.proposition.lhs()
    }
    /// Get the right-hand side of the proven equality
    pub fn rhs(&self) -> TermId {
        self.proposition.rhs()
    }

    /// Get the justification for the proof
    pub fn justification(&self) -> &Justification {
        &self.justification
    }
}

/// A packed row — a [`RawProof::Rebuild`] or a [`RawProof::Displaced`] — expands
/// to exactly the `Congr`/`Sym`/`Trans` composition the generated rule or merge
/// body used to spell across rows. The compositions here are written out by hand
/// rather than generated, so they are an oracle rather than a second copy of the
/// expansions.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::proofs::proof_encoding_helpers::RebuildShape;
    use crate::util::SymbolGen;

    /// One firing of a rebuild rule over a four-child view row, as the premises
    /// the rule records: the row proof `e_old = f(old0 old1 old2 old3)`, a step
    /// per child column (column 3's is reflexive — that column did not move),
    /// and the e-class's own move `e_old = e_new`.
    struct Firing {
        raw: RawProofStore,
        row: RawProofId,
        /// `old_j = new_j`, per column.
        steps: Vec<RawProofId>,
        /// `e_old = e_new`.
        eclass: RawProofId,
        old: Vec<TermId>,
        /// Each column's canonical form; column 3's is its old one.
        new: Vec<TermId>,
        e_old: TermId,
        e_new: TermId,
    }

    impl Firing {
        fn new() -> Firing {
            let mut raw = empty_store();
            let leaf = |raw: &mut RawProofStore, name: String| raw.term_dag.app(name, vec![]);
            let old: Vec<TermId> = (0..4).map(|j| leaf(&mut raw, format!("old{j}"))).collect();
            let new: Vec<TermId> = (0..4)
                .map(|j| match j {
                    3 => old[3],
                    _ => leaf(&mut raw, format!("new{j}")),
                })
                .collect();
            let e_old = leaf(&mut raw, "e_old".to_string());
            let e_new = leaf(&mut raw, "e_new".to_string());

            let row_term = raw.term_dag.app("f".to_string(), old.clone());
            let row = fiat(&mut raw, e_old, row_term);
            let steps = (0..4).map(|j| fiat(&mut raw, old[j], new[j])).collect();
            let eclass = fiat(&mut raw, e_old, e_new);
            Firing {
                raw,
                row,
                steps,
                eclass,
                old,
                new,
                e_old,
                e_new,
            }
        }

        /// The proposition `lhs = f(children)`.
        fn concludes(&mut self, lhs: TermId, children: Vec<TermId>) -> Proposition {
            let rhs = self.raw.term_dag.app("f".to_string(), children);
            Proposition::new(lhs, rhs)
        }

        /// Convert and simplify both proofs in one store, and require that they
        /// are the same tree, proving `expected`.
        fn assert_agree(&self, rebuild: RawProofId, chain: RawProofId, expected: &Proposition) {
            assert_agree(&self.raw, rebuild, chain, expected);
        }
    }

    /// Convert and simplify both proofs in one store, and require that they are
    /// the same tree, proving `expected`.
    fn assert_agree(
        raw: &RawProofStore,
        packed: RawProofId,
        chain: RawProofId,
        expected: &Proposition,
    ) {
        let mut store =
            ProofStore::new(raw.term_dag.clone(), HashMap::default(), HashSet::default());
        let prog = vec![];
        let globals = HashMap::default();
        let mut convert = |id| {
            let converted = store.convert_raw_proof(&prog, &globals, raw, id);
            store.simplify(converted)
        };
        let (packed, chain) = (convert(packed), convert(chain));
        assert_eq!(store.get(chain).proposition(), expected);
        assert!(
            same_proof(&store, packed, chain),
            "the expanded row\n{}\nis not the composition it packs\n{}",
            store.proof_to_string(packed),
            store.proof_to_string(chain),
        );
    }

    /// A leaf proof of `lhs = rhs`, spelled the way an extracted `Fiat` row is
    /// (each endpoint wrapped in an `Ast` constructor).
    fn fiat(raw: &mut RawProofStore, lhs: TermId, rhs: TermId) -> RawProofId {
        let lhs = raw.term_dag.app("Ast".to_string(), vec![lhs]);
        let rhs = raw.term_dag.app("Ast".to_string(), vec![rhs]);
        raw.add_proof(RawProof::Fiat(lhs, rhs))
    }

    /// Whether two proofs are the same tree. Their ids differ by construction:
    /// the chain's nodes are minted per raw node, the rebuild's by the synthesis
    /// helpers' own hash-consing.
    fn same_proof(store: &ProofStore, left: ProofId, right: ProofId) -> bool {
        let (left, right) = (store.get(left), store.get(right));
        if left.proposition != right.proposition {
            return false;
        }
        match (&left.justification, &right.justification) {
            (Justification::Fiat, Justification::Fiat) => true,
            (Justification::Sym(left), Justification::Sym(right)) => {
                same_proof(store, *left, *right)
            }
            (Justification::Trans(la, lb), Justification::Trans(ra, rb)) => {
                same_proof(store, *la, *ra) && same_proof(store, *lb, *rb)
            }
            (
                Justification::Congr {
                    proof: left,
                    child_index: left_index,
                    child_proof: left_child,
                },
                Justification::Congr {
                    proof: right,
                    child_index: right_index,
                    child_proof: right_child,
                },
            ) => {
                left_index == right_index
                    && same_proof(store, *left, *right)
                    && same_proof(store, *left_child, *right_child)
            }
            _ => false,
        }
    }

    /// Columns 0 and 2 move, column 3 does not, and so does the e-class.
    #[test]
    fn rebuild_expands_to_the_chain_it_packs() {
        let mut firing = Firing::new();
        let (row, eclass) = (firing.row, firing.eclass);
        let steps = firing.steps.clone();
        let rebuild = firing.raw.add_proof(RawProof::Rebuild {
            row,
            steps: vec![(0, steps[0]), (2, steps[2]), (3, steps[3])],
            eclass: Some(eclass),
        });

        let at_0 = firing.raw.add_proof(RawProof::Congr(row, 0, steps[0]));
        let at_2 = firing.raw.add_proof(RawProof::Congr(at_0, 2, steps[2]));
        let at_3 = firing.raw.add_proof(RawProof::Congr(at_2, 3, steps[3]));
        let back = firing.raw.add_proof(RawProof::Sym(eclass));
        let chain = firing.raw.add_proof(RawProof::Trans(back, at_3));

        let children = vec![firing.new[0], firing.old[1], firing.new[2], firing.old[3]];
        let expected = firing.concludes(firing.e_new, children);
        firing.assert_agree(rebuild, chain, &expected);
    }

    /// A view whose output is not an e-class: only child columns move.
    #[test]
    fn rebuild_without_an_eclass_step_expands_to_the_chain() {
        let mut firing = Firing::new();
        let row = firing.row;
        let steps = firing.steps.clone();
        let rebuild = firing.raw.add_proof(RawProof::Rebuild {
            row,
            steps: vec![(1, steps[1]), (3, steps[3])],
            eclass: None,
        });

        let at_1 = firing.raw.add_proof(RawProof::Congr(row, 1, steps[1]));
        let chain = firing.raw.add_proof(RawProof::Congr(at_1, 3, steps[3]));

        let children = vec![firing.old[0], firing.new[1], firing.old[2], firing.old[3]];
        let expected = firing.concludes(firing.e_old, children);
        firing.assert_agree(rebuild, chain, &expected);
    }

    /// Only the e-class moved, so the fold contributes nothing.
    #[test]
    fn rebuild_with_no_child_steps_expands_to_the_chain() {
        let mut firing = Firing::new();
        let (row, eclass) = (firing.row, firing.eclass);
        let rebuild = firing.raw.add_proof(RawProof::Rebuild {
            row,
            steps: vec![],
            eclass: Some(eclass),
        });

        let back = firing.raw.add_proof(RawProof::Sym(eclass));
        let chain = firing.raw.add_proof(RawProof::Trans(back, row));

        let children = firing.old.clone();
        let expected = firing.concludes(firing.e_new, children);
        firing.assert_agree(rebuild, chain, &expected);
    }

    /// An empty store whose names are the ones a rebuild row is spelled with.
    fn empty_store() -> RawProofStore {
        RawProofStore {
            term_dag: TermDag::default(),
            names: EncodingNames::new(&mut SymbolGen::new("test".to_string())),
            store: IndexSet::default(),
            term_to_proof: HashMap::default(),
            proof_to_term: HashMap::default(),
        }
    }

    /// A rebuild row over `row`, one step per `(column, step)` pair and the
    /// e-class's own step when its view has one, spelled as the extracted term
    /// of a [`EncodingNames::rebuild_proof`] row.
    fn rebuild_term(
        raw: &mut RawProofStore,
        row: TermId,
        steps: &[(i64, TermId)],
        eclass: Option<TermId>,
    ) -> TermId {
        let head = raw.names.rebuild_proof(RebuildShape {
            steps: steps.len(),
            eclass: eclass.is_some(),
        });
        let mut args = vec![row];
        for &(column, step) in steps {
            args.push(raw.term_dag.lit(Literal::Int(column)));
            args.push(step);
        }
        args.extend(eclass);
        raw.term_dag.app(head, args)
    }

    /// A reflexive `Fiat` row over a nullary term, as an extracted proof term.
    fn fiat_term(raw: &mut RawProofStore, name: &str) -> TermId {
        let value = raw.term_dag.app(name.to_string(), vec![]);
        let ast = raw.term_dag.app("Ast".to_string(), vec![value]);
        let head = raw.names.fiat_constructor.clone();
        raw.term_dag.app(head, vec![ast, ast])
    }

    /// The columns are literals, so a reader has to skip them to find the
    /// proofs, and the e-class's is past the last of them. Getting that wrong
    /// here costs no correctness — `parse_proof` recurses on whatever it was
    /// not handed — but it costs the stack, which is what `parse_nested_first`
    /// exists to spend on the heap instead.
    #[test]
    fn a_rebuild_rows_nested_proofs_are_its_row_and_its_steps() {
        let mut raw = empty_store();
        let row = fiat_term(&mut raw, "row");
        let first = fiat_term(&mut raw, "first");
        let second = fiat_term(&mut raw, "second");
        let eclass = fiat_term(&mut raw, "eclass");
        let steps = [(0, first), (2, second)];
        let term = rebuild_term(&mut raw, row, &steps, None);
        assert_eq!(
            raw.nested_proofs(term),
            vec![row, first, second],
            "a rebuild row nests its row proof and its step proofs"
        );
        let term = rebuild_term(&mut raw, row, &steps, Some(eclass));
        assert_eq!(
            raw.nested_proofs(term),
            vec![row, first, second, eclass],
            "and the e-class proof after them, when it has one"
        );
    }

    /// A chain of rebuilds parses without recursing per link, on a stack far
    /// too small to hold one frame per link — through either proof field a link
    /// can chain on.
    #[test]
    fn a_deep_rebuild_chain_parses_without_a_deep_stack() {
        for through_eclass in [false, true] {
            std::thread::Builder::new()
                .stack_size(512 * 1024)
                .spawn(move || {
                    let mut raw = empty_store();
                    let step = fiat_term(&mut raw, "step");
                    let leaf = fiat_term(&mut raw, "row");
                    let mut chain = leaf;
                    for _ in 0..50_000 {
                        chain = if through_eclass {
                            rebuild_term(&mut raw, leaf, &[(0, step)], Some(chain))
                        } else {
                            rebuild_term(&mut raw, chain, &[(0, step)], None)
                        };
                    }
                    RawProofStore::from_extracted(&raw.names, raw.term_dag.clone(), chain);
                })
                .expect("spawn")
                .join()
                .expect("a deep rebuild chain should parse");
        }
    }

    /// A displaced-edge row over two carried proofs, spelled as the extracted
    /// term of a [`EncodingNames::displaced_proof`] row.
    fn displaced_term(
        raw: &mut RawProofStore,
        hi: TermId,
        lo: TermId,
        shared: SharedEnd,
    ) -> TermId {
        let head = raw.names.displaced_proof(shared).to_string();
        raw.term_dag.app(head, vec![hi, lo])
    }

    /// One merge collision, meeting at `shared`: the larger side's carried proof,
    /// the smaller side's, and the `hi = lo` the displaced edge has to state.
    fn collision(
        raw: &mut RawProofStore,
        shared: SharedEnd,
    ) -> (RawProofId, RawProofId, Proposition) {
        let leaf = |raw: &mut RawProofStore, name: &str| raw.term_dag.app(name.into(), vec![]);
        let hi_term = leaf(raw, "hi");
        let lo_term = leaf(raw, "lo");
        let shared_term = leaf(raw, "shared");
        let (hi, lo) = match shared {
            SharedEnd::Lhs => (
                fiat(raw, shared_term, hi_term),
                fiat(raw, shared_term, lo_term),
            ),
            SharedEnd::Rhs => (
                fiat(raw, hi_term, shared_term),
                fiat(raw, lo_term, shared_term),
            ),
        };
        (hi, lo, Proposition::new(hi_term, lo_term))
    }

    /// Either way the carried proofs point, the row expands to the `Sym` + `Trans`
    /// pair a merge body used to write, proving that the displaced side equals the
    /// kept one.
    #[test]
    fn displaced_expands_to_the_pair_it_packs() {
        for shared in [SharedEnd::Lhs, SharedEnd::Rhs] {
            let mut raw = empty_store();
            let (hi, lo, expected) = collision(&mut raw, shared);
            let displaced = raw.add_proof(RawProof::Displaced { hi, lo, shared });
            let pair = match shared {
                SharedEnd::Lhs => {
                    let back = raw.add_proof(RawProof::Sym(hi));
                    raw.add_proof(RawProof::Trans(back, lo))
                }
                SharedEnd::Rhs => {
                    let back = raw.add_proof(RawProof::Sym(lo));
                    raw.add_proof(RawProof::Trans(hi, back))
                }
            };
            assert_agree(&raw, displaced, pair, &expected);
        }
    }

    /// Both carried proofs nest. Getting that wrong here costs no correctness —
    /// `parse_proof` recurses on whatever it was not handed — but it costs the
    /// stack, which is what `parse_nested_first` exists to spend on the heap
    /// instead.
    #[test]
    fn a_displaced_rows_nested_proofs_are_its_two_carried_proofs() {
        let mut raw = empty_store();
        let hi = fiat_term(&mut raw, "hi");
        let lo = fiat_term(&mut raw, "lo");
        for shared in [SharedEnd::Lhs, SharedEnd::Rhs] {
            let term = displaced_term(&mut raw, hi, lo, shared);
            assert_eq!(
                raw.nested_proofs(term),
                vec![hi, lo],
                "a {shared:?}-sharing displaced row nests both carried proofs"
            );
        }
    }

    /// A chain of displaced edges — one collision's proof carried into the next —
    /// parses without recursing per link, on a stack far too small to hold one
    /// frame per link, through either carried proof.
    #[test]
    fn a_deep_displaced_chain_parses_without_a_deep_stack() {
        for shared in [SharedEnd::Lhs, SharedEnd::Rhs] {
            for through_lo in [false, true] {
                std::thread::Builder::new()
                    .stack_size(512 * 1024)
                    .spawn(move || {
                        let mut raw = empty_store();
                        let leaf = fiat_term(&mut raw, "carried");
                        let mut chain = leaf;
                        for _ in 0..50_000 {
                            chain = if through_lo {
                                displaced_term(&mut raw, leaf, chain, shared)
                            } else {
                                displaced_term(&mut raw, chain, leaf, shared)
                            };
                        }
                        RawProofStore::from_extracted(&raw.names, raw.term_dag.clone(), chain);
                    })
                    .expect("spawn")
                    .join()
                    .expect("a deep displaced chain should parse");
            }
        }
    }
}
