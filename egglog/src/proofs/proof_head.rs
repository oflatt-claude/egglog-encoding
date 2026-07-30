//! How a rule head lowers, and the flat array of proofs that lowering produces.
//!
//! A head that builds a term needs more proofs than it concludes: the term as
//! the head wrote it, the same term over its children's representatives, and the
//! edges between them. One walk of the head produces them all, in a fixed order,
//! so a proof is named by nothing but its position in that array — its *column*.
//! The encoder walks a head to lower it, naming each row it emits by the column
//! the walk is at; [`Firing`] walks the same head to rebuild the array from the
//! substitution, the body premises, and the rule proof's trailing *bridge*
//! premises — the view-row proof of each subterm the head interned. A row's
//! column indexes straight into what comes back.
//!
//! [`HeadPlan`] is the head as the encoder lowers it, read by both walks. The
//! compositions themselves are written once, over [`ProofAlgebra`]: this walk
//! applies them to proof nodes, and the encoder to the proof variables it emits
//! wherever it composes rather than records — a top-level action or a merge
//! body. [`ProofSite`] is which of the two the encoder is doing.

use crate::{
    TermId,
    ast::{
        FunctionSubtype, GenericAction, GenericExpr, ResolvedAction, ResolvedExpr, ResolvedExprExt,
        ResolvedVar, Span,
    },
    core::ResolvedCall,
    proofs::{
        proof_checker::eval_expr_with_subst,
        proof_encoding::ProofInstrumentor,
        proof_format::{Justification, Proof, ProofId, ProofStore, Proposition, SynthKey},
    },
    typechecking::FuncType,
    util::{HashMap, HashSet, IndexMap},
};

/// Which of the encoding's two layers the encoder is lowering under.
///
/// Layer 1 composes each proof where it is needed and writes every step out.
/// Layer 2 keeps the same walk but, having the rule head to replay, numbers the
/// proofs by column and writes a row only where the e-graph stores one. Every
/// site that has to know which layer it is in asks this (see the *Proofs* part
/// of `proof_encoding.md`).
pub(crate) enum ProofSite {
    /// No rule head to replay: a top-level action, a merge body, or a position
    /// inside a head that concludes nothing — a `change` argument.
    Composed,
    /// A rule head, whose next unclaimed column is `next_column`.
    Skeleton { next_column: usize },
}

impl ProofSite {
    /// Whether the proofs here are composed on the spot rather than numbered.
    pub(crate) fn composes(&self) -> bool {
        matches!(self, ProofSite::Composed)
    }

    /// Reserve the next `count` columns and answer with the first, or `None`
    /// where the site composes instead of numbering.
    pub(crate) fn take_columns(&mut self, count: usize) -> Option<usize> {
        let ProofSite::Skeleton { next_column } = self else {
            return None;
        };
        let first = *next_column;
        *next_column += count;
        Some(first)
    }
}

/// A rule head as the encoder lowers it.
pub(crate) struct HeadPlan {
    /// The head with every constructor-application `union` operand lifted into a
    /// preceding `let`.
    pub actions: Vec<ResolvedAction>,
    /// Guest variable -> the variable holding the e-class its constructor is
    /// built into, instead of a fresh one.
    pub construct_into: HashMap<String, String>,
    /// Indices into [`Self::actions`] of the `union`s the plan makes redundant.
    pub dropped: HashSet<usize>,
}

impl HeadPlan {
    /// Plan `actions`. `fresh` names the lifted `let`s; only their uniqueness
    /// matters, so a consumer that wants the shape rather than the code can
    /// supply a local counter.
    pub(crate) fn new(actions: &[ResolvedAction], fresh: &mut dyn FnMut() -> String) -> Self {
        let actions = normalize_union_operands(actions, fresh);
        let (construct_into, dropped) = plan_construct_into(&actions);
        HeadPlan {
            actions,
            construct_into,
            dropped,
        }
    }
}

/// The `(FuncType, args)` of a constructor-application expression, else `None`.
pub(crate) fn constructor_operand(expr: &ResolvedExpr) -> Option<(&FuncType, &[ResolvedExpr])> {
    match expr {
        ResolvedExpr::Call(_, ResolvedCall::Func(func_type), args)
            if func_type.subtype == FunctionSubtype::Constructor =>
        {
            Some((func_type, args.as_slice()))
        }
        _ => None,
    }
}

/// The row a `set` writes, as a call the head can evaluate: a custom function
/// stores its output as the last argument.
fn set_row_expr(
    span: &Span,
    func: &ResolvedCall,
    args: &[ResolvedExpr],
    value: &ResolvedExpr,
) -> ResolvedExpr {
    let mut row = args.to_vec();
    row.push(value.clone());
    ResolvedExpr::Call(span.clone(), func.clone(), row)
}

/// Lift each constructor-application `union` operand into a preceding `let`, so
/// every union operand is a variable and the inline and let-bound shapes coincide
/// before [`plan_construct_into`] runs.
fn normalize_union_operands(
    actions: &[ResolvedAction],
    fresh: &mut dyn FnMut() -> String,
) -> Vec<ResolvedAction> {
    let mut out = vec![];
    for action in actions {
        match action {
            ResolvedAction::Union(span, lhs, rhs) => {
                let lhs = lift_union_operand(lhs.clone(), &mut out, fresh);
                let rhs = lift_union_operand(rhs.clone(), &mut out, fresh);
                out.push(ResolvedAction::Union(span.clone(), lhs, rhs));
            }
            other => out.push(other.clone()),
        }
    }
    out
}

/// If `operand` is a constructor application, bind it to a fresh `let` (pushed
/// onto `out`) and return a variable referencing it; otherwise return `operand`
/// unchanged.
fn lift_union_operand(
    operand: ResolvedExpr,
    out: &mut Vec<ResolvedAction>,
    fresh: &mut dyn FnMut() -> String,
) -> ResolvedExpr {
    if constructor_operand(&operand).is_none() {
        return operand;
    }
    let span = operand.span();
    let var = ResolvedVar {
        name: fresh(),
        sort: operand.output_type(),
        is_global_ref: false,
    };
    out.push(ResolvedAction::Let(span.clone(), var.clone(), operand));
    GenericExpr::Var(span, var)
}

/// Plan the construct-into optimization over normalized actions (union operands
/// are variables). Returns a map from each guest variable — whose constructor is
/// built into the target's e-class instead of a fresh one — to the target
/// variable, and the set of union action indices it makes redundant.
///
/// Conservative: only a `union` of two distinct, not-yet-touched variables where
/// at least one is a constructor-`let` is optimized. The guest is the
/// later-defined constructor operand (so the target's e-class is already bound
/// where the guest is built); a matched (un-`let`) variable is always an eligible
/// target.
fn plan_construct_into(actions: &[ResolvedAction]) -> (HashMap<String, String>, HashSet<usize>) {
    let mut all_def: HashMap<String, usize> = HashMap::default();
    let mut ctor_def: HashMap<String, usize> = HashMap::default();
    for (i, action) in actions.iter().enumerate() {
        if let ResolvedAction::Let(_, v, expr) = action {
            all_def.insert(v.name.clone(), i);
            if constructor_operand(expr).is_some() {
                ctor_def.insert(v.name.clone(), i);
            }
        }
    }

    let mut construct_into: HashMap<String, String> = HashMap::default();
    let mut dropped: HashSet<usize> = HashSet::default();
    let mut used: HashSet<String> = HashSet::default();
    for (i, action) in actions.iter().enumerate() {
        let ResolvedAction::Union(_, lhs, rhs) = action else {
            continue;
        };
        let (GenericExpr::Var(_, va), GenericExpr::Var(_, vb)) = (lhs, rhs) else {
            continue;
        };
        let (a, b) = (va.name.clone(), vb.name.clone());
        if a == b {
            // Union of a variable with itself is a no-op.
            dropped.insert(i);
            continue;
        }
        if used.contains(&a) || used.contains(&b) {
            // Keep chains of optimized unions out of scope for now.
            continue;
        }
        let (guest, target) = match (ctor_def.get(&a), ctor_def.get(&b)) {
            (Some(&ia), Some(&ib)) => {
                if ia >= ib {
                    (a.clone(), b)
                } else {
                    (b, a.clone())
                }
            }
            (Some(_), None) => (a.clone(), b),
            (None, Some(_)) => (b, a.clone()),
            (None, None) => continue,
        };
        // The target's e-class must be bound where the guest is built: a matched
        // variable always is; a `let` must precede the guest's.
        let guest_idx = ctor_def[&guest];
        if let Some(&target_idx) = all_def.get(&target)
            && target_idx >= guest_idx
        {
            continue;
        }
        used.insert(guest.clone());
        used.insert(target.clone());
        construct_into.insert(guest, target);
        dropped.insert(i);
    }
    (construct_into, dropped)
}

/// One firing of a rule head, and the flat array of proofs its lowering produces.
///
/// The array is built by walking the head bottom-up: an action's operands before
/// the action, a term's children before the term, so every proof a later column
/// composes from is already in hand. Each position claims a fixed run of columns,
/// which the encoder's walk of the same head must claim the same way:
///
/// - a term the head builds: its own conclusion, that conclusion over the
///   children's representatives, and the connector to the e-class it interned
///   into — except a construct-into guest, whose run is its own conclusion, the
///   dropped `union`'s edge, the view row it writes, and its connector;
/// - any other call: its own conclusion;
/// - a `union`: its equality, then the union-find edge in each direction, routed
///   through whichever operands the head built;
/// - a `set`: its row, then the stored-value proof of a global row.
///
/// A position whose head does not produce a proof still holds its column, so the
/// numbering follows the walk rather than what either side emits.
pub(crate) struct Firing<'a> {
    rule_name: &'a str,
    plan: &'a HeadPlan,
    /// The premises the rule body matched, one per body fact.
    body_premises: Vec<ProofId>,
    substitution: IndexMap<String, TermId>,
    /// The view-row proof the head recorded at a bridge position, converted on
    /// demand. `None` for a position the requesting rule proof row does not carry.
    bridge_at: Box<dyn FnMut(&mut ProofStore, usize) -> Option<ProofId> + 'a>,
    /// What the head's variables stand for, as the walk binds them.
    bindings: HashMap<String, TermId>,
    /// A variable holding a term the head built -> that term's connector.
    connectors: HashMap<String, ProofId>,
    /// How many bridge premises the walk has asked for.
    bridges_read: usize,
    proofs: Vec<Option<ProofId>>,
    walked: bool,
}

impl<'a> Firing<'a> {
    /// `bindings` must resolve every variable the head reads: the globals plus
    /// the body's substitution.
    pub(crate) fn new(
        rule_name: &'a str,
        plan: &'a HeadPlan,
        bindings: HashMap<String, TermId>,
        body_premises: Vec<ProofId>,
        substitution: IndexMap<String, TermId>,
        bridge_at: Box<dyn FnMut(&mut ProofStore, usize) -> Option<ProofId> + 'a>,
    ) -> Self {
        Firing {
            rule_name,
            plan,
            body_premises,
            substitution,
            bridge_at,
            bindings,
            connectors: HashMap::default(),
            bridges_read: 0,
            proofs: vec![],
            walked: false,
        }
    }

    /// The proofs the head's lowering produces, by column. Empty at a column the
    /// walk numbers but the head produces no proof for.
    pub(crate) fn proofs(&mut self, store: &mut ProofStore) -> &[Option<ProofId>] {
        if !self.walked {
            self.walked = true;
            self.walk(store);
        }
        &self.proofs
    }

    /// The proof the e-graph stored in the column `raw` names.
    pub(crate) fn column(&mut self, store: &mut ProofStore, raw: i64) -> ProofId {
        let rule_name = self.rule_name;
        let column = usize::try_from(raw).unwrap_or_else(|_| {
            panic!("rule {rule_name} proof was emitted without a column ({raw})")
        });
        self.proofs(store)
            .get(column)
            .copied()
            .flatten()
            .unwrap_or_else(|| {
                panic!("rule {rule_name}'s head produces no proof at column {column}")
            })
    }

    /// Walk the head, filling the array.
    fn walk(&mut self, store: &mut ProofStore) {
        for (at, action) in self.plan.actions.iter().enumerate() {
            if self.plan.dropped.contains(&at) {
                continue;
            }
            match action {
                GenericAction::Let(_, var, expr) => {
                    let connector = match self.plan.construct_into.get(&var.name) {
                        Some(target) => self.guest(store, expr, target),
                        None => self.expr(store, expr),
                    };
                    let term = self.eval(store, expr);
                    self.bindings.insert(var.name.clone(), term);
                    if let Some(connector) = connector {
                        self.connectors.insert(var.name.clone(), connector);
                    }
                }
                GenericAction::Expr(_, expr) => {
                    self.expr(store, expr);
                }
                GenericAction::Union(_, lhs, rhs) => {
                    let lhs_connector = self.expr(store, lhs);
                    let rhs_connector = self.expr(store, rhs);
                    let lhs_term = self.eval(store, lhs);
                    let rhs_term = self.eval(store, rhs);
                    let own = self.own(store, Proposition::new(lhs_term, rhs_term));
                    match (lhs_connector, rhs_connector) {
                        // Nothing was built, so both endpoints' terms are the
                        // ones the head concluded over and the edge is that
                        // conclusion, in whichever direction the union-find asks
                        // for.
                        (None, None) => {
                            self.own(store, Proposition::new(lhs_term, rhs_term));
                            self.own(store, Proposition::new(rhs_term, lhs_term));
                        }
                        operands => self.union_edge(store, own, operands),
                    }
                }
                GenericAction::Set(span, func, args, value) => {
                    for arg in args {
                        self.expr(store, arg);
                    }
                    self.expr(store, value);
                    let row = set_row_expr(span, func, args, value);
                    let row_term = self.eval(store, &row);
                    self.own(store, Proposition::new(row_term, row_term));
                    // The stored-value column of a global row. Only a top-level
                    // action sets a global, and only a rule head is walked, so the
                    // column is held but never filled.
                    self.proofs.push(None);
                }
                GenericAction::Change(..) | GenericAction::Panic(..) => {}
            }
        }
    }

    /// Walk `expr`, and answer with its connector when it holds a term the head
    /// built.
    fn expr(&mut self, store: &mut ProofStore, expr: &ResolvedExpr) -> Option<ProofId> {
        let ResolvedExpr::Call(_, _, args) = expr else {
            // A variable's value comes from wherever it was bound; a literal
            // holds no built term.
            return match expr {
                ResolvedExpr::Var(_, var) => self.connectors.get(&var.name).copied(),
                _ => None,
            };
        };
        let steps = self.args(store, args);
        let term = self.eval(store, expr);
        let own = self.own(store, Proposition::new(term, term));
        // A primitive or a global lookup builds nothing itself, though a
        // constructor argument of it is still built.
        constructor_operand(expr)?;
        let to_canonical = store.canonicalize(own, steps);
        let canonical_reflexive = store.reflexive(to_canonical);
        self.proofs.push(Some(canonical_reflexive));
        let connector = match self.bridge(store, to_canonical) {
            Some(bridge) => store.connect(to_canonical, bridge),
            None => to_canonical,
        };
        self.proofs.push(Some(connector));
        Some(connector)
    }

    /// Walk a construct-into guest, whose constructor is built into `target`'s
    /// e-class: the dropped `union`'s edge stands in for the interning row, and
    /// the guest's view row states that e-class equals the guest's term.
    fn guest(
        &mut self,
        store: &mut ProofStore,
        expr: &ResolvedExpr,
        target: &str,
    ) -> Option<ProofId> {
        let (_, args) =
            constructor_operand(expr).expect("a construct-into guest is a constructor application");
        let steps = self.args(store, args);
        let term = self.eval(store, expr);
        let own = self.own(store, Proposition::new(term, term));
        let to_canonical = store.canonicalize(own, steps);
        let target_term = *self.bindings.get(target).unwrap_or_else(|| {
            panic!(
                "rule {}'s construct-into target {target} is unbound",
                self.rule_name
            )
        });
        let edge = self.own(store, Proposition::new(target_term, term));
        let target_connector = self.connectors.get(target).copied();
        let view = store.guest_view(edge, to_canonical, target_connector);
        self.proofs.push(Some(view));
        let connector = store.connect(to_canonical, view);
        self.proofs.push(Some(connector));
        Some(connector)
    }

    /// Walk a call's arguments, keeping the connector of each one holding a term
    /// the head built, at the position it sits in the call.
    fn args(&mut self, store: &mut ProofStore, args: &[ResolvedExpr]) -> Vec<(usize, ProofId)> {
        let mut steps = vec![];
        for (index, arg) in args.iter().enumerate() {
            if let Some(connector) = self.expr(store, arg) {
                steps.push((index, connector));
            }
        }
        steps
    }

    /// A `union`'s union-find edge, routed through the operands' written forms so
    /// both endpoints' proofs end at one shared term. Which endpoint is on the
    /// left is decided at run time by the value ordering the union-find uses, so
    /// both orientations are recorded.
    fn union_edge(
        &mut self,
        store: &mut ProofStore,
        own: ProofId,
        operands: (Option<ProofId>, Option<ProofId>),
    ) {
        let (lhs, rhs) = operands;
        let (lhs_to, rhs_to) = store.union_to_shared(own, lhs, rhs);
        for (max_pf, min_pf) in [(lhs_to, rhs_to), (rhs_to, lhs_to)] {
            let back = sym(store, min_pf);
            let edge = trans(store, max_pf, back);
            self.proofs.push(Some(edge));
        }
    }

    /// The head's own conclusion at the next column.
    fn own(&mut self, store: &mut ProofStore, proposition: Proposition) -> ProofId {
        let column = self.proofs.len() as i64;
        let id = store.push_shared_proof(
            SynthKey::Rule(
                self.rule_name.to_string(),
                column,
                self.body_premises.clone(),
            ),
            Proof {
                proposition,
                justification: Justification::Rule {
                    name: self.rule_name.to_string(),
                    premise_proofs: self.body_premises.clone(),
                    substitution: self.substitution.clone(),
                },
            },
        );
        self.proofs.push(Some(id));
        id
    }

    /// The term `expr` evaluates to under the bindings in effect.
    fn eval(&mut self, store: &mut ProofStore, expr: &ResolvedExpr) -> TermId {
        eval_expr_with_subst(self.rule_name, expr, &mut store.term_dag, &self.bindings)
            .unwrap_or_else(|err| panic!("rule {}'s head did not replay: {err}", self.rule_name))
            .0
    }

    /// The view-row proof recorded for the term the walk just built, when it says
    /// the interned term landed in an e-class whose own term is spelled
    /// differently.
    ///
    /// `None` for a term with no bridge recorded: a row minted before the head
    /// reached the subterm it is about has nothing to name yet.
    fn bridge(&mut self, store: &mut ProofStore, to_canonical: ProofId) -> Option<ProofId> {
        let position = self.bridges_read;
        self.bridges_read += 1;
        let bridge = (self.bridge_at)(store, position)?;
        // Every proof this read can return — an existing row's, a rebuilt row's, a
        // construct-into guest view, or the encoder's `can_prf` fallback — ends at
        // the canonical term. A bridge that does not is one aligned to the wrong
        // term, which would otherwise compose into a proof of the wrong equality.
        assert_eq!(
            store.get(bridge).rhs(),
            store.get(to_canonical).rhs(),
            "rule {}'s bridge {position} does not end at the canonical term",
            self.rule_name
        );
        Some(bridge)
    }
}

/// Layer 1: the equality axioms, plus the four compositions a head's lowering
/// builds out of them.
///
/// Walking a head bottom-up and applying [`Self::canonicalize`],
/// [`Self::reflexive`], [`Self::connect`] and [`Self::guest_view`] — with
/// [`Self::union_to_shared`] for a `union`'s two orientations — is the whole of
/// layer 1. The algebra is written once here and interpreted twice: for
/// [`ProofStore`] a proof is a node, so applying it builds the proof; for
/// [`ProofInstrumentor`] a proof is the name of an emitted variable, so applying
/// it writes the composition into the encoding. Same algebra, evaluated while
/// replaying a skeleton or while lowering.
///
/// A rule head is where neither happens: layer 2 writes one row per stored proof
/// and leaves the composing to conversion, so nothing here is applied (see the
/// *Proofs* part of `proof_encoding.md`).
pub(super) trait ProofAlgebra {
    type Proof: Clone;

    /// `p : a = b` reversed to `b = a`.
    fn sym(&mut self, proof: Self::Proof) -> Self::Proof;
    /// `a = b` and `b = c` joined into `a = c`.
    fn trans(&mut self, left: Self::Proof, right: Self::Proof) -> Self::Proof;
    /// `base`'s right-hand side with the child at `child` rewritten by `step`.
    fn congr(&mut self, base: Self::Proof, child: usize, step: Self::Proof) -> Self::Proof;

    /// The proof that a term the head wrote equals the same term over its
    /// children's representatives: one `congr` per child the head built.
    fn canonicalize(
        &mut self,
        own: Self::Proof,
        children: impl IntoIterator<Item = (usize, Self::Proof)>,
    ) -> Self::Proof {
        let mut to_canonical = own;
        for (child, step) in children {
            to_canonical = self.congr(to_canonical, child, step);
        }
        to_canonical
    }

    /// `t = t` for the term `to_canonical` reaches.
    fn reflexive(&mut self, to_canonical: Self::Proof) -> Self::Proof {
        let back = self.sym(to_canonical.clone());
        self.trans(back, to_canonical)
    }

    /// A built term's connector, from the term as written to the e-class the head
    /// interned it into: `dedup` states that e-class equals the canonical term, so
    /// the connector runs through the canonical term and back.
    fn connect(&mut self, to_canonical: Self::Proof, dedup: Self::Proof) -> Self::Proof {
        let back = self.sym(dedup);
        self.trans(to_canonical, back)
    }

    /// Both operands of a `union` routed to one shared term, so the union-find
    /// edge can be composed in either orientation. `own` states the union's own
    /// conclusion `lhs = rhs`, and an operand's connector is present when the head
    /// built that operand; at least one of them must have been.
    fn union_to_shared(
        &mut self,
        own: Self::Proof,
        lhs: Option<Self::Proof>,
        rhs: Option<Self::Proof>,
    ) -> (Self::Proof, Self::Proof) {
        match rhs {
            Some(rhs) => {
                let lhs_to = match lhs {
                    Some(lhs) => {
                        let back = self.sym(lhs);
                        self.trans(back, own)
                    }
                    None => own,
                };
                let rhs_to = self.sym(rhs);
                (lhs_to, rhs_to)
            }
            None => {
                let lhs = lhs.expect("one operand of the union was built");
                let lhs_to = self.sym(lhs);
                let rhs_to = self.sym(own);
                (lhs_to, rhs_to)
            }
        }
    }

    /// A construct-into guest's view-row proof: the target's e-class equals the
    /// guest's term over its children's representatives. `edge` is the dropped
    /// `union`'s equality stated `target = guest`, and `target` the target's own
    /// connector when the head built it too.
    fn guest_view(
        &mut self,
        edge: Self::Proof,
        to_canonical: Self::Proof,
        target: Option<Self::Proof>,
    ) -> Self::Proof {
        let to_dedup = self.trans(edge, to_canonical);
        match target {
            Some(target) => {
                let back = self.sym(target);
                self.trans(back, to_dedup)
            }
            None => to_dedup,
        }
    }
}

/// Applying the algebra builds the proof.
impl ProofAlgebra for ProofStore {
    type Proof = ProofId;

    fn sym(&mut self, proof: ProofId) -> ProofId {
        sym(self, proof)
    }

    fn trans(&mut self, left: ProofId, right: ProofId) -> ProofId {
        trans(self, left, right)
    }

    fn congr(&mut self, base: ProofId, child: usize, step: ProofId) -> ProofId {
        congr(self, base, child, step)
    }
}

/// Applying the algebra emits the proof: each step is a row, named by the
/// variable it binds.
impl ProofAlgebra for ProofInstrumentor<'_> {
    type Proof = String;

    fn sym(&mut self, proof: String) -> String {
        self.mint_sym(&proof)
    }

    fn trans(&mut self, left: String, right: String) -> String {
        self.mint_trans(&left, &right)
    }

    fn congr(&mut self, base: String, child: usize, step: String) -> String {
        self.mint_congr(&base, child, &step)
    }
}

/// `Sym(p)`: `p : a = b` reversed to `b = a`.
pub(super) fn sym(store: &mut ProofStore, proof: ProofId) -> ProofId {
    let prop = store.get(proof).proposition().clone();
    store.push_shared_proof(
        SynthKey::Sym(proof),
        Proof {
            proposition: Proposition::new(prop.rhs, prop.lhs),
            justification: Justification::Sym(proof),
        },
    )
}

/// `Trans(left, right)`. Panics unless the two meet at the same middle term.
pub(super) fn trans(store: &mut ProofStore, left: ProofId, right: ProofId) -> ProofId {
    let lhs = store.get(left).lhs();
    let rhs = store.get(right).rhs();
    assert_eq!(
        store.get(left).rhs(),
        store.get(right).lhs(),
        "transitivity requires matching middle terms"
    );
    store.push_shared_proof(
        SynthKey::Trans(left, right),
        Proof {
            proposition: Proposition::new(lhs, rhs),
            justification: Justification::Trans(left, right),
        },
    )
}

/// `Congr(base, child_index, child_proof)`: `base`'s right-hand side with the
/// child at `child_index` rewritten by `child_proof`.
pub(super) fn congr(
    store: &mut ProofStore,
    base: ProofId,
    child_index: usize,
    child_proof: ProofId,
) -> ProofId {
    let lhs = store.get(base).lhs();
    let base_rhs = store.get(base).rhs();
    let child_rhs = store.get(child_proof).rhs();
    let rhs = store.replace_term_child(base_rhs, child_index, child_rhs);
    store.push_shared_proof(
        SynthKey::Congr(base, child_index, child_proof),
        Proof {
            proposition: Proposition::new(lhs, rhs),
            justification: Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            },
        },
    )
}
