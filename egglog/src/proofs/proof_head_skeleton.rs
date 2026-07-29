//! How a rule head lowers, and the proof skeleton that lowering needs.
//!
//! A head that builds a term needs more proofs than it concludes: the term as
//! the head wrote it, the same term over its children's representatives, and the
//! edges between them. The e-graph records only the head's own conclusions, each
//! tagged with the [`SiteRole`] naming which of those proofs it stands for; the
//! composition is rebuilt here, at conversion time, from the role, the
//! substitution, and the rule proof's trailing *bridge* premises — the view-row
//! proof of each subterm the head interned.
//!
//! [`HeadPlan`] is the one description of how a head lowers, read by the encoder
//! and by conversion alike, so neither mirrors the other.

use std::{cell::RefCell, rc::Rc};

use crate::{
    TermId,
    ast::{
        FunctionSubtype, GenericExpr, ResolvedAction, ResolvedExpr, ResolvedExprExt, ResolvedVar,
    },
    core::ResolvedCall,
    proofs::{
        proof_format::{Justification, Proof, ProofId, ProofStore, Proposition, SynthKey},
        proof_reconstruct_check,
        proof_sites::{ActionSites, ExprSites, SiteIndex, SiteRef, SiteRole, action_sites},
    },
    typechecking::FuncType,
    util::{HashMap, HashSet, IndexMap},
};

/// A planned construct-into: the guest's constructor is built into `target`'s
/// e-class instead of a fresh one, and the `union` that said so is dropped.
pub(crate) struct ConstructInto {
    /// The variable holding the e-class the guest is built into.
    pub target: String,
    /// The dropped `union`'s conclusion site, oriented the way the guest's view
    /// row states it (`target = guest`).
    pub edge: SiteRef,
}

/// A rule head as the encoder lowers it.
pub(crate) struct HeadPlan {
    /// The head with every constructor-application `union` operand lifted into a
    /// preceding `let`, each action carrying the [`ActionSites`] of the action it
    /// came from.
    pub actions: Vec<(ResolvedAction, ActionSites)>,
    /// Guest variable -> where its constructor is built instead.
    pub construct_into: HashMap<String, ConstructInto>,
    /// Indices into [`Self::actions`] of the `union`s the plan makes redundant.
    pub dropped: HashSet<usize>,
}

impl HeadPlan {
    /// Plan `actions`. `fresh` names the lifted `let`s; only their uniqueness
    /// matters, so a consumer that wants the shape rather than the code can
    /// supply a local counter.
    pub(crate) fn new(actions: &[ResolvedAction], fresh: &mut dyn FnMut() -> String) -> Self {
        let lowered = normalize_union_operands(actions, fresh);
        let (construct_into, dropped) = plan_construct_into(&lowered);
        HeadPlan {
            actions: lowered,
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

/// Lift each constructor-application `union` operand into a preceding `let`, so
/// every union operand is a variable and the inline and let-bound shapes coincide
/// before [`plan_construct_into`] runs.
///
/// Each output action keeps the [`ActionSites`] of the action it came from, so
/// every conclusion the encoder emits still names a site of the head as
/// written — lifting an operand shifts no index.
fn normalize_union_operands(
    actions: &[ResolvedAction],
    fresh: &mut dyn FnMut() -> String,
) -> Vec<(ResolvedAction, ActionSites)> {
    let mut out = vec![];
    for (action, sites) in actions.iter().zip(action_sites(actions)) {
        match action {
            ResolvedAction::Union(span, lhs, rhs) => {
                let ActionSites { own, operands } = sites;
                let [lhs_sites, rhs_sites] = <[ExprSites; 2]>::try_from(operands)
                    .expect("a union contributes sites for both operands");
                let lhs = lift_union_operand(lhs.clone(), &lhs_sites, &mut out, fresh);
                let rhs = lift_union_operand(rhs.clone(), &rhs_sites, &mut out, fresh);
                out.push((
                    ResolvedAction::Union(span.clone(), lhs, rhs),
                    ActionSites {
                        own,
                        operands: vec![lhs_sites, rhs_sites],
                    },
                ));
            }
            other => out.push((other.clone(), sites)),
        }
    }
    out
}

/// If `operand` is a constructor application, bind it to a fresh `let` (pushed
/// onto `out` carrying `sites`) and return a variable referencing it; otherwise
/// return `operand` unchanged.
fn lift_union_operand(
    operand: ResolvedExpr,
    sites: &ExprSites,
    out: &mut Vec<(ResolvedAction, ActionSites)>,
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
    out.push((
        ResolvedAction::Let(span.clone(), var.clone(), operand),
        ActionSites {
            own: None,
            operands: vec![sites.clone()],
        },
    ));
    GenericExpr::Var(span, var)
}

/// Plan the construct-into optimization over normalized actions (union operands
/// are variables). Returns a map from each guest variable — whose constructor is
/// built into the target's e-class instead of a fresh one — to its
/// [`ConstructInto`], and the set of union action indices it makes redundant.
///
/// Conservative: only a `union` of two distinct, not-yet-touched variables where
/// at least one is a constructor-`let` is optimized. The guest is the
/// later-defined constructor operand (so the target's e-class is already bound
/// where the guest is built); a matched (un-`let`) variable is always an eligible
/// target.
fn plan_construct_into(
    actions: &[(ResolvedAction, ActionSites)],
) -> (HashMap<String, ConstructInto>, HashSet<usize>) {
    let mut all_def: HashMap<String, usize> = HashMap::default();
    let mut ctor_def: HashMap<String, usize> = HashMap::default();
    for (i, (action, _)) in actions.iter().enumerate() {
        if let ResolvedAction::Let(_, v, expr) = action {
            all_def.insert(v.name.clone(), i);
            if constructor_operand(expr).is_some() {
                ctor_def.insert(v.name.clone(), i);
            }
        }
    }

    let mut construct_into: HashMap<String, ConstructInto> = HashMap::default();
    let mut dropped: HashSet<usize> = HashSet::default();
    let mut used: HashSet<String> = HashSet::default();
    for (i, (action, sites)) in actions.iter().enumerate() {
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
        // Dropping the union leaves its equality as the guest's view-row proof,
        // stated `target = guest`. The site states it `lhs = rhs`, so it is
        // reversed exactly when the guest is the union's lhs.
        let edge = SiteRef {
            index: sites
                .own
                .expect("a union contributes a site for its equality"),
            reversed: guest == a,
            role: SiteRole::AsWritten,
        };
        used.insert(guest.clone());
        used.insert(target.clone());
        construct_into.insert(guest, ConstructInto { target, edge });
        dropped.insert(i);
    }
    (construct_into, dropped)
}

/// The expressions an action evaluates, in the order [`action_sites`] lists
/// them. `change` and `panic` contribute none — `change` concludes nothing, so
/// its arguments name no site.
fn action_operands(action: &ResolvedAction) -> Box<dyn Iterator<Item = &ResolvedExpr> + '_> {
    match action {
        ResolvedAction::Let(_, _, expr) | ResolvedAction::Expr(_, expr) => {
            Box::new(std::iter::once(expr))
        }
        ResolvedAction::Union(_, lhs, rhs) => Box::new([lhs, rhs].into_iter()),
        ResolvedAction::Set(_, _, args, value) => {
            Box::new(args.iter().chain(std::iter::once(value)))
        }
        ResolvedAction::Change(..) | ResolvedAction::Panic(..) => Box::new(std::iter::empty()),
    }
}

/// Where a build site's children come from, and what it is built into.
#[derive(Clone)]
struct BuildSite {
    /// Per child, in order: the build site its value comes from, or `None` when
    /// the child is a leaf the head did not build.
    children: Vec<Option<SiteIndex>>,
    /// Set when the site is a construct-into guest: the dropped `union`'s site,
    /// oriented `target = guest`, and the target's build site if the head built
    /// it too.
    guest_of: Option<(SiteRef, Option<SiteIndex>)>,
}

/// A head's build sites, indexed the way a rule proof names them.
#[derive(Clone, Default)]
pub(crate) struct BuildSites {
    sites: HashMap<SiteIndex, BuildSite>,
    /// A dropped `union`'s site -> the guest built into its other operand.
    guest_at_union: HashMap<SiteIndex, SiteIndex>,
    /// A kept `union`'s site -> its two operands' build sites.
    unions: HashMap<SiteIndex, (Option<SiteIndex>, Option<SiteIndex>)>,
    /// A global `set`'s row site -> the build site of the value it aliases.
    globals: HashMap<SiteIndex, Option<SiteIndex>>,
    /// The build sites that record a bridge premise, in construction order.
    bridge_order: Vec<SiteIndex>,
}

/// Index `plan`'s build sites: actions in order, and within an action the
/// post-order of its constructor applications (children before the node), which
/// is the order the encoder builds them and therefore the order a rule proof's
/// trailing bridge premises are recorded in.
///
/// A construct-into guest records no bridge: its representative is the target's
/// e-class, which the dropped `union`'s site already names, so the encoder reads
/// no view-row proof for it.
pub(crate) fn build_sites(plan: &HeadPlan) -> BuildSites {
    let mut out = BuildSites::default();
    // A `let`-bound name -> the build site whose value it holds.
    let mut bound: HashMap<String, SiteIndex> = HashMap::default();
    for (at, (action, sites)) in plan.actions.iter().enumerate() {
        if plan.dropped.contains(&at) {
            continue;
        }
        let guest = match action {
            ResolvedAction::Let(_, v, _) => plan.construct_into.get(&v.name),
            _ => None,
        };
        for (expr, expr_sites) in action_operands(action).zip(&sites.operands) {
            walk_build_sites(expr, expr_sites, guest.is_some(), &bound, &mut out);
        }
        match action {
            ResolvedAction::Let(_, v, expr) => {
                if let Some(site) = value_site(expr, sites.operands.first(), &bound) {
                    if let Some(plan) = guest {
                        let target = bound.get(&plan.target).copied();
                        out.sites
                            .get_mut(&site)
                            .expect("a construct-into guest is a build site")
                            .guest_of = Some((plan.edge, target));
                        out.guest_at_union.insert(plan.edge.index, site);
                    }
                    bound.insert(v.name.clone(), site);
                }
            }
            ResolvedAction::Union(_, lhs, rhs) => {
                let own = sites
                    .own
                    .expect("a union contributes a site for its equality");
                let operands = (
                    value_site(lhs, sites.operands.first(), &bound),
                    value_site(rhs, sites.operands.get(1), &bound),
                );
                out.unions.insert(own, operands);
            }
            ResolvedAction::Set(_, _, args, value) if args.is_empty() => {
                let own = sites.own.expect("a set contributes a site for its row");
                out.globals
                    .insert(own, value_site(value, sites.operands.first(), &bound));
            }
            _ => {}
        }
    }
    out
}

/// Record `expr`'s constructor applications post-order. `skip_root` leaves out
/// the top node, whose build the caller handles (a construct-into guest).
fn walk_build_sites(
    expr: &ResolvedExpr,
    sites: &ExprSites,
    skip_root: bool,
    bound: &HashMap<String, SiteIndex>,
    out: &mut BuildSites,
) {
    let Some((_, args)) = constructor_operand(expr) else {
        // A primitive or a global lookup builds nothing itself, but a
        // constructor argument of it is still built.
        if let ResolvedExpr::Call(_, _, args) = expr {
            for (arg, arg_sites) in args.iter().zip(&sites.operands) {
                walk_build_sites(arg, arg_sites, false, bound, out);
            }
        }
        return;
    };
    for (arg, arg_sites) in args.iter().zip(&sites.operands) {
        walk_build_sites(arg, arg_sites, false, bound, out);
    }
    let children = args
        .iter()
        .zip(&sites.operands)
        .map(|(arg, arg_sites)| value_site(arg, Some(arg_sites), bound))
        .collect();
    out.sites.insert(
        sites.index,
        BuildSite {
            children,
            guest_of: None,
        },
    );
    if !skip_root {
        out.bridge_order.push(sites.index);
    }
}

/// The build site an expression's value comes from, if the head built it: the
/// expression's own site when it is a constructor application, or the site the
/// variable it names was bound to.
fn value_site(
    expr: &ResolvedExpr,
    sites: Option<&ExprSites>,
    bound: &HashMap<String, SiteIndex>,
) -> Option<SiteIndex> {
    match expr {
        ResolvedExpr::Var(_, v) => bound.get(&v.name).copied(),
        _ if constructor_operand(expr).is_some() => Some(sites?.index),
        _ => None,
    }
}

/// The build sites a proof about `site` is composed from — the ones whose
/// bridge premises conversion has to read. A proof stating only the head's own
/// conclusion needs none.
pub(crate) fn sites_needed(sites: &BuildSites, site: SiteRef) -> Vec<SiteIndex> {
    let mut out = vec![];
    match site.role {
        SiteRole::AsWritten => {}
        SiteRole::CanonicalReflexive | SiteRole::Connector => closure(sites, site.index, &mut out),
        SiteRole::GuestView | SiteRole::GuestConnector => {
            if let Some(&guest) = sites.guest_at_union.get(&site.index) {
                closure(sites, guest, &mut out);
            }
        }
        SiteRole::UnionEdge => {
            let (lhs, rhs) = sites
                .unions
                .get(&site.index)
                .copied()
                .unwrap_or((None, None));
            for operand in [lhs, rhs].into_iter().flatten() {
                closure(sites, operand, &mut out);
            }
        }
        SiteRole::GlobalValue => {
            if let Some(Some(value)) = sites.globals.get(&site.index).copied() {
                closure(sites, value, &mut out);
            }
        }
    }
    out
}

fn closure(sites: &BuildSites, site: SiteIndex, out: &mut Vec<SiteIndex>) {
    if out.contains(&site) {
        return;
    }
    out.push(site);
    let Some(build) = sites.sites.get(&site) else {
        return;
    };
    for child in build.children.iter().flatten() {
        closure(sites, *child, out);
    }
    if let Some((_, Some(target))) = build.guest_of {
        closure(sites, target, out);
    }
}

impl BuildSites {
    /// Where `site`'s bridge premise sits in a rule proof's bridge list, counted
    /// from the list's end (the list is consed onto as the head builds, so the
    /// oldest bridge is last). `None` for a site that records no bridge.
    pub(crate) fn bridge_position(&self, site: SiteIndex) -> Option<usize> {
        self.bridge_order.iter().position(|s| *s == site)
    }
}

/// What one firing of a rule head recorded.
pub(crate) struct FiringRecord<'a> {
    pub rule_name: &'a str,
    pub build_sites: Rc<BuildSites>,
    /// The head's as-written propositions, in `conclusion_sites` order.
    pub site_props: Vec<(SiteIndex, Proposition)>,
    /// The premises the rule body matched, one per body fact.
    pub body_premises: Vec<ProofId>,
    /// The view-row proof of each interned subterm the composition needs, by
    /// build site.
    pub bridges: HashMap<SiteIndex, ProofId>,
    pub substitution: IndexMap<String, TermId>,
}

/// A firing, owned so a [`HeadSkeleton`] can be cached across the rows the firing
/// wrote.
struct Firing {
    rule_name: String,
    sites: Rc<BuildSites>,
    site_props: Vec<(SiteIndex, Proposition)>,
    body_premises: Vec<ProofId>,
    substitution: IndexMap<String, TermId>,
    bridges: HashMap<SiteIndex, ProofId>,
}

/// One side of a built term's proof composition: the encoder, which names a
/// proof by the variable it emits, and proof conversion, which names one by its
/// node in a [`ProofStore`].
pub(crate) trait HeadSink {
    /// How this side names a proof.
    type Proof: Clone;

    /// Whether this side composes the skeleton at all. A rule head does not: it
    /// records one row per [`SiteRole`] it stores and leaves the composition to
    /// proof conversion.
    fn composes(&self) -> bool;

    /// The proof this side names for a role it does not compose. Only reached
    /// when [`Self::composes`] is false, and only for a role whose row is always
    /// stored — a role whose row is minted on first read stays with the caller.
    fn roled(&mut self, role: SiteRole) -> Self::Proof;

    /// `Congr(acc, index, step)`, rewriting `acc`'s right-hand side at `index`.
    fn congr(&mut self, acc: Self::Proof, index: usize, step: Self::Proof) -> Self::Proof;
    /// `Sym(proof)`.
    fn sym(&mut self, proof: Self::Proof) -> Self::Proof;
    /// `Trans(left, right)`.
    fn trans(&mut self, left: Self::Proof, right: Self::Proof) -> Self::Proof;
}

/// The proofs a built constructor term needs beyond the head's own conclusion
/// at that position.
pub(crate) struct BuiltTerm<P> {
    /// `canonical = canonical`.
    pub canonical_reflexive: P,
    /// `written = interned`: the edge to the e-class the term was interned into.
    /// `None` on a side that records the position instead of composing, whose
    /// row for it is minted only where something reads it.
    pub connector: Option<P>,
}

/// `written = canonical`: the term as written equals the same term over its
/// children's representatives, one `Congr` per child that needed one.
pub(crate) fn congr_chain<S: HeadSink>(
    sink: &mut S,
    own: S::Proof,
    child_connectors: &[Option<S::Proof>],
) -> S::Proof {
    let mut chain = own;
    for (index, connector) in child_connectors.iter().enumerate() {
        if let Some(connector) = connector {
            chain = sink.congr(chain, index, connector.clone());
        }
    }
    chain
}

/// Compose the proofs a built constructor term needs, from the head's own
/// conclusion at that position and its children's connectors.
///
/// `intern` interns the canonical term, taking the two proofs composed so far —
/// the [`congr_chain`], and [`BuiltTerm::canonical_reflexive`], the one the
/// interning row carries — and answers with the interning row's proof when the
/// row states an e-class the canonical term is not itself spelled by. Answering
/// `None` leaves the term its own representative.
pub(crate) fn compose_built_term<S: HeadSink>(
    sink: &mut S,
    own: S::Proof,
    child_connectors: &[Option<S::Proof>],
    intern: impl FnOnce(&mut S, Option<&S::Proof>, &S::Proof) -> Option<S::Proof>,
) -> BuiltTerm<S::Proof> {
    if !sink.composes() {
        let canonical_reflexive = sink.roled(SiteRole::CanonicalReflexive);
        intern(sink, None, &canonical_reflexive);
        return BuiltTerm {
            canonical_reflexive,
            connector: None,
        };
    }
    let to_canonical = congr_chain(sink, own, child_connectors);
    let back = sink.sym(to_canonical.clone());
    let canonical_reflexive = sink.trans(back, to_canonical.clone());
    let connector = match intern(sink, Some(&to_canonical), &canonical_reflexive) {
        Some(row) => {
            let back = sink.sym(row);
            sink.trans(to_canonical, back)
        }
        None => to_canonical,
    };
    BuiltTerm {
        canonical_reflexive,
        connector: Some(connector),
    }
}

/// A construct-into guest's view-row proof: the target's e-class equals the
/// guest's term over its children's representatives.
pub(crate) fn compose_guest_view<S: HeadSink>(
    sink: &mut S,
    edge: S::Proof,
    to_canonical: S::Proof,
    target_connector: Option<S::Proof>,
) -> S::Proof {
    let to_dedup = sink.trans(edge, to_canonical);
    match target_connector {
        Some(connector) => {
            let back = sink.sym(connector);
            sink.trans(back, to_dedup)
        }
        None => to_dedup,
    }
}

/// Proof conversion's [`HeadSink`]: a proof is a node, and a congruence's
/// right-hand side follows from the terms the store already holds.
pub(super) struct StoreSink<'a>(pub &'a mut ProofStore);

impl HeadSink for StoreSink<'_> {
    type Proof = ProofId;

    fn composes(&self) -> bool {
        true
    }

    fn roled(&mut self, role: SiteRole) -> ProofId {
        unreachable!("proof conversion composes {role:?} rather than naming a row for it")
    }

    fn congr(&mut self, acc: ProofId, index: usize, step: ProofId) -> ProofId {
        congr(self.0, acc, index, step)
    }

    fn sym(&mut self, proof: ProofId) -> ProofId {
        sym(self.0, proof)
    }

    fn trans(&mut self, left: ProofId, right: ProofId) -> ProofId {
        trans(self.0, left, right)
    }
}

/// The proofs one firing of a rule head produced, keyed the way the e-graph names
/// them.
///
/// Built on demand: a firing writes a few of the propositions its sites have, and
/// materializing the rest would cost a proof node — with a copy of the
/// substitution — per site per firing.
pub(crate) struct HeadSkeleton {
    firing: Firing,
    state: RefCell<State>,
}

#[derive(Default)]
struct State {
    roles: HashMap<(SiteIndex, SiteRole, bool), ProofId>,
    /// A build site -> its connector, `written = interned`.
    resolved: HashMap<SiteIndex, ProofId>,
}

impl HeadSkeleton {
    /// Record one firing. Nothing is built until [`Self::role`] asks for it.
    pub(crate) fn new(record: FiringRecord) -> Rc<Self> {
        let bridges = record.bridges;
        Rc::new(HeadSkeleton {
            firing: Firing {
                rule_name: record.rule_name.to_string(),
                sites: record.build_sites.clone(),
                site_props: record.site_props,
                body_premises: record.body_premises,
                substitution: record.substitution,
                bridges,
            },
            state: RefCell::new(State::default()),
        })
    }

    /// The proof the e-graph stored for `site`, stated the way `site` states it.
    pub(crate) fn role(&self, store: &mut ProofStore, site: SiteRef) -> ProofId {
        let mut state = self.state.borrow_mut();
        Builder {
            firing: &self.firing,
            state: &mut state,
        }
        .role(store, site)
    }
}

struct Builder<'a> {
    firing: &'a Firing,
    state: &'a mut State,
}

impl Builder<'_> {
    fn role(&mut self, store: &mut ProofStore, site: SiteRef) -> ProofId {
        if let Some(&id) = self
            .state
            .roles
            .get(&(site.index, site.role, site.reversed))
        {
            return id;
        }
        match site.role {
            SiteRole::AsWritten => self.base(store, site.index, site.reversed),
            SiteRole::CanonicalReflexive | SiteRole::Connector => {
                self.resolve(store, site.index);
                self.recorded(site)
            }
            SiteRole::GuestView | SiteRole::GuestConnector => {
                let guest = *self
                    .firing
                    .sites
                    .guest_at_union
                    .get(&site.index)
                    .unwrap_or_else(|| {
                        panic!(
                            "rule {}'s union at site {} builds no guest",
                            self.firing.rule_name, site.index.0
                        )
                    });
                self.resolve(store, guest);
                self.recorded(site)
            }
            SiteRole::UnionEdge => {
                let operands = self.firing.sites.unions[&site.index];
                self.union_edge(store, site.index, operands);
                self.recorded(site)
            }
            SiteRole::GlobalValue => {
                let value = self.firing.sites.globals[&site.index];
                self.global_value(store, site.index, value);
                self.recorded(site)
            }
        }
    }

    /// A role the resolution above must have recorded.
    fn recorded(&self, site: SiteRef) -> ProofId {
        *self
            .state
            .roles
            .get(&(site.index, site.role, site.reversed))
            .unwrap_or_else(|| {
                panic!(
                    "rule {}'s head builds no {:?} proof at site {}",
                    self.firing.rule_name, site.role, site.index.0
                )
            })
    }

    /// The head's own conclusion at `site`, cached so every composite over it
    /// shares one node.
    fn base(&mut self, store: &mut ProofStore, site: SiteIndex, reversed: bool) -> ProofId {
        let key = (site, SiteRole::AsWritten, reversed);
        if let Some(&id) = self.state.roles.get(&key) {
            return id;
        }
        let reference = SiteRef {
            index: site,
            reversed,
            role: SiteRole::AsWritten,
        };
        let proposition = self
            .firing
            .site_props
            .iter()
            .find_map(|(index, prop)| (*index == site).then(|| reference.orient(prop)))
            .unwrap_or_else(|| {
                panic!(
                    "rule {} has no conclusion site {}",
                    self.firing.rule_name, site.0
                )
            });
        let id = store.push_shared_proof(
            SynthKey::Rule(
                self.firing.rule_name.clone(),
                reference,
                self.firing.body_premises.clone(),
            ),
            Proof {
                proposition,
                justification: Justification::Rule {
                    name: self.firing.rule_name.clone(),
                    premise_proofs: self.firing.body_premises.clone(),
                    substitution: self.firing.substitution.clone(),
                    site: reference,
                },
            },
        );
        self.state.roles.insert(key, id);
        id
    }

    /// Resolve a build site: fold one `Congr` per built child onto the site's own
    /// conclusion, then settle which e-class the interned term landed in.
    fn resolve(&mut self, store: &mut ProofStore, site: SiteIndex) -> ProofId {
        if let Some(&connector) = self.state.resolved.get(&site) {
            return connector;
        }
        let build = self.firing.sites.sites[&site].clone();
        let base = self.base(store, site, false);
        let child_connectors: Vec<Option<ProofId>> = build
            .children
            .iter()
            .map(|child| child.map(|child| self.resolve(store, child)))
            .collect();

        let built = compose_built_term(
            &mut StoreSink(store),
            base,
            &child_connectors,
            |sink, to_canonical, _reflexive| {
                let to_canonical = *to_canonical.expect("proof conversion composes the chain");
                match build.guest_of {
                    Some((edge, target)) => {
                        Some(self.guest_view(sink.0, edge, target, to_canonical))
                    }
                    None => {
                        let canonical = sink.0.get(to_canonical).rhs();
                        self.bridge(sink.0, site, canonical)
                    }
                }
            },
        );

        let connector = built
            .connector
            .expect("proof conversion composes the connector");
        if let Some((edge, _)) = build.guest_of {
            self.state.roles.insert(
                (edge.index, SiteRole::GuestConnector, edge.reversed),
                connector,
            );
        }
        self.state.roles.insert(
            (site, SiteRole::CanonicalReflexive, false),
            built.canonical_reflexive,
        );
        self.state
            .roles
            .insert((site, SiteRole::Connector, false), connector);
        self.state.resolved.insert(site, connector);
        connector
    }

    /// The view-row proof recorded for `site`, when it says the interned term
    /// landed in an e-class whose own term is spelled differently.
    ///
    /// A row the head's own `set-if-empty` seeded is absent when the encoder reads
    /// it, so the read returns its fallback — a proof about the term as written,
    /// not about the canonical one. That is the discriminator: only a proof whose
    /// right-hand side *is* the canonical term states which e-class the canonical
    /// term was interned into.
    fn bridge(
        &self,
        store: &mut ProofStore,
        site: SiteIndex,
        canonical: TermId,
    ) -> Option<ProofId> {
        let bridge = *self.firing.bridges.get(&site)?;
        let prop = store.get(bridge).proposition();
        if prop.rhs != canonical {
            return None;
        }
        let moved = prop.lhs != prop.rhs;
        proof_reconstruct_check::record_head_bridge(&self.firing.rule_name, moved);
        Some(bridge)
    }

    /// A construct-into guest's view-row proof: the target's e-class equals the
    /// guest's term over its children's representatives.
    fn guest_view(
        &mut self,
        store: &mut ProofStore,
        edge: SiteRef,
        target: Option<SiteIndex>,
        to_canonical: ProofId,
    ) -> ProofId {
        let edge_proof = self.base(store, edge.index, edge.reversed);
        let target = target.map(|target| self.resolve(store, target));
        let view = compose_guest_view(&mut StoreSink(store), edge_proof, to_canonical, target);
        self.state
            .roles
            .insert((edge.index, SiteRole::GuestView, edge.reversed), view);
        view
    }

    /// A kept `union`'s union-find edge, routed through the operands' written forms
    /// so both endpoints' proofs end at one shared term. Which endpoint is on the
    /// left is decided at run time by the value ordering the union-find uses, so
    /// both orientations are recorded.
    fn union_edge(
        &mut self,
        store: &mut ProofStore,
        union: SiteIndex,
        operands: (Option<SiteIndex>, Option<SiteIndex>),
    ) {
        let (lhs, rhs) = operands;
        let base = self.base(store, union, false);
        let lhs_conn = lhs.map(|s| self.resolve(store, s));
        let rhs_conn = rhs.map(|s| self.resolve(store, s));
        let (lhs_to, rhs_to) = match rhs_conn {
            Some(rhs_conn) => {
                let lhs_to = match lhs_conn {
                    Some(lhs_conn) => {
                        let back = sym(store, lhs_conn);
                        trans(store, back, base)
                    }
                    None => base,
                };
                let rhs_to = sym(store, rhs_conn);
                (lhs_to, rhs_to)
            }
            None => {
                let lhs_conn = lhs_conn.expect("one operand of the union was built");
                let lhs_to = sym(store, lhs_conn);
                let rhs_to = sym(store, base);
                (lhs_to, rhs_to)
            }
        };
        for (reversed, max_pf, min_pf) in [(false, lhs_to, rhs_to), (true, rhs_to, lhs_to)] {
            let back = sym(store, min_pf);
            let edge = trans(store, max_pf, back);
            self.state
                .roles
                .insert((union, SiteRole::UnionEdge, reversed), edge);
        }
    }

    /// A global's stored value proof: the value equals itself, routed through the
    /// written form of the term it aliases.
    fn global_value(&mut self, store: &mut ProofStore, row: SiteIndex, value: Option<SiteIndex>) {
        let value = value.expect("a roled global proof needs a built value");
        let connector = self.resolve(store, value);
        let proof = reflexivize(store, connector);
        self.state
            .roles
            .insert((row, SiteRole::GlobalValue, false), proof);
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

/// `Trans(Sym(p), p)`: `p : a = b` reflexivized to `b = b`.
fn reflexivize(store: &mut ProofStore, proof: ProofId) -> ProofId {
    let back = sym(store, proof);
    trans(store, back, proof)
}
