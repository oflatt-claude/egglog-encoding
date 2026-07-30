//! How a rule head lowers, and the proofs that lowering composes.
//!
//! A head that builds a term needs more proofs than it concludes: the term as
//! the head wrote it, the same term over its children's representatives, and the
//! edges between them. The e-graph records only the head's own conclusions, each
//! tagged with the [`SiteRole`] naming which of those proofs it stands for; the
//! composition is rebuilt here, at conversion time, from the role, the
//! substitution, and the rule proof's trailing *bridge* premises — the view-row
//! proof of each subterm the head interned.
//!
//! [`HeadPlan`] is the head as the encoder lowers it, read by the encoder and by
//! conversion alike; what a site composes from is read off that head's syntax.
//! The numbering itself comes from [`crate::proofs::proof_sites`]; the walks here
//! re-derive its order by counting and check the count against that module's site
//! list.

use crate::{
    TermId,
    ast::{
        FunctionSubtype, GenericExpr, ResolvedAction, ResolvedExpr, ResolvedExprExt, ResolvedVar,
    },
    core::ResolvedCall,
    proofs::{
        proof_format::{Justification, Proof, ProofId, ProofStore, Proposition, SynthKey},
        proof_sites::{ActionSites, SiteIndex, SiteRef, SiteRole, action_sites},
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

/// A rule head as the encoder lowers it, and the site numbering both the encoder
/// and proof conversion read it by.
pub(crate) struct HeadPlan {
    /// The head with every constructor-application `union` operand lifted into a
    /// preceding `let`, each action carrying the [`ActionSites`] of the action it
    /// came from.
    pub actions: Vec<(ResolvedAction, ActionSites)>,
    /// Guest variable -> where its constructor is built instead.
    pub construct_into: HashMap<String, ConstructInto>,
    /// Indices into [`Self::actions`] of the `union`s the plan makes redundant.
    pub dropped: HashSet<usize>,
    /// The build sites that record a bridge premise, in construction order.
    bridge_order: Vec<SiteIndex>,
    /// A `let`-bound name -> the build site whose value it holds.
    bound: HashMap<String, SiteIndex>,
}

impl HeadPlan {
    /// Plan `actions`. `fresh` names the lifted `let`s; only their uniqueness
    /// matters, so a consumer that wants the shape rather than the code can
    /// supply a local counter.
    pub(crate) fn new(actions: &[ResolvedAction], fresh: &mut dyn FnMut() -> String) -> Self {
        let lowered = normalize_union_operands(actions, fresh);
        let (construct_into, dropped) = plan_construct_into(&lowered);
        let mut plan = HeadPlan {
            actions: lowered,
            construct_into,
            dropped,
            bridge_order: Vec::new(),
            bound: HashMap::default(),
        };
        index_builds(&mut plan);
        plan
    }

    /// Where `site`'s bridge premise sits in a rule proof's bridge list, which is
    /// in construction order. `None` for a site that records no bridge.
    fn bridge_position(&self, site: SiteIndex) -> Option<usize> {
        self.bridge_order.iter().position(|s| *s == site)
    }

    /// Each expression an action the plan keeps evaluates, with the site it
    /// starts at.
    fn operands(&self) -> impl Iterator<Item = (&ResolvedExpr, SiteIndex)> {
        self.actions
            .iter()
            .enumerate()
            .filter(|(at, _)| !self.dropped.contains(at))
            .flat_map(|(_, (action, sites))| {
                action_operands(action).zip(sites.operands.iter().copied())
            })
    }

    /// The expression the head evaluates at `site`.
    fn expr_at(&self, site: SiteIndex) -> Option<&ResolvedExpr> {
        self.operands()
            .find_map(|(expr, start)| expr_at(expr, start, site))
    }

    /// The action whose own conclusion is `site`, with that action's sites.
    fn concluding(&self, site: SiteIndex) -> Option<&(ResolvedAction, ActionSites)> {
        self.actions
            .iter()
            .enumerate()
            .find(|(at, (_, sites))| !self.dropped.contains(at) && sites.own == Some(site))
            .map(|(_, entry)| entry)
    }

    /// The build site whose value `expr`, positioned at `site`, holds: a
    /// variable's is the one it was bound to, a constructor application's is its
    /// own, and anything else holds no built value.
    fn value_site(&self, expr: &ResolvedExpr, site: SiteIndex) -> Option<SiteIndex> {
        match expr {
            ResolvedExpr::Var(_, v) => self.bound.get(&v.name).copied(),
            _ => constructor_operand(expr).map(|_| site),
        }
    }

    /// The dropped `union` whose guest the head builds at `site`, oriented
    /// `target = guest`, and the target's own build site.
    fn guest_of(&self, site: SiteIndex) -> Option<(SiteRef, Option<SiteIndex>)> {
        self.actions.iter().find_map(|(action, sites)| {
            let ResolvedAction::Let(_, v, _) = action else {
                return None;
            };
            let into = self.construct_into.get(&v.name)?;
            (sites.operands.first().copied() == Some(site))
                .then(|| (into.edge, self.bound.get(&into.target).copied()))
        })
    }

    /// The build site of the guest the `union` at `site` was dropped for.
    fn guest_at(&self, site: SiteIndex) -> Option<SiteIndex> {
        let (guest, _) = self
            .construct_into
            .iter()
            .find(|(_, into)| into.edge.index == site)?;
        self.bound.get(guest).copied()
    }

    /// The build sites the `union` at `site` unions, in the order written.
    fn union_operands(&self, site: SiteIndex) -> Option<[Option<SiteIndex>; 2]> {
        let (action, sites) = self.concluding(site)?;
        let ResolvedAction::Union(_, lhs, rhs) = action else {
            return None;
        };
        let [lhs_site, rhs_site] = <[SiteIndex; 2]>::try_from(sites.operands.clone()).ok()?;
        Some([
            self.value_site(lhs, lhs_site),
            self.value_site(rhs, rhs_site),
        ])
    }

    /// The build site of the value the global `set` at `site` stores.
    fn global_value(&self, site: SiteIndex) -> Option<SiteIndex> {
        let (action, sites) = self.concluding(site)?;
        let ResolvedAction::Set(_, _, args, value) = action else {
            return None;
        };
        args.is_empty()
            .then(|| self.value_site(value, *sites.operands.first()?))
            .flatten()
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
                let [lhs_site, rhs_site] = <[SiteIndex; 2]>::try_from(operands)
                    .expect("a union contributes sites for both operands");
                let lhs = lift_union_operand(lhs.clone(), lhs_site, &mut out, fresh);
                let rhs = lift_union_operand(rhs.clone(), rhs_site, &mut out, fresh);
                out.push((
                    ResolvedAction::Union(span.clone(), lhs, rhs),
                    ActionSites {
                        own,
                        operands: vec![lhs_site, rhs_site],
                    },
                ));
            }
            other => out.push((other.clone(), sites)),
        }
    }
    out
}

/// If `operand` is a constructor application, bind it to a fresh `let` (pushed
/// onto `out` carrying `site`) and return a variable referencing it; otherwise
/// return `operand` unchanged.
fn lift_union_operand(
    operand: ResolvedExpr,
    site: SiteIndex,
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
            operands: vec![site],
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

/// How many conclusion sites `expr` occupies: one per node, in pre-order.
fn site_count(expr: &ResolvedExpr) -> usize {
    match expr {
        ResolvedExpr::Call(_, _, args) => 1 + args.iter().map(site_count).sum::<usize>(),
        _ => 1,
    }
}

/// The subexpression of `expr` — which starts at site `start` — at site `want`.
fn expr_at(expr: &ResolvedExpr, start: SiteIndex, want: SiteIndex) -> Option<&ResolvedExpr> {
    if start == want {
        return Some(expr);
    }
    let ResolvedExpr::Call(_, _, args) = expr else {
        return None;
    };
    let mut next = start.0 + 1;
    for arg in args {
        let end = next + site_count(arg);
        if want.0 < end {
            return expr_at(arg, SiteIndex(next), want);
        }
        next = end;
    }
    None
}

/// Number `plan`'s bridge premises and its `let` bindings: actions in order, and
/// within an action the post-order of its constructor applications (children
/// before the node), which is the order the encoder builds them and therefore the
/// order a rule proof's trailing bridge premises are recorded in.
///
/// A construct-into guest records no bridge: its representative is the target's
/// e-class, which the dropped `union`'s site already names, so the encoder reads
/// no view-row proof for it.
fn index_builds(plan: &mut HeadPlan) {
    let mut bridge_order: Vec<SiteIndex> = Vec::new();
    let mut bound: HashMap<String, SiteIndex> = HashMap::default();
    for (at, (action, sites)) in plan.actions.iter().enumerate() {
        if plan.dropped.contains(&at) {
            continue;
        }
        let is_guest = matches!(action, ResolvedAction::Let(_, v, _)
            if plan.construct_into.contains_key(&v.name));
        let operands: Vec<&ResolvedExpr> = action_operands(action).collect();
        assert_eq!(
            operands.len(),
            sites.operands.len(),
            "an action's operands must match the sites numbered for it"
        );
        let mut values = Vec::with_capacity(operands.len());
        for (expr, site) in operands.into_iter().zip(&sites.operands) {
            values.push(record_bridges(
                expr,
                *site,
                is_guest,
                &bound,
                &mut bridge_order,
            ));
        }
        if let ResolvedAction::Let(_, v, _) = action
            && let Some(site) = values[0]
        {
            bound.insert(v.name.clone(), site);
        }
    }
    plan.bridge_order = bridge_order;
    plan.bound = bound;
}

/// Record the bridge premises `expr`'s constructor applications write, post-order,
/// and return the build site `expr`'s value comes from. `expr` starts at site
/// `site`. `skip_root` leaves the top node out of the bridge order, its build
/// being a construct-into guest's.
fn record_bridges(
    expr: &ResolvedExpr,
    site: SiteIndex,
    skip_root: bool,
    bound: &HashMap<String, SiteIndex>,
    bridge_order: &mut Vec<SiteIndex>,
) -> Option<SiteIndex> {
    let ResolvedExpr::Call(_, _, args) = expr else {
        // A variable's value comes from the build site it was bound to; a
        // literal comes from none.
        return match expr {
            ResolvedExpr::Var(_, v) => bound.get(&v.name).copied(),
            _ => None,
        };
    };
    let mut next = site.0 + 1;
    for arg in args {
        record_bridges(arg, SiteIndex(next), false, bound, bridge_order);
        next += site_count(arg);
    }
    // A primitive or a global lookup builds nothing itself, though a constructor
    // argument of it is still built.
    constructor_operand(expr)?;
    if !skip_root {
        bridge_order.push(site);
    }
    Some(site)
}

/// One firing of a rule head, and the proofs asked of it so far.
///
/// A firing states only a few of the propositions its sites have, so nothing is
/// built until [`Self::role`] asks for it.
pub(crate) struct Firing<'a> {
    rule_name: &'a str,
    plan: &'a HeadPlan,
    /// The head's as-written propositions, in `conclusion_sites` order.
    site_props: Vec<(SiteIndex, Proposition)>,
    /// The premises the rule body matched, one per body fact.
    body_premises: Vec<ProofId>,
    /// The view-row proof the head recorded at a bridge position, converted on
    /// demand. `None` for a position the requesting rule proof row does not carry.
    bridge_at: Box<dyn FnMut(&mut ProofStore, usize) -> Option<ProofId> + 'a>,
    substitution: IndexMap<String, TermId>,
    /// The proofs built so far, by the site reference each states.
    built: HashMap<(SiteIndex, SiteRole, bool), ProofId>,
    /// A build site -> its connector, `written = interned`.
    resolved: HashMap<SiteIndex, ProofId>,
}

impl<'a> Firing<'a> {
    pub(crate) fn new(
        rule_name: &'a str,
        plan: &'a HeadPlan,
        site_props: Vec<(SiteIndex, Proposition)>,
        body_premises: Vec<ProofId>,
        substitution: IndexMap<String, TermId>,
        bridge_at: Box<dyn FnMut(&mut ProofStore, usize) -> Option<ProofId> + 'a>,
    ) -> Self {
        Firing {
            rule_name,
            plan,
            site_props,
            body_premises,
            bridge_at,
            substitution,
            built: HashMap::default(),
            resolved: HashMap::default(),
        }
    }

    /// The proof the e-graph stored for `site`, stated the way `site` states it.
    pub(crate) fn role(&mut self, store: &mut ProofStore, site: SiteRef) -> ProofId {
        if let Some(&id) = self.built.get(&(site.index, site.role, site.reversed)) {
            return id;
        }
        match site.role {
            SiteRole::AsWritten => self.base(store, site.index, site.reversed),
            SiteRole::CanonicalReflexive | SiteRole::Connector => {
                self.resolve(store, site.index);
                self.recorded(site)
            }
            SiteRole::GuestView | SiteRole::GuestConnector => {
                let guest = self.plan.guest_at(site.index).unwrap_or_else(|| {
                    panic!(
                        "rule {}'s union at site {} builds no guest",
                        self.rule_name, site.index.0
                    )
                });
                self.resolve(store, guest);
                self.recorded(site)
            }
            SiteRole::UnionEdge => {
                let operands = self.plan.union_operands(site.index).unwrap_or_else(|| {
                    panic!(
                        "rule {}'s site {} is not a union the plan kept",
                        self.rule_name, site.index.0
                    )
                });
                self.union_edge(store, site.index, operands);
                self.recorded(site)
            }
            SiteRole::GlobalValue => {
                let value = self.plan.global_value(site.index);
                self.global_value(store, site.index, value);
                self.recorded(site)
            }
        }
    }

    /// A role the resolution above must have recorded.
    fn recorded(&self, site: SiteRef) -> ProofId {
        *self
            .built
            .get(&(site.index, site.role, site.reversed))
            .unwrap_or_else(|| {
                panic!(
                    "rule {}'s head builds no {:?} proof at site {}",
                    self.rule_name, site.role, site.index.0
                )
            })
    }

    /// The head's own conclusion at `site`, cached so every composite over it
    /// shares one node.
    fn base(&mut self, store: &mut ProofStore, site: SiteIndex, reversed: bool) -> ProofId {
        let key = (site, SiteRole::AsWritten, reversed);
        if let Some(&id) = self.built.get(&key) {
            return id;
        }
        let reference = SiteRef {
            index: site,
            reversed,
            role: SiteRole::AsWritten,
        };
        let proposition = self
            .site_props
            .iter()
            .find_map(|(index, prop)| (*index == site).then(|| reference.orient(prop)))
            .unwrap_or_else(|| panic!("rule {} has no conclusion site {}", self.rule_name, site.0));
        let id = store.push_shared_proof(
            SynthKey::Rule(
                self.rule_name.to_string(),
                reference,
                self.body_premises.clone(),
            ),
            Proof {
                proposition,
                justification: Justification::Rule {
                    name: self.rule_name.to_string(),
                    premise_proofs: self.body_premises.clone(),
                    substitution: self.substitution.clone(),
                    site: reference,
                },
            },
        );
        self.built.insert(key, id);
        id
    }

    /// Resolve a build site: fold one `Congr` per built child onto the site's own
    /// conclusion, then settle which e-class the interned term landed in.
    fn resolve(&mut self, store: &mut ProofStore, site: SiteIndex) -> ProofId {
        if let Some(&connector) = self.resolved.get(&site) {
            return connector;
        }
        let plan = self.plan;
        let expr = plan
            .expr_at(site)
            .filter(|expr| constructor_operand(expr).is_some())
            .unwrap_or_else(|| panic!("rule {}'s site {} builds no term", self.rule_name, site.0));
        let (_, args) = constructor_operand(expr).expect("filtered to a constructor application");
        let guest_of = plan.guest_of(site);

        let mut to_canonical = self.base(store, site, false);
        let mut next = site.0 + 1;
        for (i, arg) in args.iter().enumerate() {
            let child = plan.value_site(arg, SiteIndex(next));
            next += site_count(arg);
            let Some(child) = child else { continue };
            let child = self.resolve(store, child);
            to_canonical = congr(store, to_canonical, i, child);
        }

        let connector = match guest_of {
            Some((edge, target)) => {
                let view = self.guest_view(store, edge, target, to_canonical);
                let back = sym(store, view);
                let connector = trans(store, to_canonical, back);
                self.built.insert(
                    (edge.index, SiteRole::GuestConnector, edge.reversed),
                    connector,
                );
                connector
            }
            None => {
                let canonical = store.get(to_canonical).rhs();
                match self.bridge(store, site, canonical) {
                    Some(bridge) => {
                        let back = sym(store, bridge);
                        trans(store, to_canonical, back)
                    }
                    None => to_canonical,
                }
            }
        };

        let canonical_reflexive = reflexivize(store, to_canonical);
        self.built.insert(
            (site, SiteRole::CanonicalReflexive, false),
            canonical_reflexive,
        );
        self.built
            .insert((site, SiteRole::Connector, false), connector);
        self.resolved.insert(site, connector);
        connector
    }

    /// The view-row proof recorded for `site`, when it says the interned term
    /// landed in an e-class whose own term is spelled differently.
    ///
    /// `None` for a site with no bridge recorded: a row minted before the head
    /// reached the subterm it is about has nothing to name yet.
    fn bridge(
        &mut self,
        store: &mut ProofStore,
        site: SiteIndex,
        canonical: TermId,
    ) -> Option<ProofId> {
        let position = self.plan.bridge_position(site)?;
        let bridge = (self.bridge_at)(store, position)?;
        // Every proof this read can return — an existing row's, a rebuilt row's, a
        // construct-into guest view, or the encoder's `can_prf` fallback — ends at
        // the canonical term. A bridge that does not is one aligned to the wrong
        // site, which would otherwise compose into a proof of the wrong equality.
        assert_eq!(
            store.get(bridge).rhs(),
            canonical,
            "rule {}'s bridge for site {} does not end at the canonical term",
            self.rule_name,
            site.0
        );
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
        let to_dedup = trans(store, edge_proof, to_canonical);
        let view = match target {
            Some(target) => {
                let target = self.resolve(store, target);
                let back = sym(store, target);
                trans(store, back, to_dedup)
            }
            None => to_dedup,
        };
        self.built
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
        operands: [Option<SiteIndex>; 2],
    ) {
        let [lhs, rhs] = operands;
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
            self.built
                .insert((union, SiteRole::UnionEdge, reversed), edge);
        }
    }

    /// A global's stored value proof: the value equals itself, routed through the
    /// written form of the term it aliases.
    fn global_value(&mut self, store: &mut ProofStore, row: SiteIndex, value: Option<SiteIndex>) {
        let value = value.expect("a roled global proof needs a built value");
        let connector = self.resolve(store, value);
        let proof = reflexivize(store, connector);
        self.built
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
