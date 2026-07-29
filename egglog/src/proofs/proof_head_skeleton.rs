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

/// A rule head as the encoder lowers it, and the build sites that lowering
/// composes its proofs from.
pub(crate) struct HeadPlan {
    /// The head with every constructor-application `union` operand lifted into a
    /// preceding `let`, each action carrying the [`ActionSites`] of the action it
    /// came from.
    pub actions: Vec<(ResolvedAction, ActionSites)>,
    /// Guest variable -> where its constructor is built instead.
    pub construct_into: HashMap<String, ConstructInto>,
    /// Indices into [`Self::actions`] of the `union`s the plan makes redundant.
    pub dropped: HashSet<usize>,
    /// Per conclusion site whose lowering composes anything, what it composes
    /// from. See [`build_sites`] for the numbering.
    builds: HashMap<SiteIndex, Build>,
    /// The build sites that record a bridge premise, in construction order.
    bridge_order: Vec<SiteIndex>,
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
            builds: HashMap::default(),
            bridge_order: Vec::new(),
        };
        build_sites(&mut plan);
        plan
    }

    /// Where `site`'s bridge premise sits in a rule proof's bridge list, counted
    /// from the list's end (the list is consed onto as the head builds, so the
    /// oldest bridge is last). `None` for a site that records no bridge.
    pub(crate) fn bridge_position(&self, site: SiteIndex) -> Option<usize> {
        self.bridge_order.iter().position(|s| *s == site)
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

/// What one conclusion site's composite proofs are composed from. Only a site
/// whose lowering composes something has one.
#[derive(Clone)]
enum Build {
    /// A constructor application the head builds.
    Term {
        /// Per child, in order: the build site its value comes from, or `None`
        /// when the child is a leaf the head did not build.
        children: Vec<Option<SiteIndex>>,
        /// Set when the site is a construct-into guest: the dropped `union`'s
        /// site, oriented `target = guest`, and the target's build site if the
        /// head built it too.
        guest_of: Option<(SiteRef, Option<SiteIndex>)>,
    },
    /// A `union` the plan keeps: its two operands' build sites.
    Union([Option<SiteIndex>; 2]),
    /// A `union` the plan dropped: the guest built into its other operand.
    Guest(SiteIndex),
    /// A global `set`: the build site of the value it aliases.
    Global(Option<SiteIndex>),
}

/// Index `plan`'s build sites: actions in order, and within an action the
/// post-order of its constructor applications (children before the node), which
/// is the order the encoder builds them and therefore the order a rule proof's
/// trailing bridge premises are recorded in.
///
/// A construct-into guest records no bridge: its representative is the target's
/// e-class, which the dropped `union`'s site already names, so the encoder reads
/// no view-row proof for it.
fn build_sites(plan: &mut HeadPlan) {
    let mut builds: HashMap<SiteIndex, Build> = HashMap::default();
    let mut bridge_order: Vec<SiteIndex> = Vec::new();
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
        let values: Vec<Option<SiteIndex>> = action_operands(action)
            .zip(&sites.operands)
            .map(|(expr, site)| {
                let mut next = site.0;
                walk_build_sites(
                    expr,
                    &mut next,
                    guest.is_some(),
                    &bound,
                    &mut builds,
                    &mut bridge_order,
                )
            })
            .collect();
        match action {
            ResolvedAction::Let(_, v, _) => {
                if let Some(site) = values[0] {
                    if let Some(into) = guest {
                        let target = bound.get(&into.target).copied();
                        let Some(Build::Term { guest_of, .. }) = builds.get_mut(&site) else {
                            panic!("a construct-into guest is a build site");
                        };
                        *guest_of = Some((into.edge, target));
                        builds.insert(into.edge.index, Build::Guest(site));
                    }
                    bound.insert(v.name.clone(), site);
                }
            }
            ResolvedAction::Union(..) => {
                let own = sites
                    .own
                    .expect("a union contributes a site for its equality");
                builds.insert(own, Build::Union([values[0], values[1]]));
            }
            ResolvedAction::Set(_, _, args, _) if args.is_empty() => {
                let own = sites.own.expect("a set contributes a site for its row");
                builds.insert(own, Build::Global(values[0]));
            }
            _ => {}
        }
    }
    plan.builds = builds;
    plan.bridge_order = bridge_order;
}

/// Record the build sites of `expr`'s constructor applications, post-order, and
/// return the build site `expr`'s value comes from. `next` is the pre-order site
/// cursor, positioned at `expr`'s own site. `skip_root` leaves the top node out
/// of the bridge order, its build being the caller's (a construct-into guest).
fn walk_build_sites(
    expr: &ResolvedExpr,
    next: &mut usize,
    skip_root: bool,
    bound: &HashMap<String, SiteIndex>,
    builds: &mut HashMap<SiteIndex, Build>,
    bridge_order: &mut Vec<SiteIndex>,
) -> Option<SiteIndex> {
    let index = SiteIndex(*next);
    *next += 1;
    let ResolvedExpr::Call(_, _, args) = expr else {
        // A variable's value comes from the build site it was bound to; a
        // literal comes from none.
        return match expr {
            ResolvedExpr::Var(_, v) => bound.get(&v.name).copied(),
            _ => None,
        };
    };
    let children: Vec<Option<SiteIndex>> = args
        .iter()
        .map(|arg| walk_build_sites(arg, next, false, bound, builds, bridge_order))
        .collect();
    // A primitive or a global lookup builds nothing itself, though a constructor
    // argument of it is still built.
    constructor_operand(expr)?;
    builds.insert(
        index,
        Build::Term {
            children,
            guest_of: None,
        },
    );
    if !skip_root {
        bridge_order.push(index);
    }
    Some(index)
}

/// The build sites a proof about `site` is composed from — the ones whose
/// bridge premises conversion has to read. A proof stating only the head's own
/// conclusion needs none.
pub(crate) fn sites_needed(plan: &HeadPlan, site: SiteRef) -> Vec<SiteIndex> {
    let mut out = vec![];
    let mut from = |start: Option<SiteIndex>| {
        if let Some(start) = start {
            closure(plan, start, &mut out);
        }
    };
    match (site.role, plan.builds.get(&site.index)) {
        (SiteRole::AsWritten, _) => {}
        (SiteRole::CanonicalReflexive | SiteRole::Connector, _) => from(Some(site.index)),
        (SiteRole::GuestView | SiteRole::GuestConnector, Some(Build::Guest(guest))) => {
            from(Some(*guest))
        }
        (SiteRole::UnionEdge, Some(Build::Union(operands))) => {
            let operands = *operands;
            operands.into_iter().for_each(from);
        }
        (SiteRole::GlobalValue, Some(Build::Global(value))) => from(*value),
        _ => {}
    }
    out
}

fn closure(plan: &HeadPlan, site: SiteIndex, out: &mut Vec<SiteIndex>) {
    if out.contains(&site) {
        return;
    }
    out.push(site);
    let Some(Build::Term { children, guest_of }) = plan.builds.get(&site) else {
        return;
    };
    for child in children.iter().flatten() {
        closure(plan, *child, out);
    }
    if let Some((_, Some(target))) = *guest_of {
        closure(plan, target, out);
    }
}

/// One firing of a rule head, and the proofs asking about its sites has built so
/// far.
///
/// A firing writes a few of the propositions its sites have, so nothing is built
/// until [`Self::role`] asks for it: materializing the rest would cost a proof
/// node — with a copy of the substitution — per site per firing.
pub(crate) struct Firing<'a> {
    pub rule_name: &'a str,
    pub plan: &'a HeadPlan,
    /// The head's as-written propositions, in `conclusion_sites` order.
    pub site_props: Vec<(SiteIndex, Proposition)>,
    /// The premises the rule body matched, one per body fact.
    pub body_premises: Vec<ProofId>,
    /// The view-row proof of each interned subterm the composition needs, by
    /// build site.
    pub bridges: HashMap<SiteIndex, ProofId>,
    pub substitution: IndexMap<String, TermId>,
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
        bridges: HashMap<SiteIndex, ProofId>,
        substitution: IndexMap<String, TermId>,
    ) -> Self {
        Firing {
            rule_name,
            plan,
            site_props,
            body_premises,
            bridges,
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
                let Some(Build::Guest(guest)) = self.plan.builds.get(&site.index) else {
                    panic!(
                        "rule {}'s union at site {} builds no guest",
                        self.rule_name, site.index.0
                    );
                };
                let guest = *guest;
                self.resolve(store, guest);
                self.recorded(site)
            }
            SiteRole::UnionEdge => {
                let Some(Build::Union(operands)) = self.plan.builds.get(&site.index) else {
                    panic!(
                        "rule {}'s site {} is not a union the plan kept",
                        self.rule_name, site.index.0
                    );
                };
                let operands = *operands;
                self.union_edge(store, site.index, operands);
                self.recorded(site)
            }
            SiteRole::GlobalValue => {
                let Some(Build::Global(value)) = self.plan.builds.get(&site.index) else {
                    panic!(
                        "rule {}'s site {} is not a global's row",
                        self.rule_name, site.index.0
                    );
                };
                let value = *value;
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
        let Some(Build::Term { children, guest_of }) = self.plan.builds.get(&site) else {
            panic!("rule {}'s site {} builds no term", self.rule_name, site.0);
        };
        let (children, guest_of) = (children.clone(), *guest_of);

        let mut to_canonical = self.base(store, site, false);
        for (i, child) in children.iter().enumerate() {
            let Some(child) = *child else { continue };
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
        let bridge = *self.bridges.get(&site)?;
        (store.get(bridge).rhs() == canonical).then_some(bridge)
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
