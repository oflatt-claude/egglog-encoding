//! The conclusion sites of a rule head, and the columns their proofs are named
//! by.
//!
//! A rule head concludes one proposition per site. [`conclusion_sites`] is the
//! only place the sites are numbered: every consumer — the proof checker
//! replaying a head, the encoder tagging a proof with the site it concludes at —
//! must read the order from it rather than recompute it, so a proof that names a
//! column means the same thing on both sides. [`action_sites`] is the same
//! numbering arranged by action, for a consumer that walks the head's syntax
//! instead of the flat site list.

use std::borrow::Cow;

use crate::{
    ast::{GenericAction, ResolvedAction, ResolvedExpr, Span},
    core::ResolvedCall,
};

/// How many columns a conclusion site owns. Each is one proof of the head's
/// lowering, named by [`site_column`].
pub(crate) const PROOFS_PER_SITE: usize = 4;

/// Which proof of a conclusion site a rule proof's column names.
///
/// A site's first two columns are the head's own conclusion there, in each
/// direction. The other two are proofs the head's lowering composes over it,
/// which only a site that builds something has; which composites they are is
/// decided by what the head does at that site, so the aliases below overlap (see
/// [`crate::proofs::proof_head`]).
pub(crate) mod column {
    /// The head's own conclusion, over the terms it wrote.
    pub(crate) const OWN: usize = 0;
    /// The same conclusion with its two sides swapped.
    pub(crate) const OWN_REVERSED: usize = 1;
    /// The first column a site's lowering composes into.
    pub(crate) const FIRST_COMPOSED: usize = 2;
    /// `t = t` for a build site's term with every built child replaced by the
    /// e-class its view interned it into.
    pub(crate) const CANONICAL_REFLEXIVE: usize = 2;
    /// `written = interned` for a build site.
    pub(crate) const CONNECTOR: usize = 3;
    /// A construct-into guest's view-row proof: the target's e-class equals the
    /// guest's term over its children's representatives.
    pub(crate) const GUEST_VIEW: usize = 2;
    /// A construct-into guest's connector: the guest as written equals the
    /// target's e-class.
    pub(crate) const GUEST_CONNECTOR: usize = 3;
    /// A kept `union`'s union-find edge, `larger = smaller`, routed through the
    /// operands' written forms.
    pub(crate) const UNION_EDGE: usize = 2;
    /// The same edge with its two sides swapped.
    pub(crate) const UNION_EDGE_REVERSED: usize = 3;
    /// A global's stored value proof: `value = value`, routed through the written
    /// form of the term it aliases.
    pub(crate) const GLOBAL_VALUE: usize = 2;
}

/// The integer a rule proof's site column stores: which proof of `site`'s block
/// the row is, so the whole column is one value the encoder can compute with a
/// single primitive call.
pub(crate) fn site_column(site: usize, offset: usize) -> i64 {
    debug_assert!(offset < PROOFS_PER_SITE, "column offset out of range");
    (site * PROOFS_PER_SITE + offset) as i64
}

/// Read back [`site_column`] as `(site, offset)`. Panics on a value that names no
/// site.
pub(crate) fn decode(raw: i64) -> (usize, usize) {
    assert!(
        raw >= 0,
        "rule proof was emitted without a conclusion site (site column {raw})"
    );
    let raw = raw as usize;
    (raw / PROOFS_PER_SITE, raw % PROOFS_PER_SITE)
}

/// The proposition a conclusion site stands for.
pub(crate) enum SiteConclusion<'a> {
    /// `t = t`, for the term the expression evaluates to. A `set`'s site owns
    /// the synthesized row call `(func args… value)`.
    Reflexive(Cow<'a, ResolvedExpr>),
    /// `lhs = rhs`, for the terms a `union`'s operands evaluate to. The reverse
    /// direction is [`column::OWN_REVERSED`] of this site, not a site of its own.
    Equality(&'a ResolvedExpr, &'a ResolvedExpr),
}

/// One position in a rule head that the head concludes a proposition at. A
/// site is identified by its position in [`conclusion_sites`]' output.
pub(crate) struct ConclusionSite<'a> {
    /// Position of this site's action in the head.
    pub action: usize,
    pub conclusion: SiteConclusion<'a>,
}

/// Where one action's sites start. An expression's sites are the pre-order run
/// beginning at the operand's own site, so a walk that visits the expression's
/// nodes in the same order recovers every index by counting.
#[derive(Debug, Clone, Default)]
pub(crate) struct ActionSites {
    /// The action's own conclusion: a `union`'s equality or a `set`'s row.
    /// `let`, `expr`, `panic` and `change` have none.
    pub own: Option<usize>,
    /// The site of each expression the action evaluates, in the order
    /// [`conclusion_sites`] visits them: a `union`'s two operands, a `set`'s
    /// arguments then its value, a `let`'s or `expr`'s single expression.
    /// Empty for `panic` and `change`.
    pub operands: Vec<usize>,
}

/// Enumerate the conclusion sites of a rule head, in canonical order: actions in
/// order, and within an action the pre-order of its expressions — the action's
/// own conclusion first, then its operands left to right. `panic` and `change`
/// conclude nothing and contribute no sites.
pub(crate) fn conclusion_sites<'a>(
    actions: impl IntoIterator<Item = &'a ResolvedAction>,
) -> Vec<ConclusionSite<'a>> {
    walk(actions).0
}

/// [`conclusion_sites`]' numbering, one [`ActionSites`] per action.
pub(crate) fn action_sites<'a>(
    actions: impl IntoIterator<Item = &'a ResolvedAction>,
) -> Vec<ActionSites> {
    walk(actions).1
}

fn walk<'a>(
    actions: impl IntoIterator<Item = &'a ResolvedAction>,
) -> (Vec<ConclusionSite<'a>>, Vec<ActionSites>) {
    let mut sites = Vec::new();
    let mut per_action = Vec::new();
    for (at, action) in actions.into_iter().enumerate() {
        let entry = match action {
            GenericAction::Let(_, _, expr) | GenericAction::Expr(_, expr) => ActionSites {
                own: None,
                operands: vec![push_expr_sites(&mut sites, at, expr)],
            },
            GenericAction::Union(_, lhs, rhs) => {
                let own = push_site(&mut sites, at, SiteConclusion::Equality(lhs, rhs));
                let lhs_sites = push_expr_sites(&mut sites, at, lhs);
                let rhs_sites = push_expr_sites(&mut sites, at, rhs);
                ActionSites {
                    own: Some(own),
                    operands: vec![lhs_sites, rhs_sites],
                }
            }
            GenericAction::Set(span, func, args, value) => {
                let row = set_row_expr(span.clone(), func, args, value);
                let own = push_site(&mut sites, at, SiteConclusion::Reflexive(Cow::Owned(row)));
                let mut operands = Vec::with_capacity(args.len() + 1);
                for arg in args {
                    operands.push(push_expr_sites(&mut sites, at, arg));
                }
                operands.push(push_expr_sites(&mut sites, at, value));
                ActionSites {
                    own: Some(own),
                    operands,
                }
            }
            GenericAction::Panic(..) | GenericAction::Change(..) => ActionSites::default(),
        };
        per_action.push(entry);
    }
    (sites, per_action)
}

/// The row a `set` writes, as a call the head can evaluate: a custom function
/// stores its output as the last argument.
fn set_row_expr(
    span: Span,
    func: &ResolvedCall,
    args: &[ResolvedExpr],
    value: &ResolvedExpr,
) -> ResolvedExpr {
    let mut row = args.to_vec();
    row.push(value.clone());
    ResolvedExpr::Call(span, func.clone(), row)
}

/// Push a site for `expr` and, in pre-order, one for each of its
/// subexpressions. Returns `expr`'s own site.
fn push_expr_sites<'a>(
    sites: &mut Vec<ConclusionSite<'a>>,
    at: usize,
    expr: &'a ResolvedExpr,
) -> usize {
    let index = push_site(sites, at, SiteConclusion::Reflexive(Cow::Borrowed(expr)));
    if let ResolvedExpr::Call(_, _, args) = expr {
        for arg in args {
            push_expr_sites(sites, at, arg);
        }
    }
    index
}

fn push_site<'a>(
    sites: &mut Vec<ConclusionSite<'a>>,
    at: usize,
    conclusion: SiteConclusion<'a>,
) -> usize {
    let index = sites.len();
    sites.push(ConclusionSite {
        action: at,
        conclusion,
    });
    index
}
