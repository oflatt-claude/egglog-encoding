//! The conclusion sites of a rule head.
//!
//! A rule head concludes one proposition per site. [`conclusion_sites`] is the
//! only place the sites are numbered: every consumer — the proof checker
//! replaying a head, the encoder tagging a proof with the site it concludes at —
//! must read the order from it rather than recompute it, so a proof that names a
//! [`SiteIndex`] means the same thing on both sides. [`action_sites`] is the same
//! numbering arranged by action, for a consumer that walks the head's syntax
//! instead of the flat site list.

use std::borrow::Cow;

use crate::{
    ast::{GenericAction, ResolvedAction, ResolvedExpr, Span},
    core::ResolvedCall,
    proofs::proof_format::Proposition,
};

/// A conclusion site's position in its rule head's canonical site order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SiteIndex(pub usize);

/// Which proposition *about* a conclusion site a rule proof states.
///
/// Only [`SiteRole::AsWritten`] is a conclusion of the head. A head that builds
/// a term also needs the same term over its children's representatives and the
/// edges between the two, which are composed from the site's own equality;
/// proof conversion synthesizes that composition from the role, the site, and
/// the rule proof's trailing bridge premises (see
/// [`crate::proofs::proof_head_skeleton`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SiteRole {
    /// The site's own equality, over the terms the head wrote.
    AsWritten,
    /// `t = t` for a build site's term with every built child replaced by the
    /// e-class its view interned it into.
    CanonicalReflexive,
    /// `written = interned` for a build site.
    Connector,
    /// A construct-into guest's view-row proof: the target's e-class equals the
    /// guest's term over its children's representatives.
    GuestView,
    /// A construct-into guest's connector: the guest as written equals the
    /// target's e-class.
    GuestConnector,
    /// A `union`'s union-find edge, `larger = smaller`, routed through the
    /// operands' written forms.
    UnionEdge,
    /// A global's stored value proof: `value = value`, routed through the
    /// written form of the term it aliases.
    GlobalValue,
}

impl SiteRole {
    /// Every role, in the order [`Self::code`] numbers them.
    const ALL: [SiteRole; 7] = [
        SiteRole::AsWritten,
        SiteRole::CanonicalReflexive,
        SiteRole::Connector,
        SiteRole::GuestView,
        SiteRole::GuestConnector,
        SiteRole::UnionEdge,
        SiteRole::GlobalValue,
    ];

    fn code(self) -> usize {
        Self::ALL.iter().position(|r| *r == self).unwrap()
    }
}

/// A conclusion site, which way round a proof states it, and which of the
/// site's propositions the proof states.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SiteRef {
    pub index: SiteIndex,
    /// The proof concludes `rhs = lhs` for a site whose equality is `lhs = rhs`.
    pub reversed: bool,
    pub role: SiteRole,
}

impl SiteRef {
    /// The site as written.
    pub(crate) fn forward(index: SiteIndex) -> Self {
        Self {
            index,
            reversed: false,
            role: SiteRole::AsWritten,
        }
    }

    /// The site with its two sides swapped.
    pub(crate) fn reversed(index: SiteIndex) -> Self {
        Self {
            index,
            reversed: true,
            role: SiteRole::AsWritten,
        }
    }

    /// The same reference stating `role` instead.
    pub(crate) fn with_role(self, role: SiteRole) -> Self {
        Self { role, ..self }
    }

    /// The integer a rule proof's site column stores. Index, direction and role
    /// share one column because a `union`'s direction is only known once the ids
    /// being unioned are compared, so the encoder must be able to compute the
    /// whole column value with one primitive call.
    pub(crate) fn encode(self) -> i64 {
        let oriented = self.index.0 * 2 + self.reversed as usize;
        (oriented * SiteRole::ALL.len() + self.role.code()) as i64
    }

    /// Read back [`Self::encode`]. Panics on a value that names no site.
    pub(crate) fn decode(raw: i64) -> Self {
        assert!(
            raw >= 0,
            "rule proof was emitted without a conclusion site (site column {raw})"
        );
        let raw = raw as usize;
        let oriented = raw / SiteRole::ALL.len();
        Self {
            index: SiteIndex(oriented / 2),
            reversed: oriented % 2 == 1,
            role: SiteRole::ALL[raw % SiteRole::ALL.len()],
        }
    }

    /// `prop` stated the way this reference states it.
    pub(crate) fn orient(self, prop: &Proposition) -> Proposition {
        if self.reversed {
            Proposition::new(prop.rhs, prop.lhs)
        } else {
            prop.clone()
        }
    }
}

/// The proposition a conclusion site stands for.
pub(crate) enum SiteConclusion<'a> {
    /// `t = t`, for the term the expression evaluates to. A `set`'s site owns
    /// the synthesized row call `(func args… value)`.
    Reflexive(Cow<'a, ResolvedExpr>),
    /// `lhs = rhs`, for the terms a `union`'s operands evaluate to. The reverse
    /// direction is [`SiteRef::reversed`] of this site, not a site of its own.
    Equality(&'a ResolvedExpr, &'a ResolvedExpr),
}

/// One position in a rule head that the head concludes a proposition at.
pub(crate) struct ConclusionSite<'a> {
    /// Position in the head's canonical site order.
    pub index: SiteIndex,
    /// Position of this site's action in the head.
    pub action: usize,
    /// Where the site is in the source, for diagnostics.
    pub span: Span,
    pub conclusion: SiteConclusion<'a>,
}

impl ConclusionSite<'_> {
    /// The site's source location, or `<generated>` when it has no source text.
    pub fn location(&self) -> String {
        match &self.span {
            Span::Panic => "<generated>".to_string(),
            span => span.to_string(),
        }
    }
}

/// Where one action's sites start. An expression's sites are the pre-order run
/// beginning at the operand's own site, so a walk that visits the expression's
/// nodes in the same order recovers every index by counting.
#[derive(Debug, Clone, Default)]
pub(crate) struct ActionSites {
    /// The action's own conclusion: a `union`'s equality or a `set`'s row.
    /// `let`, `expr`, `panic` and `change` have none.
    pub own: Option<SiteIndex>,
    /// The site of each expression the action evaluates, in the order
    /// [`conclusion_sites`] visits them: a `union`'s two operands, a `set`'s
    /// arguments then its value, a `let`'s or `expr`'s single expression.
    /// Empty for `panic` and `change`.
    pub operands: Vec<SiteIndex>,
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
            GenericAction::Union(span, lhs, rhs) => {
                let own = push_site(
                    &mut sites,
                    at,
                    span.clone(),
                    SiteConclusion::Equality(lhs, rhs),
                );
                let lhs_sites = push_expr_sites(&mut sites, at, lhs);
                let rhs_sites = push_expr_sites(&mut sites, at, rhs);
                ActionSites {
                    own: Some(own),
                    operands: vec![lhs_sites, rhs_sites],
                }
            }
            GenericAction::Set(span, func, args, value) => {
                let row = set_row_expr(span.clone(), func, args, value);
                let own = push_site(
                    &mut sites,
                    at,
                    span.clone(),
                    SiteConclusion::Reflexive(Cow::Owned(row)),
                );
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
) -> SiteIndex {
    let index = push_site(
        sites,
        at,
        expr.span(),
        SiteConclusion::Reflexive(Cow::Borrowed(expr)),
    );
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
    span: Span,
    conclusion: SiteConclusion<'a>,
) -> SiteIndex {
    let index = SiteIndex(sites.len());
    sites.push(ConclusionSite {
        index,
        action: at,
        span,
        conclusion,
    });
    index
}
