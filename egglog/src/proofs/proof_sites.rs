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

/// A conclusion site together with which way round a proof states it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SiteRef {
    pub index: SiteIndex,
    /// The proof concludes `rhs = lhs` for a site whose equality is `lhs = rhs`.
    pub reversed: bool,
}

impl SiteRef {
    /// The site as written.
    pub(crate) fn forward(index: SiteIndex) -> Self {
        Self {
            index,
            reversed: false,
        }
    }

    /// The site with its two sides swapped.
    pub(crate) fn reversed(index: SiteIndex) -> Self {
        Self {
            index,
            reversed: true,
        }
    }

    /// The integer a rule proof's site column stores. Index and direction share
    /// one column because a `union`'s direction is only known once the ids being
    /// unioned are compared, so the encoder must be able to compute the whole
    /// column value with one primitive call.
    pub(crate) fn encode(self) -> i64 {
        self.index.0 as i64 * 2 + self.reversed as i64
    }

    /// Read back [`Self::encode`]. Panics on a value that names no site.
    pub(crate) fn decode(raw: i64) -> Self {
        assert!(
            raw >= 0,
            "rule proof was emitted without a conclusion site (site column {raw})"
        );
        Self {
            index: SiteIndex(raw as usize / 2),
            reversed: raw % 2 == 1,
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

/// The sites of an expression's nodes, mirroring the expression's shape.
#[derive(Debug, Clone)]
pub(crate) struct ExprSites {
    /// The site for the expression itself.
    pub index: SiteIndex,
    /// One entry per operand, in order. Empty for a variable or a literal.
    pub operands: Vec<ExprSites>,
}

/// The sites one action contributes, in the action's own shape.
#[derive(Debug, Clone, Default)]
pub(crate) struct ActionSites {
    /// The action's own conclusion: a `union`'s equality or a `set`'s row.
    /// `let`, `expr`, `panic` and `change` have none.
    pub own: Option<SiteIndex>,
    /// One entry per expression the action evaluates, in the order
    /// [`conclusion_sites`] visits them: a `union`'s two operands, a `set`'s
    /// arguments then its value, a `let`'s or `expr`'s single expression.
    /// Empty for `panic` and `change`.
    pub operands: Vec<ExprSites>,
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

/// Push a site for `expr` and, in pre-order, one for each of its subexpressions.
fn push_expr_sites<'a>(
    sites: &mut Vec<ConclusionSite<'a>>,
    at: usize,
    expr: &'a ResolvedExpr,
) -> ExprSites {
    let index = push_site(
        sites,
        at,
        expr.span(),
        SiteConclusion::Reflexive(Cow::Borrowed(expr)),
    );
    let mut operands = Vec::new();
    if let ResolvedExpr::Call(_, _, args) = expr {
        for arg in args {
            operands.push(push_expr_sites(sites, at, arg));
        }
    }
    ExprSites { index, operands }
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
