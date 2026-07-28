//! The conclusion sites of a rule head.
//!
//! A rule head concludes one proposition per site. [`conclusion_sites`] is the
//! only place the sites are numbered: every consumer — the proof checker
//! replaying a head, the encoder tagging a proof with the site it concludes at —
//! must read the order from it rather than recompute it, so a proof that names a
//! [`SiteIndex`] means the same thing on both sides.

use std::borrow::Cow;

use crate::{
    ast::{GenericAction, ResolvedAction, ResolvedExpr, Span},
    core::ResolvedCall,
};

/// A conclusion site's position in its rule head's canonical site order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SiteIndex(pub usize);

/// The proposition a conclusion site stands for.
pub(crate) enum SiteConclusion<'a> {
    /// `t = t`, for the term the expression evaluates to. A `set`'s site owns
    /// the synthesized row call `(func args… value)`.
    Reflexive(Cow<'a, ResolvedExpr>),
    /// `lhs = rhs`, for the terms a `union`'s operands evaluate to. The reverse
    /// direction is `Sym` of this site, not a site of its own.
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

/// Enumerate the conclusion sites of a rule head, in canonical order: actions in
/// order, and within an action the pre-order of its expressions — the action's
/// own conclusion first, then its operands left to right. `panic` and `change`
/// conclude nothing and contribute no sites.
pub(crate) fn conclusion_sites<'a>(
    actions: impl IntoIterator<Item = &'a ResolvedAction>,
) -> Vec<ConclusionSite<'a>> {
    let mut sites = Vec::new();
    for (at, action) in actions.into_iter().enumerate() {
        match action {
            GenericAction::Let(_, _, expr) | GenericAction::Expr(_, expr) => {
                push_expr_sites(&mut sites, at, expr)
            }
            GenericAction::Union(span, lhs, rhs) => {
                push_site(
                    &mut sites,
                    at,
                    span.clone(),
                    SiteConclusion::Equality(lhs, rhs),
                );
                push_expr_sites(&mut sites, at, lhs);
                push_expr_sites(&mut sites, at, rhs);
            }
            GenericAction::Set(span, func, args, value) => {
                let row = set_row_expr(span.clone(), func, args, value);
                push_site(
                    &mut sites,
                    at,
                    span.clone(),
                    SiteConclusion::Reflexive(Cow::Owned(row)),
                );
                for arg in args {
                    push_expr_sites(&mut sites, at, arg);
                }
                push_expr_sites(&mut sites, at, value);
            }
            GenericAction::Panic(..) | GenericAction::Change(..) => {}
        }
    }
    sites
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
fn push_expr_sites<'a>(sites: &mut Vec<ConclusionSite<'a>>, at: usize, expr: &'a ResolvedExpr) {
    push_site(
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
}

fn push_site<'a>(
    sites: &mut Vec<ConclusionSite<'a>>,
    at: usize,
    span: Span,
    conclusion: SiteConclusion<'a>,
) {
    sites.push(ConclusionSite {
        index: SiteIndex(sites.len()),
        action: at,
        span,
        conclusion,
    });
}
