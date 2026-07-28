//! Is a rule's conclusion reconstructible from its premises, and does the site
//! the encoder stamped name it?
//!
//! For every [`Justification::Rule`](super::proof_format::Justification::Rule)
//! proof the checker accepts, replay the rule head and report which of its
//! [`conclusion_sites`] reproduce the conclusion the proof records, and whether
//! the [`SiteRef`] the proof carries is among them. The head is replayed twice:
//! once under the substitution the proof carries, and once under a substitution
//! rebuilt without consulting any premise proof that only carries a value
//! (`@Ast` payloads for body primitives and container side conditions), which is
//! what a term-free rule justification would have to do.
//!
//! Alongside that, [`record_head_bridge`] counts the canonicalization bridges a
//! rule head emits — the `Congr` steps moving a term it built onto its children's
//! canonical e-classes — and how many of them state an equality the head does not
//! conclude, which is what a site index cannot name.
//!
//! The check observes; it never changes what the checker accepts. It is off
//! unless `EGGLOG_PROOF_RECONSTRUCT_CHECK=1`, which also logs one
//! `PROOF-RECONSTRUCT` line per node and one `PROOF-HEAD-BRIDGE` line per bridge
//! at `info`, or unless a test enables it with [`begin`] and reads the counters
//! back with [`end`].

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::sync::OnceLock;

use crate::{
    TermId,
    ast::{FunctionSubtype, ResolvedExpr, ResolvedFact, ResolvedNCommand, ResolvedRule},
    core::ResolvedCall,
    proofs::{
        proof_checker::{eval_expr_with_subst, is_container_side_condition, process_actions},
        proof_format::{ProofId, ProofStore, Proposition},
        proof_sites::{SiteConclusion, SiteRef, conclusion_sites},
    },
    util::{HashMap, IndexMap, SymbolGen},
};

/// What the experiment observed, over the `Rule` nodes checked on this thread.
#[derive(Default, Clone, Debug)]
pub(crate) struct ReconstructStats {
    /// `Rule` proof nodes checked.
    pub nodes: usize,
    /// How many nodes had exactly *k* conclusion sites reproducing the recorded
    /// conclusion, keyed by *k*, replaying under the recorded substitution.
    pub sites_matching: BTreeMap<usize, usize>,
    /// Nodes where no site matched the conclusion but one matched it reversed.
    pub sym_only: usize,
    /// Nodes where no site matched in either direction.
    pub unmatched: usize,
    /// Nodes whose payload-free substitution agreed with the recorded one on
    /// every variable and selected the same sites.
    pub payload_free_agrees: usize,
    /// Nodes whose payload-free substitution could not be built, disagreed with
    /// the recorded one, or selected different sites.
    pub payload_free_fails: usize,
    /// Variables the payload-free substitution bound by recomputing a body
    /// primitive instead of reading a premise proof's term.
    pub recomputed_vars: usize,
    /// Nodes whose stamped site reproduces the conclusion and is the only site
    /// that does, in either direction.
    pub stamped_unique: usize,
    /// Nodes whose stamped site reproduces the conclusion, alongside others.
    pub stamped_among_several: usize,
    /// Nodes whose stamped site does not reproduce the conclusion the way it
    /// says. Deriving the conclusion from a site is only sound while this is 0.
    pub stamped_wrong: usize,
    /// Canonicalization bridges: `Congr` steps moving a constructor the head
    /// built onto its children's canonical e-classes.
    pub head_bridges: usize,
    /// Bridges whose child proof is not reflexive, so the step changes the term.
    /// Those steps state an equality the head does not conclude, so a site index
    /// cannot name them.
    pub head_bridges_load_bearing: usize,
}

thread_local! {
    /// `None` until the env var is consulted for this thread.
    static ENABLED: Cell<Option<bool>> = const { Cell::new(None) };
    static STATS: RefCell<ReconstructStats> = RefCell::new(ReconstructStats::default());
}

fn env_enabled() -> bool {
    static ENV: OnceLock<bool> = OnceLock::new();
    *ENV.get_or_init(|| std::env::var("EGGLOG_PROOF_RECONSTRUCT_CHECK").as_deref() == Ok("1"))
}

/// Whether the experiment runs on this thread.
pub(super) fn enabled() -> bool {
    ENABLED.with(|e| match e.get() {
        Some(on) => on,
        None => {
            let on = env_enabled();
            e.set(Some(on));
            on
        }
    })
}

/// Turn the experiment on for this thread and discard anything it recorded.
#[cfg(test)]
pub(crate) fn begin() {
    ENABLED.with(|e| e.set(Some(true)));
    STATS.with(|s| *s.borrow_mut() = ReconstructStats::default());
}

/// Turn the experiment off for this thread and take what it recorded.
#[cfg(test)]
pub(crate) fn end() -> ReconstructStats {
    ENABLED.with(|e| e.set(Some(false)));
    STATS.with(|s| std::mem::take(&mut *s.borrow_mut()))
}

/// Which conclusion sites of a rule head reproduce a claimed conclusion.
struct SiteMatch {
    sites: usize,
    /// Sites concluding the claim as written.
    exact: Vec<usize>,
    /// Sites concluding it reversed, i.e. reachable by one `Sym`.
    sym: Vec<usize>,
    /// Whether the site the proof was stamped with, read in the direction it
    /// names, concludes the claim.
    stamped_ok: bool,
}

impl SiteMatch {
    /// Sites reproducing the claim in either direction.
    fn matching(&self) -> usize {
        self.exact.len() + self.sym.len()
    }
}

/// Replay `rule`'s head under `subst` and report which sites conclude `claimed`,
/// `stamped` among them.
fn match_sites(
    store: &mut ProofStore,
    rule: &ResolvedRule,
    rule_name: &str,
    subst: HashMap<String, TermId>,
    claimed: &Proposition,
    stamped: SiteRef,
) -> Result<SiteMatch, String> {
    let actions: Vec<_> = rule.head.0.iter().collect();
    let ctx = process_actions(rule_name, subst, &actions, &mut store.term_dag)
        .map_err(|err| err.to_string())?;
    let mut result = SiteMatch {
        sites: ctx.site_propositions.len(),
        exact: Vec::new(),
        sym: Vec::new(),
        stamped_ok: false,
    };
    for (index, prop) in &ctx.site_propositions {
        if prop == claimed {
            result.exact.push(index.0);
        } else if prop.lhs == claimed.rhs && prop.rhs == claimed.lhs {
            result.sym.push(index.0);
        }
        if *index == stamped.index {
            result.stamped_ok = stamped.orient(prop) == *claimed;
        }
    }
    Ok(result)
}

/// A body fact the encoder never matches a row for: it mentions no function, so
/// everything it binds is recomputable from primitives. These are the facts
/// whose premise proofs exist only to carry a value.
fn is_computed_fact(fact: &ResolvedFact) -> bool {
    fn mentions_function(expr: &ResolvedExpr) -> bool {
        match expr {
            ResolvedExpr::Call(_, ResolvedCall::Primitive(_), args) => {
                args.iter().any(mentions_function)
            }
            ResolvedExpr::Call(..) => true,
            _ => false,
        }
    }
    match fact {
        ResolvedFact::Eq(_, lhs, rhs) => !mentions_function(lhs) && !mentions_function(rhs),
        ResolvedFact::Fact(expr) => !mentions_function(expr),
    }
}

/// The outcome of trying to satisfy one value-carrying fact by recomputation.
enum Step {
    /// Bound the fact's output variable.
    Bound,
    /// Both sides were already determined and agreed.
    Checked,
    /// An operand is not bound yet; retry after another fact binds it.
    Blocked,
    /// Both sides were determined and disagreed.
    Conflict,
}

/// Evaluate `expr`, or `None` if it is an unbound variable or evaluation fails.
fn eval_side(
    store: &mut ProofStore,
    rule_name: &str,
    expr: &ResolvedExpr,
    subst: &HashMap<String, TermId>,
) -> Option<TermId> {
    if let ResolvedExpr::Var(_, var) = expr {
        return subst.get(&var.name).copied();
    }
    eval_expr_with_subst(rule_name, expr, &mut store.term_dag, subst)
        .ok()
        .map(|(term, _)| term)
}

fn derive_fact(
    store: &mut ProofStore,
    rule_name: &str,
    fact: &ResolvedFact,
    subst: &mut HashMap<String, TermId>,
) -> Step {
    let (lhs, rhs) = match fact {
        ResolvedFact::Eq(_, lhs, rhs) => (lhs, rhs),
        ResolvedFact::Fact(expr) => {
            return match eval_side(store, rule_name, expr, subst) {
                Some(_) => Step::Checked,
                None => Step::Blocked,
            };
        }
    };
    let lhs_val = eval_side(store, rule_name, lhs, subst);
    let rhs_val = eval_side(store, rule_name, rhs, subst);
    match (lhs, lhs_val, rhs, rhs_val) {
        (ResolvedExpr::Var(_, var), None, _, Some(val))
        | (_, Some(val), ResolvedExpr::Var(_, var), None) => {
            subst.insert(var.name.clone(), val);
            Step::Bound
        }
        (_, Some(l), _, Some(r)) if l == r => Step::Checked,
        (_, Some(_), _, Some(_)) => Step::Conflict,
        _ => Step::Blocked,
    }
}

/// What a substitution rebuilt without value-carrying premises looks like.
struct PayloadFree {
    subst: HashMap<String, TermId>,
    /// Variables bound by recomputing a body primitive, with the value computed.
    recomputed: Vec<(String, TermId)>,
    /// Why the rebuild is incomplete, if it is.
    failure: Option<String>,
}

/// Rebuild the rule's substitution the way a term-free justification would have
/// to: unify only against premises that stand for a real row, then recompute
/// everything else from the rule body with the primitives' validators.
fn payload_free_substitution(
    store: &mut ProofStore,
    rule: &ResolvedRule,
    rule_name: &str,
    premise_proofs: &[ProofId],
    globals: &HashMap<String, TermId>,
) -> PayloadFree {
    let mut unified: IndexMap<String, TermId> = IndexMap::default();
    let mut pending = Vec::new();
    for (fact, &premise) in rule.body.iter().zip(premise_proofs) {
        if is_container_side_condition(fact) || is_computed_fact(fact) {
            pending.push(fact);
        } else {
            store.unify_fact(fact, premise, &mut unified);
        }
    }

    let mut subst = globals.clone();
    subst.extend(unified);
    let mut recomputed = Vec::new();
    let mut failure = None;

    // Facts can bind each other's operands, so keep sweeping until a sweep binds
    // nothing new. Each sweep binds at least one variable or is the last.
    for _ in 0..=pending.len() {
        let mut progress = false;
        pending.retain(
            |fact| match derive_fact(store, rule_name, fact, &mut subst) {
                Step::Bound => {
                    if let ResolvedFact::Eq(_, lhs, rhs) = fact {
                        for side in [lhs, rhs] {
                            if let ResolvedExpr::Var(_, var) = side
                                && let Some(&term) = subst.get(&var.name)
                                && !recomputed.iter().any(|(name, _)| *name == var.name)
                            {
                                recomputed.push((var.name.clone(), term));
                            }
                        }
                    }
                    progress = true;
                    false
                }
                Step::Checked => false,
                Step::Conflict => {
                    failure = Some(format!("recomputed fact disagrees: {fact}"));
                    false
                }
                Step::Blocked => true,
            },
        );
        if !progress {
            break;
        }
    }
    if failure.is_none()
        && let Some(fact) = pending.first()
    {
        failure = Some(format!("fact not recomputable: {fact}"));
    }

    PayloadFree {
        subst,
        recomputed,
        failure,
    }
}

/// Record one `Rule` proof node: which of the rule's conclusion sites reproduce
/// the conclusion the proof records, under the recorded substitution and under a
/// payload-free one, and whether `stamped` — the site the encoder tagged the
/// proof with — is one of them.
#[allow(clippy::too_many_arguments)]
pub(super) fn record(
    store: &mut ProofStore,
    rule: &ResolvedRule,
    rule_name: &str,
    premise_proofs: &[ProofId],
    globals: &HashMap<String, TermId>,
    recorded_subst: &HashMap<String, TermId>,
    claimed: &Proposition,
    stamped: SiteRef,
) {
    let recorded = match_sites(
        store,
        rule,
        rule_name,
        recorded_subst.clone(),
        claimed,
        stamped,
    );
    let payload_free = payload_free_substitution(store, rule, rule_name, premise_proofs, globals);
    let disagreeing: Vec<&String> = recorded_subst
        .iter()
        .filter(|(var, term)| payload_free.subst.get(*var) != Some(*term))
        .map(|(var, _)| var)
        .collect();
    let derived = match_sites(
        store,
        rule,
        rule_name,
        payload_free.subst.clone(),
        claimed,
        stamped,
    );

    let (sites, exact, sym) = match &recorded {
        Ok(m) => (m.sites, m.exact.len(), m.sym.len()),
        Err(_) => (0, 0, 0),
    };
    let payload_free_ok = payload_free.failure.is_none()
        && disagreeing.is_empty()
        && match (&recorded, &derived) {
            (Ok(a), Ok(b)) => a.exact == b.exact && a.sym == b.sym,
            _ => false,
        };

    STATS.with(|stats| {
        let mut stats = stats.borrow_mut();
        stats.nodes += 1;
        *stats.sites_matching.entry(exact).or_default() += 1;
        if exact == 0 {
            if sym > 0 {
                stats.sym_only += 1;
            } else {
                stats.unmatched += 1;
            }
        }
        match &recorded {
            Ok(m) if m.stamped_ok && m.matching() == 1 => stats.stamped_unique += 1,
            Ok(m) if m.stamped_ok => stats.stamped_among_several += 1,
            _ => stats.stamped_wrong += 1,
        }
        if payload_free_ok {
            stats.payload_free_agrees += 1;
        } else {
            stats.payload_free_fails += 1;
        }
        stats.recomputed_vars += payload_free.recomputed.len();
    });

    if !env_enabled() {
        return;
    }
    let status = |m: &Result<SiteMatch, String>| match m {
        Ok(m) => format!(
            "exact={} sym={} at={:?}{:?} stamped={}{} stamped_ok={}",
            m.exact.len(),
            m.sym.len(),
            m.exact,
            m.sym,
            stamped.index.0,
            if stamped.reversed { "-sym" } else { "" },
            m.stamped_ok,
        ),
        Err(err) => format!("exact=err sym=err at={}", one_line(err)),
    };
    let payload_free_status = match (&payload_free.failure, disagreeing.is_empty()) {
        (Some(_), _) => "unbuildable",
        (None, false) => "disagrees",
        (None, true) if payload_free_ok => "agrees",
        (None, true) => "different-sites",
    };
    log::info!(
        "PROOF-RECONSTRUCT {} payload_free={payload_free_status} sites={sites} \
         recomputed={} head={} rule={}",
        status(&recorded),
        show_recomputed(store, &payload_free.recomputed),
        one_line(
            &rule
                .head
                .0
                .iter()
                .map(|action| action.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        ),
        one_line(rule_name),
    );
    let stamped_ok = recorded.as_ref().is_ok_and(|m| m.stamped_ok);
    if exact != 1 || !payload_free_ok || !stamped_ok {
        log::info!(
            "PROOF-RECONSTRUCT-DETAIL claimed={} = {} | recorded-subst: {} | \
             payload-free-subst: {} | failure: {:?} | disagreeing: {:?} | derived-{} | \
             sites: {} | rule: {}",
            show_term(store, claimed.lhs),
            show_term(store, claimed.rhs),
            show_subst(store, recorded_subst),
            show_subst(store, &payload_free.subst),
            payload_free.failure,
            disagreeing,
            status(&derived),
            show_sites(store, rule, rule_name, recorded_subst.clone()),
            one_line(&rule.to_string()),
        );
    }
}

/// Record one canonicalization bridge, if `site` of `rule_name` names a
/// constructor the head builds — a `Congr` step over any other kind of site
/// belongs to rebuilding, not to the head.
pub(super) fn record_head_bridge(
    prog: &[ResolvedNCommand],
    rule_name: &str,
    site: SiteRef,
    child_is_reflexive: bool,
) {
    let Some(rule) = prog.iter().find_map(|cmd| match cmd {
        ResolvedNCommand::NormRule { rule } if rule.name == rule_name => Some(rule),
        _ => None,
    }) else {
        return;
    };
    let sites = conclusion_sites(rule.head.0.iter());
    let builds_constructor = matches!(
        sites.get(site.index.0).map(|s| &s.conclusion),
        Some(SiteConclusion::Reflexive(expr))
            if matches!(
                expr.as_ref(),
                ResolvedExpr::Call(_, ResolvedCall::Func(func), _)
                    if func.subtype == FunctionSubtype::Constructor
            )
    );
    if !builds_constructor {
        return;
    }
    STATS.with(|stats| {
        let mut stats = stats.borrow_mut();
        stats.head_bridges += 1;
        if !child_is_reflexive {
            stats.head_bridges_load_bearing += 1;
        }
    });
    if env_enabled() {
        log::info!(
            "PROOF-HEAD-BRIDGE site={} load_bearing={} rule={}",
            site.index.0,
            !child_is_reflexive,
            one_line(rule_name),
        );
    }
}

/// What every conclusion site of the head concludes under `subst`.
fn show_sites(
    store: &mut ProofStore,
    rule: &ResolvedRule,
    rule_name: &str,
    subst: HashMap<String, TermId>,
) -> String {
    let actions: Vec<_> = rule.head.0.iter().collect();
    let Ok(ctx) = process_actions(rule_name, subst, &actions, &mut store.term_dag) else {
        return "<head did not replay>".to_string();
    };
    let sites = conclusion_sites(rule.head.0.iter());
    ctx.site_propositions
        .iter()
        .zip(&sites)
        .map(|((index, prop), site)| {
            format!(
                "{}@{}: {} = {}",
                index.0,
                site.location(),
                show_term(store, prop.lhs),
                show_term(store, prop.rhs)
            )
        })
        .collect::<Vec<_>>()
        .join("; ")
}

/// Render a term for a log line: shared with `let` (a proof term is a DAG, and
/// expanding it would blow up) and clipped, since only the shape matters here.
fn show_term(store: &ProofStore, term: TermId) -> String {
    let text = one_line(
        &store
            .term_dag
            .to_string_with_let(&mut SymbolGen::new(String::new()), term),
    );
    text.chars().take(200).collect()
}

/// Collapse runs of whitespace so a rule renders on one log line.
fn one_line(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The values the payload-free rebuild computed, so a log line shows that a
/// value the proof carried was re-derived rather than read.
fn show_recomputed(store: &ProofStore, recomputed: &[(String, TermId)]) -> String {
    let entries: Vec<String> = recomputed
        .iter()
        .map(|(var, term)| format!("{var}={}", show_term(store, *term)))
        .collect();
    format!("[{}]", entries.join(" "))
}

fn show_subst(store: &ProofStore, subst: &HashMap<String, TermId>) -> String {
    let mut entries: Vec<String> = subst
        .iter()
        .map(|(var, term)| format!("{var} -> {}", show_term(store, *term)))
        .collect();
    entries.sort();
    entries.join(", ")
}
