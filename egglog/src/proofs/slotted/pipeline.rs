//! Runs the slotted proof pipeline inside an e-graph: records the source
//! metadata the compiler publishes as the program runs, and on each `prove`
//! translates the egglog proof to a slotted proof and checks it.

use super::checker::check_claim;
use super::source::{ColumnKind, SlottedProgram, SourceError};
use super::translate::translate;
use crate::ast::{Expr, Fact, Literal};
use crate::proofs::proof_format::{ProofId, ProofStore};
use crate::util::HashMap;
use crate::{GenericExpr, TermDag};
use std::collections::BTreeSet;

/// One source-level fact the compiler recorded, in program order.
#[derive(Clone, Debug)]
enum Source {
    Let(String, String),
    Union(String, String),
    Rule(String, String),
    Claim(i64, String, String, String),
}

/// The physical layout the compiler publishes for a constructor, before it is
/// read into surface columns.
#[derive(Clone, Debug, Default)]
struct RawLayout {
    arity: Option<usize>,
    edges: BTreeSet<usize>,
    binders: BTreeSet<usize>,
    payloads: BTreeSet<usize>,
}

/// What the encoding calls each carrier's pieces.
#[derive(Clone, Debug, Default)]
pub struct Carriers {
    /// Surface sort name -> carrier index.
    pub index: HashMap<String, i64>,
}

impl Carriers {
    /// The variable constructor of a carrier: `(SlottedVar_N 0)` is slot `$0`.
    pub fn var_constructor(index: i64) -> String {
        format!("SlottedVar_{index}")
    }

    pub fn is_var_constructor(&self, head: &str) -> bool {
        head.strip_prefix("SlottedVar_")
            .is_some_and(|n| n.parse::<i64>().is_ok())
    }
}

#[derive(Clone, Debug, Default)]
pub struct SlottedProofState {
    carriers: Carriers,
    layouts: HashMap<String, RawLayout>,
    sources: Vec<Source>,
    /// The claim the next `prove` is about: the last one recorded.
    current_claim: Option<i64>,
    /// The facts of the `prove` being run, in order: the existence rule's
    /// premises line up with them.
    claim_facts: Vec<Fact>,
}

const METADATA_TABLES: &[&str] = &[
    "SlottedCarrier",
    "SlottedNodeLayout",
    "SlottedEdgeLayout",
    "SlottedBinderLayout",
    "SlottedPayloadLayout",
    "SlottedRuleSource",
    "SlottedLetSource",
    "SlottedUnionSource",
    "SlottedClaimSource",
];

fn lit_string(e: &Expr) -> Option<String> {
    match e {
        GenericExpr::Lit(_, Literal::String(s)) => Some(s.clone()),
        _ => None,
    }
}

fn lit_int(e: &Expr) -> Option<i64> {
    match e {
        GenericExpr::Lit(_, Literal::Int(n)) => Some(*n),
        _ => None,
    }
}

impl SlottedProofState {
    /// Record a top-level `(set (Slotted... args) ())` if it is one of the
    /// metadata tables. Returns whether it was.
    pub fn record(&mut self, head: &str, args: &[Expr]) -> Result<bool, SourceError> {
        if !METADATA_TABLES.contains(&head) {
            return Ok(false);
        }
        let bad = || SourceError(format!("malformed metadata row ({head} ...)"));
        let s = |i: usize| args.get(i).and_then(lit_string).ok_or_else(bad);
        let n = |i: usize| args.get(i).and_then(lit_int).ok_or_else(bad);
        match head {
            "SlottedCarrier" => {
                self.carriers.index.insert(s(0)?, n(1)?);
            }
            "SlottedNodeLayout" => {
                let arity = usize::try_from(n(1)?).map_err(|_| bad())?;
                self.layouts.entry(s(0)?).or_default().arity = Some(arity);
            }
            "SlottedEdgeLayout" => {
                let edge = usize::try_from(n(1)?).map_err(|_| bad())?;
                self.layouts.entry(s(0)?).or_default().edges.insert(edge);
            }
            "SlottedBinderLayout" => {
                let edge = usize::try_from(n(1)?).map_err(|_| bad())?;
                self.layouts.entry(s(0)?).or_default().binders.insert(edge);
            }
            "SlottedPayloadLayout" => {
                let col = usize::try_from(n(1)?).map_err(|_| bad())?;
                self.layouts.entry(s(0)?).or_default().payloads.insert(col);
            }
            "SlottedRuleSource" => self.sources.push(Source::Rule(s(0)?, s(1)?)),
            "SlottedLetSource" => self.sources.push(Source::Let(s(0)?, s(1)?)),
            "SlottedUnionSource" => self.sources.push(Source::Union(s(0)?, s(1)?)),
            "SlottedClaimSource" => {
                let index = n(0)?;
                self.sources.push(Source::Claim(index, s(1)?, s(2)?, s(3)?));
                self.current_claim = Some(index);
            }
            _ => unreachable!(),
        }
        Ok(true)
    }

    /// Remember the facts of the `prove` about to run.
    pub fn record_prove(&mut self, facts: Vec<Fact>) {
        self.claim_facts = facts;
    }

    pub fn carriers(&self) -> &Carriers {
        &self.carriers
    }

    /// The source program as recorded so far, over a fresh term dag.
    pub fn program(&self) -> Result<(SlottedProgram, TermDag), SourceError> {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        for (name, layout) in &self.layouts {
            if self.carriers.is_var_constructor(name) {
                continue;
            }
            let arity = layout
                .arity
                .ok_or_else(|| SourceError(format!("constructor {name} has no node layout")))?;
            let mut columns = vec![];
            let mut i = 0;
            while i < arity {
                if layout.edges.contains(&i) {
                    columns.push(if layout.binders.contains(&i) {
                        ColumnKind::Binder
                    } else {
                        ColumnKind::Child
                    });
                    i += 2;
                } else if layout.payloads.contains(&i) {
                    columns.push(ColumnKind::Payload);
                    i += 1;
                } else {
                    return Err(SourceError(format!(
                        "constructor {name}: physical column {i} is neither an edge nor a payload"
                    )));
                }
            }
            program.add_constructor(name, columns);
        }
        for source in &self.sources {
            match source {
                Source::Let(name, text) => program.add_let(&mut dag, name, text)?,
                Source::Union(a, b) => program.add_union(&mut dag, a, b)?,
                Source::Rule(name, text) => {
                    program.add_named_rewrite(&mut dag, Some(name), text)?;
                }
                Source::Claim(index, kind, a, b) => {
                    program.add_claim(&mut dag, *index, kind, a, b)?
                }
            }
        }
        Ok((program, dag))
    }

    /// Translate the egglog proof of the current claim and check it. Returns the
    /// slotted proof's text.
    pub fn prove(&mut self, egg: &ProofStore, root: ProofId) -> Result<String, String> {
        let index = self
            .current_claim
            .ok_or_else(|| "a prove ran before any claim was recorded".to_string())?;
        let (program, dag) = self.program().map_err(|e| e.to_string())?;
        let claim = program
            .claims
            .iter()
            .find(|c| c.index == index)
            .cloned()
            .ok_or_else(|| format!("claim {index} was not recorded"))?;
        log::debug!(
            "egglog proof of claim {index}:\n{}",
            egg.proof_to_string(root)
        );
        let translated = translate(
            &program,
            dag,
            &self.carriers,
            egg,
            root,
            &claim,
            &self.claim_facts,
        )
        .map_err(|e| format!("claim {index}: {e}"))?;
        let (mut store, proof) = translated;
        check_claim(&mut store, &program, &claim, proof).map_err(|e| {
            format!(
                "the translated proof does not check: {e}\n{}",
                store.proof_to_string(proof)
            )
        })?;
        Ok(store.proof_to_string(proof))
    }
}
