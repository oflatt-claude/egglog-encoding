//! Runs the slotted proof pipeline inside an e-graph: records the source
//! metadata the compiler publishes as the program runs, and on each
//! `prove-slotted` translates the egglog proof to a slotted proof of the
//! command's claim and checks it.

use super::checker::check_claim;
use super::source::{ColumnKind, SlottedProgram, SourceError};
use super::translate::translate;
use crate::ast::{Expr, Literal, SlottedClaim};
use crate::proofs::proof_format::{ProofId, ProofStore};
use crate::util::HashMap;
use crate::{GenericExpr, TermDag};
use std::collections::BTreeSet;

/// One source-level fact the compiler recorded, in program order.
#[derive(Clone, Debug)]
enum Source {
    Let(String, String),
    Union(String, String, String),
    Rule(String, String),
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
    /// Is this the variable constructor of a registered carrier? A user
    /// constructor that happens to be spelled `SlottedVar_7` is not one unless
    /// carrier 7 exists.
    pub fn is_var_constructor(&self, head: &str) -> bool {
        head.strip_prefix("SlottedVar_")
            .and_then(|n| n.parse::<i64>().ok())
            .is_some_and(|n| self.index.values().any(|&i| i == n))
    }
}

#[derive(Clone, Debug, Default)]
pub struct SlottedProofState {
    carriers: Carriers,
    layouts: HashMap<String, RawLayout>,
    /// Each declared constructor's input and output sorts, as the encoded
    /// program declares them: a child column is a `Renaming` and then its sort.
    signatures: HashMap<String, (Vec<String>, String)>,
    sources: Vec<Source>,
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
            "SlottedUnionSource" => self.sources.push(Source::Union(s(0)?, s(1)?, s(2)?)),
            _ => unreachable!(),
        }
        Ok(true)
    }

    /// Record a constructor declaration: the sorts its columns and output have.
    pub fn record_constructor(&mut self, name: &str, inputs: &[String], outputs: &[String]) {
        if let [output] = outputs {
            self.signatures
                .insert(name.to_string(), (inputs.to_vec(), output.clone()));
        }
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
            let (inputs, output) = self
                .signatures
                .get(name)
                .ok_or_else(|| SourceError(format!("constructor {name} was never declared")))?;
            if inputs.len() != arity {
                return Err(SourceError(format!(
                    "constructor {name} is declared with {} columns, its layout has {arity}",
                    inputs.len()
                )));
            }
            let mut columns = vec![];
            let mut i = 0;
            while i < arity {
                if layout.edges.contains(&i) {
                    let kind = if layout.binders.contains(&i) {
                        ColumnKind::Binder
                    } else {
                        ColumnKind::Child
                    };
                    // the edge's renaming, then the child's sort
                    let sort = inputs.get(i + 1).cloned().ok_or_else(|| {
                        SourceError(format!("constructor {name}: edge {i} has no class column"))
                    })?;
                    columns.push((kind, sort));
                    i += 2;
                } else if layout.payloads.contains(&i) {
                    columns.push((ColumnKind::Payload, inputs[i].clone()));
                    i += 1;
                } else {
                    return Err(SourceError(format!(
                        "constructor {name}: physical column {i} is neither an edge nor a payload"
                    )));
                }
            }
            program.add_sorted_constructor(name, output, columns);
        }
        for source in &self.sources {
            match source {
                Source::Let(name, text) => program.add_let(&mut dag, name, text)?,
                Source::Union(a, b, sort) => program.add_union(&mut dag, a, b, sort)?,
                Source::Rule(name, text) => {
                    program.add_named_rewrite(&mut dag, Some(name), text)?;
                }
            }
        }
        Ok((program, dag))
    }

    /// Translate the egglog proof `root` of a `prove-slotted` to a slotted proof
    /// of its claim and check it. Returns the slotted proof's text.
    pub fn prove(
        &self,
        egg: &ProofStore,
        root: ProofId,
        claim: &SlottedClaim,
    ) -> Result<String, String> {
        let (program, mut dag) = self.program().map_err(|e| e.to_string())?;
        let source = program
            .claim(&mut dag, &claim.kind, &claim.sort, &claim.lhs, &claim.rhs)
            .map_err(|e| format!("claim {claim}: {e}"))?;
        log::debug!(
            "egglog proof of claim {claim}:\n{}",
            egg.proof_to_string(root)
        );
        let translated = translate(
            &program,
            dag,
            &self.carriers,
            egg,
            root,
            &source,
            [&claim.lhs_class, &claim.rhs_class],
        )
        .map_err(|e| format!("claim {claim}: {e}"))?;
        let (mut store, proof) = translated;
        check_claim(&mut store, &program, &source, proof).map_err(|e| {
            format!(
                "the translated proof does not check: {e}\n{}",
                store.proof_to_string(proof)
            )
        })?;
        Ok(store.proof_to_string(proof))
    }
}
