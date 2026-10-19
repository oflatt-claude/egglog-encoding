use std::collections::{BTreeMap, BTreeSet};

use egraph_serialize::{ClassId, EGraph, NodeId};
use serde::{Deserialize, Serialize};

use crate::Error;

/// The standard serialized e-graph, optionally annotated with slotted structure.
/// Ordinary consumers of `egraph-serialize` can still read the flattened document.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct AnnotatedEGraph {
    #[serde(flatten)]
    pub egraph: EGraph,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub slotted: Option<Slotted>,
}

/// Complete annotations: when present, every class and node must have an entry.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Slotted {
    pub classes: BTreeMap<ClassId, ClassSlots>,
    pub nodes: BTreeMap<NodeId, NodeSlots>,
}

/// Slots are class-local names. Each group element is a permutation of their indices.
/// Supply the full group, including identity; the reader validates rather than closes it.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ClassSlots {
    pub slots: Vec<String>,
    pub group: Vec<Vec<usize>>,
}

/// Arguments interleave direct slots and the standard node's ordered children.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeSlots {
    pub arguments: Vec<Argument>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Argument {
    Slot {
        slot: String,
    },
    /// The next child in `Node::children`, with its complete injective slot map.
    Child {
        renaming: Vec<(String, String)>,
    },
}

/// A validated graph. IDs and slot spellings have no semantic role in matching.
#[derive(Clone, Debug)]
pub struct Graph {
    pub(crate) classes: Vec<Class>,
    pub(crate) indices: BTreeMap<ClassId, usize>,
    pub(crate) roots: Vec<usize>,
}

#[derive(Clone, Debug)]
pub(crate) struct Class {
    pub id: ClassId,
    pub sort: Option<String>,
    pub slots: usize,
    pub group: Vec<Vec<usize>>,
    pub nodes: Vec<Node>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Label {
    pub op: String,
    pub subsumed: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct Node {
    pub id: NodeId,
    pub label: Label,
    pub args: Vec<Arg>,
    /// Number of private (binder or redundant) slots, in first-occurrence order.
    pub locals: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Arg {
    Slot(usize),
    Child { class: usize, slots: Vec<usize> },
}

impl Node {
    pub fn children(&self) -> impl Iterator<Item = usize> + '_ {
        self.args.iter().filter_map(|arg| match arg {
            Arg::Child { class, .. } => Some(*class),
            Arg::Slot(_) => None,
        })
    }
}

/// Exact group validation using incremental generation. Missing products are errors.
pub(crate) fn closed_group(group: &BTreeSet<Vec<usize>>, degree: usize) -> bool {
    let identity: Vec<_> = (0..degree).collect();
    if !group.contains(&identity) {
        return false;
    }
    let mut generated = BTreeSet::from([identity.clone()]);
    let mut generators = Vec::new();
    for p in group {
        if generated.contains(p) {
            continue;
        }
        generators.push(p);
        let mut pending: Vec<_> = generated.iter().cloned().collect();
        let mut i = 0;
        while i < pending.len() {
            for generator in &generators {
                let product: Vec<_> = pending[i].iter().map(|&v| generator[v]).collect();
                if !group.contains(&product) {
                    return false;
                }
                if generated.insert(product.clone()) {
                    pending.push(product);
                }
            }
            i += 1;
        }
    }
    true
}

pub(crate) fn bijection(values: &[usize], degree: usize) -> bool {
    values.len() == degree
        && values.iter().copied().collect::<BTreeSet<_>>() == (0..degree).collect()
}

impl TryFrom<&AnnotatedEGraph> for Graph {
    type Error = Error;

    fn try_from(doc: &AnnotatedEGraph) -> Result<Self, Error> {
        let graph = &doc.egraph;
        let mut ids: BTreeSet<_> = graph.class_data.keys().cloned().collect();
        ids.extend(graph.nodes.values().map(|n| n.eclass.clone()));
        if let Some(slotted) = &doc.slotted {
            // An explicitly annotated empty class must not disappear.
            ids.extend(slotted.classes.keys().cloned());
            if ids != slotted.classes.keys().cloned().collect()
                || graph.nodes.keys().cloned().collect::<BTreeSet<_>>()
                    != slotted.nodes.keys().cloned().collect()
            {
                return Err(Error(
                    "slotted annotations must cover exactly the graph's classes and nodes".into(),
                ));
            }
        }
        let indices: BTreeMap<_, _> = ids.into_iter().enumerate().map(|(i, id)| (id, i)).collect();
        let mut classes = Vec::new();
        let mut named_slots = Vec::new();
        for id in indices.keys() {
            let (slots, group) = if let Some(slotted) = &doc.slotted {
                let data = &slotted.classes[id];
                let slots: BTreeMap<_, _> = data
                    .slots
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(i, s)| (s, i))
                    .collect();
                if slots.len() != data.slots.len() {
                    return Err(Error(format!("{id}: repeated class slot")));
                }
                let group: BTreeSet<_> = data.group.iter().cloned().collect();
                if group.len() != data.group.len()
                    || group.iter().any(|p| !bijection(p, slots.len()))
                    || !closed_group(&group, slots.len())
                {
                    return Err(Error(format!("{id}: invalid or incomplete symmetry group")));
                }
                (slots, group.into_iter().collect())
            } else {
                (BTreeMap::new(), vec![vec![]])
            };
            classes.push(Class {
                id: id.clone(),
                sort: graph.class_data.get(id).and_then(|c| c.typ.clone()),
                slots: slots.len(),
                group,
                nodes: Vec::new(),
            });
            named_slots.push(slots);
        }
        let mut node_ids: Vec<_> = graph.nodes.keys().collect();
        node_ids.sort();
        for id in node_ids {
            let raw = &graph.nodes[id];
            let class = indices[&raw.eclass];
            let mut frame = named_slots[class].clone();
            let mut args = Vec::new();
            let mut children = raw.children.iter();
            let ordinary: Vec<_>;
            let annotations = if let Some(slotted) = &doc.slotted {
                &slotted.nodes[id].arguments
            } else {
                ordinary = raw
                    .children
                    .iter()
                    .map(|_| Argument::Child { renaming: vec![] })
                    .collect();
                &ordinary
            };
            for arg in annotations {
                match arg {
                    Argument::Slot { slot } => {
                        let fresh = frame.len();
                        args.push(Arg::Slot(*frame.entry(slot.clone()).or_insert(fresh)));
                    }
                    Argument::Child { renaming } => {
                        let child_id = children.next().ok_or_else(|| {
                            Error(format!("{id}: too many annotated child edges"))
                        })?;
                        let child = graph
                            .nodes
                            .get(child_id)
                            .ok_or_else(|| Error(format!("{id}: missing child node {child_id}")))?;
                        let child_class = indices[&child.eclass];
                        let domain = &named_slots[child_class];
                        let keys: BTreeSet<_> = renaming.iter().map(|(k, _)| k).collect();
                        let values: BTreeSet<_> = renaming.iter().map(|(_, v)| v).collect();
                        if keys.len() != renaming.len()
                            || values.len() != renaming.len()
                            || keys != domain.keys().collect()
                        {
                            return Err(Error(format!(
                                "{id}: child slot map must be injective with exactly the child's slots as its domain"
                            )));
                        }
                        let mut slots = vec![0; domain.len()];
                        for (key, value) in renaming {
                            let fresh = frame.len();
                            slots[domain[key]] = *frame.entry(value.clone()).or_insert(fresh);
                        }
                        args.push(Arg::Child {
                            class: child_class,
                            slots,
                        });
                    }
                }
            }
            if children.next().is_some() {
                return Err(Error(format!("{id}: missing annotated child edges")));
            }
            classes[class].nodes.push(Node {
                id: id.clone(),
                label: Label {
                    op: raw.op.clone(),
                    subsumed: raw.subsumed,
                },
                args,
                locals: frame.len() - named_slots[class].len(),
            });
        }
        let roots = graph
            .root_eclasses
            .iter()
            .map(|id| {
                indices
                    .get(id)
                    .copied()
                    .ok_or_else(|| Error(format!("missing root class {id}")))
            })
            .collect::<Result<_, _>>()?;
        Ok(Self {
            classes,
            indices,
            roots,
        })
    }
}
