use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::graph::{Arg, Class, Graph, Label, Node};
use crate::witness::{ClassMatch, NodeMatch, Witness};
use crate::{Limits, Outcome};

#[derive(Debug)]
struct Limit(&'static str);

struct Budget {
    remaining: usize,
    name: &'static str,
}
impl Budget {
    fn tick(&mut self) -> Result<(), Limit> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Limit(self.name))?;
        Ok(())
    }
}

fn intern<T: Ord>(palette: &mut BTreeMap<T, usize>, signature: T) -> usize {
    let fresh = palette.len();
    *palette.entry(signature).or_insert(fresh)
}

type ClassSignature = (
    usize,
    Option<String>,
    usize,
    usize,
    Vec<usize>,
    Vec<(Label, Vec<Option<usize>>)>,
);

fn colors(left: &Graph, right: &Graph) -> (Vec<usize>, Vec<usize>) {
    let graphs = [left, right];
    let mut colors = [vec![0; left.classes.len()], vec![0; right.classes.len()]];
    for _ in 0..7 {
        let old_count = colors.iter().flatten().collect::<BTreeSet<_>>().len();
        let mut palette = BTreeMap::<ClassSignature, usize>::new();
        let next = std::array::from_fn(|side| {
            let graph = graphs[side];
            graph
                .classes
                .iter()
                .enumerate()
                .map(|(c, class)| {
                    let mut nodes: Vec<_> = class
                        .nodes
                        .iter()
                        .map(|n| {
                            (
                                n.label.clone(),
                                n.args
                                    .iter()
                                    .map(|a| match a {
                                        Arg::Slot(_) => None,
                                        Arg::Child { class, .. } => Some(colors[side][*class]),
                                    })
                                    .collect(),
                            )
                        })
                        .collect();
                    nodes.sort();
                    let roots = graph
                        .roots
                        .iter()
                        .enumerate()
                        .filter_map(|(i, &r)| (r == c).then_some(i))
                        .collect();
                    intern(
                        &mut palette,
                        (
                            colors[side][c],
                            class.sort.clone(),
                            class.slots,
                            class.group.len(),
                            roots,
                            nodes,
                        ),
                    )
                })
                .collect()
        });
        colors = next;
        if palette.len() == old_count {
            break;
        }
    }
    let [a, b] = colors;
    (a, b)
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Occurrence {
    Direct(Label, usize),
    Edge(Label, usize, usize, usize),
}

type SlotColors = Vec<Vec<usize>>;

fn slot_colors(
    left: &Graph,
    right: &Graph,
    lc: &[usize],
    rc: &[usize],
) -> (SlotColors, SlotColors) {
    let graphs = [left, right];
    let cc = [lc, rc];
    let mut colors = [left, right].map(|g| {
        g.classes
            .iter()
            .map(|c| vec![0; c.slots])
            .collect::<SlotColors>()
    });
    for _ in 0..3 {
        let mut palette = BTreeMap::new();
        let next = std::array::from_fn(|side| {
            let graph = graphs[side];
            graph
                .classes
                .iter()
                .enumerate()
                .map(|(c, class)| {
                    let mut occurrences = vec![Vec::new(); class.slots];
                    for n in &class.nodes {
                        for (column, arg) in n.args.iter().enumerate() {
                            match arg {
                                Arg::Slot(s) if *s < class.slots => occurrences[*s]
                                    .push(Occurrence::Direct(n.label.clone(), column)),
                                Arg::Slot(_) => {}
                                Arg::Child {
                                    class: child,
                                    slots,
                                } => {
                                    for (cs, &ps) in slots.iter().enumerate() {
                                        if ps < class.slots {
                                            occurrences[ps].push(Occurrence::Edge(
                                                n.label.clone(),
                                                column,
                                                cc[side][*child],
                                                colors[side][*child][cs],
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    (0..class.slots)
                        .map(|s| {
                            let orbit: BTreeSet<_> = class.group.iter().map(|p| p[s]).collect();
                            let mut all: Vec<_> = orbit
                                .iter()
                                .flat_map(|&s| occurrences[s].iter().cloned())
                                .collect();
                            all.sort();
                            intern(&mut palette, (colors[side][c][s], all))
                        })
                        .collect()
                })
                .collect()
        });
        colors = next;
    }
    let [a, b] = colors;
    (a, b)
}

fn depths(graph: &Graph) -> Vec<usize> {
    let mut depth = vec![usize::MAX; graph.classes.len()];
    loop {
        let mut changed = false;
        for (c, class) in graph.classes.iter().enumerate() {
            for n in &class.nodes {
                let d = n
                    .children()
                    .filter(|&k| k != c)
                    .map(|k| depth[k])
                    .max()
                    .unwrap_or(0)
                    .saturating_add(1);
                if d < depth[c] {
                    depth[c] = d;
                    changed = true;
                }
            }
        }
        if !changed {
            return depth;
        }
    }
}

fn next_permutation(xs: &mut [usize]) -> bool {
    let Some(i) = (0..xs.len().saturating_sub(1))
        .rev()
        .find(|&i| xs[i] < xs[i + 1])
    else {
        return false;
    };
    let j = (i + 1..xs.len()).rev().find(|&j| xs[i] < xs[j]).unwrap();
    xs.swap(i, j);
    xs[i + 1..].reverse();
    true
}

/// All bijections preserving slot colors.
struct Bijections {
    source: Vec<Vec<usize>>,
    target: Vec<Vec<usize>>,
    degree: usize,
    first: bool,
    done: bool,
}
impl Bijections {
    fn new(source: &[usize], target: &[usize]) -> Self {
        let bins = |colors: &[usize]| {
            let mut bins = BTreeMap::<usize, Vec<usize>>::new();
            for (s, &color) in colors.iter().enumerate() {
                bins.entry(color).or_default().push(s);
            }
            bins
        };
        let a = bins(source);
        let b = bins(target);
        let done = a.keys().ne(b.keys())
            || a.iter()
                .any(|(k, v)| b.get(k).is_none_or(|x| x.len() != v.len()));
        Self {
            source: a.into_values().collect(),
            target: b.into_values().collect(),
            degree: source.len(),
            first: true,
            done,
        }
    }
}
impl Iterator for Bijections {
    type Item = Vec<usize>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        if !self.first {
            let mut advanced = false;
            for cell in self.target.iter_mut().rev() {
                if next_permutation(cell) {
                    advanced = true;
                    break;
                }
                cell.sort();
            }
            if !advanced {
                self.done = true;
                return None;
            }
        }
        self.first = false;
        let mut map = vec![0; self.degree];
        for (a, b) in self.source.iter().zip(&self.target) {
            for (&x, &y) in a.iter().zip(b) {
                map[x] = y;
            }
        }
        Some(map)
    }
}

fn conjugates(a: &Class, b: &Class, slots: &[usize]) -> bool {
    a.group.iter().all(|p| {
        let mut image = vec![0; slots.len()];
        for (i, &j) in p.iter().enumerate() {
            image[slots[i]] = slots[j];
        }
        b.group.binary_search(&image).is_ok()
    })
}

/// Target-node representatives, retaining the group elements that produced each one.
type Variants = BTreeMap<Vec<Arg>, (usize, Vec<usize>)>;

fn variants(
    graph: &Graph,
    class: usize,
    node: &Node,
    budget: &mut Budget,
) -> Result<Variants, Limit> {
    let children: Vec<_> = node.children().collect();
    let sizes: Vec<_> = std::iter::once(graph.classes[class].group.len())
        .chain(children.iter().map(|&c| graph.classes[c].group.len()))
        .collect();
    let mut choice = vec![0; sizes.len()];
    let mut result = BTreeMap::new();
    loop {
        budget.tick()?;
        let parent = &graph.classes[class].group[choice[0]];
        let image = |s: usize| if s < parent.len() { parent[s] } else { s };
        let mut child = 0;
        let args = node
            .args
            .iter()
            .map(|arg| match arg {
                Arg::Slot(s) => Arg::Slot(image(*s)),
                Arg::Child { class, slots } => {
                    child += 1;
                    let group = &graph.classes[*class].group[choice[child]];
                    Arg::Child {
                        class: *class,
                        slots: group.iter().map(|&s| image(slots[s])).collect(),
                    }
                }
            })
            .collect();
        result
            .entry(args)
            .or_insert_with(|| (choice[0], choice[1..].to_vec()));
        let mut i = choice.len();
        loop {
            if i == 0 {
                return Ok(result);
            }
            i -= 1;
            choice[i] += 1;
            if choice[i] < sizes[i] {
                break;
            }
            choice[i] = 0;
        }
    }
}

struct Mapping<'a> {
    classes: &'a [Option<usize>],
    slots: &'a [Vec<usize>],
    parent: &'a [usize],
}

fn compatible(
    source: &Node,
    target: &Node,
    a: &Class,
    b: &Class,
    mapping: &Mapping<'_>,
    variants: &Variants,
    budget: &mut Budget,
) -> Result<Option<NodeMatch>, Limit> {
    if source.label != target.label
        || source.locals != target.locals
        || source.args.len() != target.args.len()
    {
        return Ok(None);
    }
    for locals in Bijections::new(&vec![0; source.locals], &vec![0; target.locals]) {
        budget.tick()?;
        let image = |s: usize| {
            if s < a.slots {
                mapping.parent[s]
            } else {
                b.slots + locals[s - a.slots]
            }
        };
        let args = source
            .args
            .iter()
            .map(|arg| match arg {
                Arg::Slot(s) => Arg::Slot(image(*s)),
                Arg::Child { class, slots } => {
                    let mut moved = vec![0; slots.len()];
                    for (s, &p) in slots.iter().enumerate() {
                        moved[mapping.slots[*class][s]] = image(p);
                    }
                    Arg::Child {
                        class: mapping.classes[*class].unwrap(),
                        slots: moved,
                    }
                }
            })
            .collect::<Vec<_>>();
        if let Some((parent, children)) = variants.get(&args) {
            return Ok(Some(NodeMatch {
                target: target.id.clone(),
                locals,
                parent: *parent,
                children: children.clone(),
            }));
        }
    }
    Ok(None)
}

fn match_nodes(
    left: &Graph,
    right: &Graph,
    a: usize,
    b: usize,
    phi: &[Option<usize>],
    sig: &[Vec<usize>],
    cap: usize,
) -> Result<Option<BTreeMap<egraph_serialize::NodeId, NodeMatch>>, Limit> {
    let source = &left.classes[a];
    let target = &right.classes[b];
    if source.nodes.len() != target.nodes.len() {
        return Ok(None);
    }
    let mut budget = Budget {
        remaining: cap,
        name: "node-variant cap reached",
    };
    let variants = target
        .nodes
        .iter()
        .map(|n| variants(right, b, n, &mut budget))
        .collect::<Result<Vec<_>, _>>()?;
    let mut pairs: Vec<Option<(usize, NodeMatch)>> = vec![None; target.nodes.len()];
    // Iterative augmenting paths avoid recursion proportional to class size.
    for start in 0..source.nodes.len() {
        let mut queue = VecDeque::from([start]);
        let mut seen = vec![false; target.nodes.len()];
        let mut back: Vec<Option<(usize, usize, NodeMatch)>> = vec![None; source.nodes.len()];
        let mut found = false;
        'search: while let Some(i) = queue.pop_front() {
            for j in 0..target.nodes.len() {
                if seen[j] {
                    continue;
                }
                let Some(cert) = compatible(
                    &source.nodes[i],
                    &target.nodes[j],
                    source,
                    target,
                    &Mapping {
                        classes: phi,
                        slots: sig,
                        parent: &sig[a],
                    },
                    &variants[j],
                    &mut budget,
                )?
                else {
                    continue;
                };
                seen[j] = true;
                if let Some((old, _)) = &pairs[j] {
                    back[*old] = Some((i, j, cert));
                    queue.push_back(*old);
                } else {
                    pairs[j] = Some((i, cert));
                    let mut current = i;
                    while let Some((previous, edge, cert)) = back[current].take() {
                        pairs[edge] = Some((previous, cert));
                        current = previous;
                    }
                    found = true;
                    break 'search;
                }
            }
        }
        if !found {
            return Ok(None);
        }
    }
    Ok(Some(
        pairs
            .into_iter()
            .map(|pair| {
                let (i, cert) = pair.unwrap();
                (source.nodes[i].id.clone(), cert)
            })
            .collect(),
    ))
}

struct Frame {
    candidates: Vec<usize>,
    next: usize,
    slots: Option<Bijections>,
}
impl Frame {
    fn new(candidates: &[usize]) -> Self {
        Self {
            candidates: candidates.to_vec(),
            next: 0,
            slots: None,
        }
    }
    fn next_mapping(
        &mut self,
        used: &[bool],
        source_colors: &[usize],
        target_colors: &[Vec<usize>],
        budget: &mut Budget,
    ) -> Result<Option<(usize, Vec<usize>)>, Limit> {
        while let Some(&b) = self.candidates.get(self.next) {
            if used[b] {
                self.next += 1;
                self.slots = None;
                continue;
            }
            let slots = self
                .slots
                .get_or_insert_with(|| Bijections::new(source_colors, &target_colors[b]));
            if let Some(m) = slots.next() {
                budget.tick()?;
                return Ok(Some((b, m)));
            }
            self.next += 1;
            self.slots = None;
        }
        Ok(None)
    }
}

pub(crate) fn search(left: &Graph, right: &Graph, limits: Limits) -> Outcome {
    match search_inner(left, right, limits) {
        Ok(Some(witness)) => Outcome::Isomorphic { witness },
        Ok(None) => Outcome::Different {
            reason: "no isomorphism exists (search exhausted)".into(),
        },
        Err(Limit(reason)) => Outcome::Inconclusive {
            reason: reason.into(),
        },
    }
}

fn search_inner(left: &Graph, right: &Graph, limits: Limits) -> Result<Option<Witness>, Limit> {
    if left.classes.len() != right.classes.len() || left.roots.len() != right.roots.len() {
        return Ok(None);
    }
    let (lc, rc) = colors(left, right);
    let counts = |colors: &[usize]| {
        let mut counts = BTreeMap::new();
        for c in colors {
            *counts.entry(*c).or_insert(0) += 1;
        }
        counts
    };
    if counts(&lc) != counts(&rc) {
        return Ok(None);
    }
    let (ls, rs) = slot_colors(left, right, &lc, &rc);
    let mut by_color = BTreeMap::<usize, Vec<usize>>::new();
    for (b, &color) in rc.iter().enumerate() {
        by_color.entry(color).or_default().push(b);
    }
    let candidates: Vec<_> = lc.iter().map(|c| by_color[c].clone()).collect();
    let depth = depths(left);
    let mut order: Vec<_> = (0..left.classes.len()).collect();
    order.sort_by_key(|&a| (depth[a], candidates[a].len(), a));
    let mut phi = vec![None; order.len()];
    let mut sig = vec![vec![]; order.len()];
    let mut used = vec![false; order.len()];
    let mut budget = Budget {
        remaining: limits.search,
        name: "search cap reached",
    };
    if order.is_empty() {
        return Ok(Some(Witness {
            classes: BTreeMap::new(),
        }));
    }
    let mut frames = vec![Frame::new(&candidates[order[0]])];
    loop {
        let k = frames.len() - 1;
        let a = order[k];
        if let Some(b) = phi[a].take() {
            used[b] = false;
        }
        let Some((b, m)) = frames[k].next_mapping(&used, &ls[a], &rs, &mut budget)? else {
            frames.pop();
            if frames.is_empty() {
                return Ok(None);
            }
            continue;
        };
        if !conjugates(&left.classes[a], &right.classes[b], &m) {
            continue;
        }
        phi[a] = Some(b);
        sig[a] = m;
        used[b] = true;
        let ready = left.classes[a]
            .nodes
            .iter()
            .flat_map(Node::children)
            .all(|c| phi[c].is_some());
        if ready && match_nodes(left, right, a, b, &phi, &sig, limits.node_variants)?.is_none() {
            continue;
        }
        if k + 1 < order.len() {
            frames.push(Frame::new(&candidates[order[k + 1]]));
            continue;
        }
        let mut classes = BTreeMap::new();
        for (c, class) in left.classes.iter().enumerate() {
            let d = phi[c].unwrap();
            let Some(nodes) = match_nodes(left, right, c, d, &phi, &sig, limits.node_variants)?
            else {
                break;
            };
            classes.insert(
                class.id.clone(),
                ClassMatch {
                    target: right.classes[d].id.clone(),
                    slots: sig[c].clone(),
                    nodes,
                },
            );
        }
        if classes.len() == order.len() {
            return Ok(Some(Witness { classes }));
        }
    }
}
