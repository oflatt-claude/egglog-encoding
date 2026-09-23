//! Slotted matching frames: what a rule's atoms say about slots, joined.
//!
//! egglog finds the e-nodes a slotted pattern matches; this decides what the match
//! says about SLOTS. Every column of every matched node contributes equations
//! between *occurrences* of slots, and a frame is the closure of those equations:
//!
//! * `Node(a, s)` is slot `s` of the e-node matched at the atom rooted at variable `a`;
//! * `Var(v, t)` is slot `t` of the class variable `v` is bound to;
//! * `Lit("$x")` is a slot the pattern wrote, or one the right-hand side minted.
//!
//! An atom labelled `a` and rooted at `p` whose column carries `v` by the edge `e` says
//! `Node(a, e(t)) = Var(v, t)` for every class slot `t`; its root says `Node(a, s) =
//! Var(p, s)`; a literal `$x` at edge `e` says `Node(a, e(0)) = Lit("$x")`. The label
//! is the atom's own, since three atoms rooted at one variable match three e-nodes of
//! its class. A second occurrence of a variable comes with a symmetry of its class,
//! composed into the equation, so the match quantifies over the class's group.
//!
//! The equations say which occurrences are ONE slot; the CLIQUES say which are
//! DIFFERENT slots. A clique is a set of occurrences every two of which must be
//! distinct slots, so no two of them may share a block of the partition: the slots
//! of one e-node, the slots of one class, and the different literals. A frame is
//! consistent when no clique is broken.
//!
//! [`Frame::join`] unions two frames' equations and re-closes; it is associative and
//! commutative, so the atoms of a pattern may be joined in any order and evaluated as
//! soon as each is matched. Where two atoms agree on a variable the join identifies
//! the occurrences on both sides, which is the reference's `unify`: a slot no
//! equation has tied down is a placeholder, not a name that was committed to. The
//! blocks of the closure are the pattern's slots, numbered in canonical order, and
//! [`Frame::refine`] enumerates the consistent ways the remaining blocks may be
//! merged, which is the reference's `final_refine`.

use super::*;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

type Slots = BTreeMap<i64, i64>;

/// Where a slot shows up in a match.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Occ {
    /// slot `s` of the e-node matched at the atom with this label
    Node(String, i64),
    /// slot `t` of the class this variable is bound to
    Var(String, i64),
    /// a literal the pattern wrote, or a slot the right-hand side minted
    Lit(String),
}

impl fmt::Display for Occ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Occ::Node(a, s) => write!(f, "{a}.{s}"),
            Occ::Var(v, t) => write!(f, "{v}:{t}"),
            Occ::Lit(x) => write!(f, "{x}"),
        }
    }
}

/// One column of an atom, as the pattern reads it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Binding {
    /// the atom's node is an invocation of this variable's class
    Root {
        var: String,
        class_slots: Slots,
        sym: Option<Slots>,
    },
    /// a child column carrying a variable by an edge
    Child {
        var: String,
        edge: Slots,
        class_slots: Slots,
        sym: Option<Slots>,
    },
    /// a slot literal; `carried` when the column is an ordinary one, whose slot
    /// refinement may merge
    Lit {
        name: String,
        edge: Slots,
        carried: bool,
    },
    /// a payload leaf reached through its own class: it names node slots, nothing more
    Leaf { edge: Slots },
    /// contract violations to commit on purpose, for mutation testing
    Bugs(BTreeSet<String>),
}

pub type Bd = Boxed<Binding>;

/// A list of pattern variables and literals, by name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Names(pub Vec<String>);

pub type Ns = Boxed<Names>;

/// The constraints a match has placed on slots so far, closed.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Frame {
    /// the partition of every occurrence named so far into the pattern's slots: two
    /// occurrences in one block are one slot, and `numbering` gives each block its
    /// number. Each block sorted, the blocks sorted by their least member. The
    /// cliques are not stored: `apart` reads them off the occurrences.
    blocks: Vec<Vec<Occ>>,
    /// per variable, the slots of its class: the domain of its renaming
    class_slots: BTreeMap<String, BTreeSet<i64>>,
    /// every literal, and whether refinement may merge a placeholder into its block
    literals: BTreeMap<String, bool>,
    /// deliberate violations of the contract, for mutation testing
    bugs: BTreeSet<String>,
    /// the variable whose class slots name the pattern's slots: a block holding
    /// `Var(anchor, t)` is slot `t`, the rest take the smallest free numbers
    anchor: Option<String>,
}

pub type Fr = Boxed<Frame>;

/// How many refinements are enumerated at most; index 0 is always the identity.
pub const REFINE_CAP: usize = 64;

impl Frame {
    /// One atom's constraints: its label, exactly one `Root` among the bindings, and
    /// every other binding a column of that node. `None` when the columns already
    /// contradict each other.
    pub fn atom(label: &str, bindings: &[Binding]) -> Option<Frame> {
        let mut roots = bindings.iter().filter_map(|b| match b {
            Binding::Root {
                var,
                class_slots,
                sym,
            } => Some((var, class_slots, sym)),
            _ => None,
        });
        let (root_var, root_slots, root_sym) = roots.next()?;
        if roots.next().is_some() {
            return None;
        }
        let atom = label.to_owned();
        let bugs: BTreeSet<String> = bindings
            .iter()
            .filter_map(|b| match b {
                Binding::Bugs(bugs) => Some(bugs.iter().cloned()),
                _ => None,
            })
            .flatten()
            .collect();
        let mut node_slots: BTreeSet<i64> = BTreeSet::new();
        let mut eqs: Vec<(Occ, Occ)> = Vec::new();
        let mut occs: BTreeSet<Occ> = BTreeSet::new();
        let mut class_slots: BTreeMap<String, BTreeSet<i64>> = BTreeMap::new();
        let mut literals: BTreeMap<String, bool> = BTreeMap::new();

        // the root: the node is an invocation of the variable's class
        let cs: BTreeSet<i64> = root_slots.keys().copied().collect();
        for &s in &cs {
            let t = match root_sym {
                Some(sym) => *sym.get(&s)?,
                None => s,
            };
            occs.insert(Occ::Var(root_var.clone(), t));
            eqs.push((Occ::Node(atom.clone(), s), Occ::Var(root_var.clone(), t)));
        }
        node_slots.extend(cs.iter().copied());
        class_slots.insert(root_var.clone(), cs);

        for b in bindings {
            match b {
                Binding::Root { .. } => {}
                Binding::Child {
                    var,
                    edge,
                    class_slots: cls,
                    sym,
                } => {
                    let cs: BTreeSet<i64> = cls.keys().copied().collect();
                    node_slots.extend(edge.values().copied());
                    for &t in &cs {
                        let u = match sym {
                            Some(sym) => *sym.get(&t)?,
                            None => t,
                        };
                        // every class slot is an occurrence, so a variable's renaming is
                        // total on its class: a slot no edge reaches is a mint of its own
                        occs.insert(Occ::Var(var.clone(), u));
                        if let Some(&s) = edge.get(&t) {
                            eqs.push((Occ::Node(atom.clone(), s), Occ::Var(var.clone(), u)));
                        }
                    }
                    if let Some(prev) = class_slots.insert(var.clone(), cs.clone())
                        && prev != cs
                    {
                        return None;
                    }
                }
                Binding::Lit {
                    name,
                    edge,
                    carried,
                } => {
                    let s = *edge.get(&0)?;
                    node_slots.extend(edge.values().copied());
                    occs.insert(Occ::Lit(name.clone()));
                    eqs.push((Occ::Node(atom.clone(), s), Occ::Lit(name.clone())));
                    let entry = literals.entry(name.clone()).or_insert(false);
                    *entry |= carried;
                }
                Binding::Leaf { edge } => node_slots.extend(edge.values().copied()),
                Binding::Bugs(_) => {}
            }
        }
        occs.extend(node_slots.iter().map(|&s| Occ::Node(atom.clone(), s)));

        let frame = Frame {
            blocks: close(occs, &eqs),
            class_slots,
            literals,
            bugs,
            anchor: None,
        };
        frame.consistent().then_some(frame)
    }

    /// Both frames' constraints together, closed; `None` when a clique breaks.
    /// Associative and commutative.
    pub fn join(&self, other: &Frame) -> Option<Frame> {
        let mut occs: BTreeSet<Occ> = BTreeSet::new();
        let mut eqs: Vec<(Occ, Occ)> = Vec::new();
        for block in self.blocks.iter().chain(&other.blocks) {
            occs.extend(block.iter().cloned());
            for pair in block.windows(2) {
                eqs.push((pair[0].clone(), pair[1].clone()));
            }
        }
        let mut class_slots = self.class_slots.clone();
        for (v, cs) in &other.class_slots {
            if let Some(prev) = class_slots.insert(v.clone(), cs.clone())
                && prev != *cs
            {
                return None;
            }
        }
        let mut literals = self.literals.clone();
        for (x, carried) in &other.literals {
            *literals.entry(x.clone()).or_insert(false) |= carried;
        }
        let frame = Frame {
            blocks: close(occs, &eqs),
            class_slots,
            literals,
            bugs: self.bugs.union(&other.bugs).cloned().collect(),
            anchor: self.anchor.clone().or_else(|| other.anchor.clone()),
        };
        frame.consistent().then_some(frame)
    }

    /// The frame spelled in this variable's slot names.
    pub fn anchored(&self, var: &str) -> Option<Frame> {
        self.class_slots.get(var)?;
        Some(Frame {
            anchor: Some(var.to_owned()),
            ..self.clone()
        })
    }

    /// Each block's slot number: the anchor's class slot where the block holds one,
    /// the smallest numbers the anchor does not use for the rest, in block order.
    fn numbering(&self) -> Vec<i64> {
        let mut out: Vec<Option<i64>> = vec![None; self.blocks.len()];
        let mut taken: BTreeSet<i64> = BTreeSet::new();
        if let Some(anchor) = &self.anchor {
            for (i, block) in self.blocks.iter().enumerate() {
                if let Some(t) = block.iter().find_map(|o| match o {
                    Occ::Var(v, t) if v == anchor => Some(*t),
                    _ => None,
                }) {
                    out[i] = Some(t);
                    taken.insert(t);
                }
            }
        }
        let mut next = 0;
        for slot in out.iter_mut() {
            if slot.is_none() {
                while taken.contains(&next) {
                    next += 1;
                }
                *slot = Some(next);
                next += 1;
            }
        }
        out.into_iter()
            .map(|s| s.expect("every block numbered"))
            .collect()
    }

    fn has_bug(&self, bug: &str) -> bool {
        self.bugs.contains(bug)
    }

    /// No clique has two members in one block.
    fn consistent(&self) -> bool {
        self.blocks.iter().all(|block| {
            block
                .iter()
                .enumerate()
                .all(|(i, o)| block[i + 1..].iter().all(|p| !self.violated(o, p)))
        })
    }

    /// `apart`, less the cliques a bug switches off.
    fn violated(&self, o: &Occ, p: &Occ) -> bool {
        let bug = match (o, p) {
            (Occ::Lit(_), Occ::Lit(_)) => "literals-alias",
            _ => "no-cliques",
        };
        apart(o, p) && !self.has_bug(bug)
    }

    /// The block an occurrence lies in.
    fn block_of(&self, occ: &Occ) -> Option<usize> {
        self.blocks
            .iter()
            .position(|c| c.binary_search(occ).is_ok())
    }

    /// The pattern slot an occurrence names.
    fn slot(&self, occ: &Occ) -> Option<i64> {
        self.block_of(occ).map(|i| self.numbering()[i])
    }

    /// A variable's renaming into the pattern's slots, or a literal's `{0 -> slot}`.
    pub fn ren(&self, name: &str) -> Option<Slots> {
        if name.starts_with('$') {
            if !self.literals.contains_key(name) {
                return None;
            }
            return Some(Slots::from([(0, self.slot(&Occ::Lit(name.to_owned()))?)]));
        }
        let cs = self.class_slots.get(name)?;
        cs.iter()
            .map(|&t| Some((t, self.slot(&Occ::Var(name.to_owned(), t))?)))
            .collect()
    }

    /// Does the literal's slot lie in any of these variables' images?
    pub fn is_free(&self, lit: &str, vars: &[String]) -> Option<bool> {
        let i = self.block_of(&Occ::Lit(lit.to_owned()))?;
        for v in vars {
            self.class_slots.get(v)?;
        }
        Some(
            self.blocks[i]
                .iter()
                .any(|o| matches!(o, Occ::Var(v, _) if vars.iter().any(|w| w == v))),
        )
    }

    /// The same invocation: equal renamings into the pattern's slots.
    pub fn same(&self, a: &str, b: &str) -> Option<bool> {
        Some(self.ren(a)? == self.ren(b)?)
    }

    /// Fresh slots for a right-hand side, apart from everything the match named.
    pub fn mint(&self, names: &[String]) -> Option<Frame> {
        let mut out = self.clone();
        for name in names {
            if !name.starts_with('$') || out.literals.contains_key(name) {
                return None;
            }
            out.literals.insert(name.clone(), false);
            out.blocks.push(vec![Occ::Lit(name.clone())]);
        }
        out.blocks.sort();
        Some(out)
    }

    /// A slot set with these literals' slots taken out: a built child's slots under a
    /// binder that binds them.
    pub fn without(&self, slots: &Slots, bound: &[String]) -> Option<Slots> {
        let mut out = slots.clone();
        for x in bound {
            out.remove(&self.slot(&Occ::Lit(x.clone()))?);
        }
        Some(out)
    }

    /// The free slots of a node built over these columns: the images of the
    /// uncovered columns, and of the covered ones and binder markers with the bound
    /// literals' slots taken out. As an identity renaming.
    pub fn node_slots(
        &self,
        uncovered: &[String],
        covered: &[String],
        bound: &[String],
    ) -> Option<Slots> {
        let mut slots: BTreeSet<i64> = BTreeSet::new();
        for v in uncovered {
            slots.extend(self.ren(v)?.values().copied());
        }
        let mut inner: BTreeSet<i64> = BTreeSet::new();
        for v in covered {
            inner.extend(self.ren(v)?.values().copied());
        }
        for x in bound {
            inner.remove(&self.slot(&Occ::Lit(x.clone()))?);
        }
        slots.extend(inner);
        Some(slots.into_iter().map(|s| (s, s)).collect())
    }

    /// Whether refinement may merge this block: one a variable or a carried literal
    /// reaches. A redundant node slot or a binder's own slot stays as it is.
    fn carried(&self, block: &[Occ]) -> bool {
        block.iter().any(|o| match o {
            Occ::Var(..) => true,
            Occ::Lit(x) => self.literals.get(x).copied().unwrap_or(false),
            Occ::Node(..) => false,
        })
    }

    /// May these two blocks become one? Not when a clique has a member in each.
    fn mergeable(&self, i: usize, j: usize) -> bool {
        let (a, b) = (&self.blocks[i], &self.blocks[j]);
        !a.iter().any(|o| b.iter().any(|p| apart(o, p)))
    }

    fn merged(&self, i: usize, j: usize) -> Frame {
        let mut out = self.clone();
        let mut b = out.blocks.remove(j.max(i));
        let a = &mut out.blocks[i.min(j)];
        a.append(&mut b);
        a.sort();
        out.blocks.sort();
        out
    }

    /// Every consistent way to merge the blocks refinement may touch, the identity
    /// first, at most `cap` of them. This is the reference's `final_refine`.
    pub fn refinements(&self, cap: usize) -> Vec<Frame> {
        let mut out = vec![self.clone()];
        if self.has_bug("no-refine") {
            return out;
        }
        let mut seen: BTreeSet<Vec<Vec<Occ>>> = BTreeSet::from([self.blocks.clone()]);
        self.walk(cap, &mut seen, &mut out);
        out
    }

    fn walk(&self, cap: usize, seen: &mut BTreeSet<Vec<Vec<Occ>>>, out: &mut Vec<Frame>) {
        if out.len() >= cap {
            return;
        }
        let cands: Vec<usize> = (0..self.blocks.len())
            .filter(|&i| self.carried(&self.blocks[i]))
            .collect();
        for (k, &i) in cands.iter().enumerate() {
            for &j in &cands[k + 1..] {
                if !self.mergeable(i, j) {
                    continue;
                }
                let next = self.merged(i, j);
                if !seen.insert(next.blocks.clone()) {
                    continue;
                }
                out.push(next.clone());
                next.walk(cap, seen, out);
                if out.len() >= cap {
                    return;
                }
            }
        }
    }

    /// The `i`-th refinement, if there is one.
    pub fn refine(&self, i: usize) -> Option<Frame> {
        // a rule asks once per index for the same frame: enumerate once, remember
        thread_local! {
            static MEMO: std::cell::RefCell<HashMap<Frame, std::rc::Rc<Vec<Frame>>>> =
                std::cell::RefCell::new(HashMap::default());
        }
        MEMO.with(|memo| {
            let all = {
                let mut memo = memo.borrow_mut();
                if memo.len() > REFINE_MEMO_CAP {
                    memo.clear();
                }
                memo.entry(self.clone())
                    .or_insert_with(|| std::rc::Rc::new(self.refinements(REFINE_CAP)))
                    .clone()
            };
            all.get(i).cloned()
        })
    }
}

/// How many frames' refinements are remembered before the memo is emptied.
const REFINE_MEMO_CAP: usize = 4096;

/// The CLIQUES: must these two occurrences be different slots? Two slots of one
/// e-node, two slots of one class, or two different literals.
fn apart(o: &Occ, p: &Occ) -> bool {
    match (o, p) {
        (Occ::Node(a, s), Occ::Node(b, t)) => a == b && s != t,
        (Occ::Var(v, s), Occ::Var(w, t)) => v == w && s != t,
        (Occ::Lit(x), Occ::Lit(y)) => x != y,
        _ => false,
    }
}

/// The partition of `occs` generated by `eqs`: each block sorted, the blocks sorted.
fn close(occs: BTreeSet<Occ>, eqs: &[(Occ, Occ)]) -> Vec<Vec<Occ>> {
    let index: BTreeMap<&Occ, usize> = occs.iter().enumerate().map(|(i, o)| (o, i)).collect();
    let mut parent: Vec<usize> = (0..occs.len()).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    for (a, b) in eqs {
        let (ra, rb) = (find(&mut parent, index[a]), find(&mut parent, index[b]));
        if ra != rb {
            parent[ra.max(rb)] = ra.min(rb);
        }
    }
    let mut blocks: BTreeMap<usize, Vec<Occ>> = BTreeMap::new();
    for (o, &i) in &index {
        let r = find(&mut parent, i);
        blocks.entry(r).or_default().push((*o).clone());
    }
    let mut out: Vec<Vec<Occ>> = blocks
        .into_values()
        .map(|mut c| {
            c.sort();
            c
        })
        .collect();
    out.sort();
    out
}

impl fmt::Display for Frame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, block) in self.blocks.iter().enumerate() {
            if i > 0 {
                write!(f, "; ")?;
            }
            write!(f, "{i}:")?;
            for o in block {
                write!(f, " {o}")?;
            }
        }
        write!(f, "}}")
    }
}

fn strings(names: &Names) -> &[String] {
    &names.0
}

#[derive(Debug)]
pub struct FrameSort;

impl BaseSort for FrameSort {
    type Base = Fr;

    fn name(&self) -> &str {
        "Frame"
    }

    #[rustfmt::skip]
    fn register_primitives(&self, eg: &mut EGraph) {
        // a frame with no constraints
        add_primitive!(eg, "frame" = | | -> Fr { Fr::new(Frame::default()) });
        // contract violations an atom commits on purpose, for mutation testing
        add_primitive!(eg, "bugs" = [xs: S] -> Bd { Bd::new(Binding::Bugs(xs.map(|s| s.as_str().to_owned()).collect())) });
        // one atom's constraints: `(atom "label" binding...)`, the label first because the
        // macro's varargs are of one sort
        eg.add_pure_primitive(
            AtomPrim {
                string: eg.type_info.get_sort_by_name("String").expect("String sort").clone(),
                binding: eg.type_info.get_sort_by_name("Binding").expect("Binding sort").clone(),
                frame: eg.type_info.get_sort_by_name("Frame").expect("Frame sort").clone(),
            },
            None,
        );
        // both frames' constraints, closed; fails where a clique breaks
        add_primitive!(eg, "frame-join" = |a: Fr, b: Fr| -?> Fr { a.join(&b).map(Fr::new) });
        // the i-th consistent merging of the slots refinement may touch, 0 the identity
        add_primitive!(eg, "refine" = |f: Fr, i: i64| -?> Fr { usize::try_from(i).ok().and_then(|i| f.refine(i)).map(Fr::new) });
        // conditions, read after refinement
        add_primitive!(eg, "free"     = |f: Fr, lit: S, vs: Ns| -?> () { f.is_free(lit.as_str(), strings(&vs)).filter(|b| *b).map(|_| ()) });
        add_primitive!(eg, "not-free" = |f: Fr, lit: S, vs: Ns| -?> () { f.is_free(lit.as_str(), strings(&vs)).filter(|b| !*b).map(|_| ()) });
        // two variables are the same invocation
        add_primitive!(eg, "same"      = |f: Fr, a: S, b: S| -?> () { f.same(a.as_str(), b.as_str()).filter(|b| *b).map(|_| ()) });
        add_primitive!(eg, "bool-same" = |f: Fr, a: S, b: S| -?> bool { f.same(a.as_str(), b.as_str()) });
        // right-hand-side slots the pattern never pinned
        add_primitive!(eg, "mint" = |f: Fr, xs: Ns| -?> Fr { f.mint(strings(&xs)).map(Fr::new) });
        // the frame spelled in a variable's slot names -- the rule's root, so that its
        // renaming is the identity
        add_primitive!(eg, "anchor" = |f: Fr, v: S| -?> Fr { f.anchored(v.as_str()).map(Fr::new) });
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let frame = base_values.unwrap::<Fr>(value);
        termdag.lit(Literal::String(frame.0.to_string()))
    }
}

/// `(atom "label" binding...)`: one atom's constraints as a frame.
#[derive(Debug, Clone)]
struct AtomPrim {
    string: ArcSort,
    binding: ArcSort,
    frame: ArcSort,
}

impl Primitive for AtomPrim {
    fn name(&self) -> &str {
        "atom"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(AtomTypeConstraint {
            string: self.string.clone(),
            binding: self.binding.clone(),
            frame: self.frame.clone(),
            span: span.clone(),
        })
    }
}

impl PurePrim for AtomPrim {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let bv = state.base_values();
        let (label, rest) = args.split_first()?;
        let label = bv.unwrap::<S>(*label).0;
        let bindings: Vec<Binding> = rest.iter().map(|v| bv.unwrap::<Bd>(*v).0).collect();
        let frame = Frame::atom(&label, &bindings)?;
        Some(bv.get::<Fr>(Fr::new(frame)))
    }
}

struct AtomTypeConstraint {
    string: ArcSort,
    binding: ArcSort,
    frame: ArcSort,
    span: Span,
}

impl TypeConstraint for AtomTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        _typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let too_few = || {
            vec![constraint::impossible(
                constraint::ImpossibleConstraint::ArityMismatch {
                    atom: Atom {
                        span: self.span.clone(),
                        head: "atom".to_owned(),
                        args: arguments.to_vec(),
                    },
                    expected: 2,
                },
            )]
        };
        let Some((out, inputs)) = arguments.split_last() else {
            return too_few();
        };
        let Some((label, bindings)) = inputs.split_first() else {
            return too_few();
        };
        let mut cs: Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> = vec![
            constraint::assign(out.clone(), self.frame.clone()),
            constraint::assign(label.clone(), self.string.clone()),
        ];
        cs.extend(
            bindings
                .iter()
                .map(|b| constraint::assign(b.clone(), self.binding.clone())),
        );
        cs
    }
}

#[derive(Debug)]
pub struct BindingSort;

impl BaseSort for BindingSort {
    type Base = Bd;

    fn name(&self) -> &str {
        "Binding"
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let binding = base_values.unwrap::<Bd>(value);
        termdag.lit(Literal::String(format!("{:?}", binding.0)))
    }
}

#[derive(Debug)]
pub struct NamesSort;

impl BaseSort for NamesSort {
    type Base = Ns;

    fn name(&self) -> &str {
        "Names"
    }

    #[rustfmt::skip]
    fn register_primitives(&self, eg: &mut EGraph) {
        add_primitive!(eg, "names" = [xs: S] -> Ns { Ns::new(Names(xs.map(|s| s.as_str().to_owned()).collect())) });
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let names = base_values.unwrap::<Ns>(value);
        termdag.lit(Literal::String(names.0.0.join(" ")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(pairs: &[(i64, i64)]) -> Slots {
        pairs.iter().copied().collect()
    }

    fn ident(slots: &[i64]) -> Slots {
        slots.iter().map(|&s| (s, s)).collect()
    }

    fn root(v: &str, cs: &[i64]) -> Binding {
        Binding::Root {
            var: v.into(),
            class_slots: ident(cs),
            sym: None,
        }
    }

    fn child(v: &str, edge: &[(i64, i64)], cs: &[i64]) -> Binding {
        Binding::Child {
            var: v.into(),
            edge: m(edge),
            class_slots: ident(cs),
            sym: None,
        }
    }

    fn lit(x: &str, edge: &[(i64, i64)]) -> Binding {
        Binding::Lit {
            name: x.into(),
            edge: m(edge),
            carried: true,
        }
    }

    /// `p = (Sum R $x $y t1)`, `t1 = (Sing e1 e2)` on a node whose slots are 0..4.
    fn sum_sing() -> (Frame, Frame) {
        let sum = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                child("R", &[(0, 0)], &[0]),
                lit("$x", &[(0, 2)]),
                lit("$y", &[(0, 3)]),
                child("t1", &[(0, 1), (1, 2), (2, 3)], &[0, 1, 2]),
            ],
        )
        .unwrap();
        let sing = Frame::atom(
            "t1",
            &[
                root("t1", &[0, 1, 2]),
                child("e1", &[(0, 0)], &[0]),
                child("e2", &[(0, 1), (1, 2)], &[0, 1]),
            ],
        )
        .unwrap();
        (sum, sing)
    }

    #[test]
    fn join_is_commutative_and_identifies_shared_variables() {
        let (sum, sing) = sum_sing();
        let ab = sum.join(&sing).unwrap();
        let ba = sing.join(&sum).unwrap();
        assert_eq!(ab, ba);
        // e1 sits where t1's slot 0 does, which is p's node slot 1
        assert_eq!(
            ab.ren("e1").unwrap(),
            m(&[(0, ab.slot(&Occ::Node("p".into(), 1)).unwrap())])
        );
        // $x is t1's slot 1 seen from p, and e2's slot 0 seen from t1
        assert_eq!(ab.ren("$x").unwrap()[&0], ab.ren("e2").unwrap()[&0]);
        // the literals are apart, and the root's renaming is total on its class
        assert_ne!(ab.ren("$x").unwrap()[&0], ab.ren("$y").unwrap()[&0]);
        assert_eq!(ab.ren("p").unwrap().len(), 2);
    }

    #[test]
    fn a_node_cannot_have_two_of_its_slots_identified() {
        // (F a a) where a's class has one slot: both columns carry a, so the node's
        // two slots would have to be one -- refused
        let f = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                child("a", &[(0, 0)], &[0]),
                child("a", &[(0, 1)], &[0]),
            ],
        );
        assert!(f.is_none());
        // with symmetric edges it is fine: (F a a) matching F(c[0,1], c[1,0]) needs a sym
        let f = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                child("a", &[(0, 0), (1, 1)], &[0, 1]),
                Binding::Child {
                    var: "a".into(),
                    edge: m(&[(0, 1), (1, 0)]),
                    class_slots: ident(&[0, 1]),
                    sym: Some(m(&[(0, 1), (1, 0)])),
                },
            ],
        );
        assert!(f.is_some());
    }

    #[test]
    fn two_literals_never_become_one_slot() {
        let f = Frame::atom(
            "p",
            &[root("p", &[0]), lit("$x", &[(0, 0)]), lit("$y", &[(0, 0)])],
        );
        assert!(f.is_none());
        let g = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                lit("$x", &[(0, 0)]),
                lit("$y", &[(0, 1)]),
            ],
        )
        .unwrap();
        // refinement never merges them either
        assert!(
            g.refinements(REFINE_CAP)
                .iter()
                .all(|r| r.ren("$x") != r.ren("$y"))
        );
    }

    #[test]
    fn refinement_merges_only_what_the_pattern_left_open() {
        // (F a b) with a and b on one-slot classes at different node slots: the two
        // slots are distinct in the node, so no refinement merges them
        let f = Frame::atom(
            "p",
            &[
                root("p", &[0, 1]),
                child("a", &[(0, 0)], &[0]),
                child("b", &[(0, 1)], &[0]),
            ],
        )
        .unwrap();
        assert_eq!(f.refinements(REFINE_CAP).len(), 1);
        // a redundant class slot of `a` that no edge reaches is a placeholder, and a
        // second such placeholder on `b` may be identified with it
        let g = Frame::atom(
            "p",
            &[
                root("p", &[0]),
                child("a", &[(0, 0)], &[0, 5]),
                child("b", &[(0, 0)], &[0, 7]),
            ],
        )
        .unwrap();
        let alts = g.refinements(REFINE_CAP);
        assert_eq!(alts[0], g, "the identity comes first");
        assert!(
            alts.iter()
                .skip(1)
                .any(|r| r.ren("a").unwrap()[&5] == r.ren("b").unwrap()[&7])
        );
        assert!(
            alts.iter()
                .all(|r| r.ren("a").unwrap()[&5] != r.ren("a").unwrap()[&0]),
            "one node's slots stay apart"
        );
    }

    #[test]
    fn atoms_rooted_at_one_variable_are_distinct_nodes() {
        // (Root r) with r = (Add $x b0), r = (Mul a1 b1), r = (Pair a2 b2), r's class
        // slotless: the three nodes' slots are three occurrence spaces, so $x (the Add's
        // slot 0) and a2 (the Pair's slot 0) are placeholders refinement may identify
        let add = Frame::atom(
            "r",
            &[
                root("r", &[]),
                lit("$x", &[(0, 0)]),
                child("b0", &[(0, 1)], &[0]),
            ],
        )
        .unwrap();
        let mul = Frame::atom(
            "r2",
            &[
                root("r", &[]),
                child("a1", &[(0, 0)], &[0]),
                child("b1", &[(0, 1)], &[0]),
            ],
        )
        .unwrap();
        let pair = Frame::atom(
            "r3",
            &[
                root("r", &[]),
                child("a2", &[(0, 0)], &[0]),
                child("b2", &[(0, 1)], &[0]),
            ],
        )
        .unwrap();
        let f = add.join(&mul).unwrap().join(&pair).unwrap();
        assert!(
            f.refinements(REFINE_CAP)
                .iter()
                .any(|r| r.is_free("$x", &["a2".into()]) == Some(true))
        );
    }

    #[test]
    fn conditions_and_mints_read_the_refined_frame() {
        let (sum, sing) = sum_sing();
        let f = sum.join(&sing).unwrap();
        // $x is t1's second slot, which e2 carries: free in e2, not in e1
        assert_eq!(f.is_free("$x", &["e2".into()]), Some(true));
        assert_eq!(f.is_free("$x", &["e1".into()]), Some(false));
        let g = f.mint(&["$z".into()]).unwrap();
        let z = g.ren("$z").unwrap()[&0];
        assert_eq!(g.slot(&Occ::Lit("$z".into())), Some(z));
        // anchored at p, p's renaming is the identity and the mint stays apart from it
        let a = g.anchored("p").unwrap();
        assert!(a.ren("p").unwrap().iter().all(|(k, v)| k == v));
        assert!(
            !a.ren("p")
                .unwrap()
                .values()
                .any(|v| *v == a.ren("$z").unwrap()[&0])
        );
        assert!(
            f.mint(&["$x".into()]).is_none(),
            "a literal the pattern wrote is not fresh"
        );
        // node-slots: a Sing over e1 and a bound $x drops $x's slot from the covered side
        let slots = g
            .node_slots(&["e1".into()], &["$x".into(), "e2".into()], &["$x".into()])
            .unwrap();
        assert!(!slots.contains_key(&g.ren("$x").unwrap()[&0]));
        assert!(slots.contains_key(&g.ren("e1").unwrap()[&0]));
    }
}
