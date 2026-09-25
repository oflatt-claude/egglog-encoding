use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapContainer {
    do_rebuild_keys: bool,
    do_rebuild_vals: bool,
    pub data: BTreeMap<Value, Value>,
}

impl MapContainer {
    /// A renaming: a map whose keys and values are slot names, so its contents
    /// never need rebuilding.
    pub(crate) fn renaming(data: BTreeMap<Value, Value>) -> Self {
        MapContainer {
            do_rebuild_keys: false,
            do_rebuild_vals: false,
            data,
        }
    }

    /// Whether this map's keys or values are e-classes, and so are rebuilt when
    /// the e-graph merges classes.
    pub(crate) fn rebuilds_contents(&self) -> bool {
        self.do_rebuild_keys || self.do_rebuild_vals
    }
}

/// A renaming's entries as slot numbers, which is what the solvers in this file
/// work on.
pub(crate) fn slot_map(bv: &BaseValues, m: &BTreeMap<Value, Value>) -> BTreeMap<i64, i64> {
    m.iter()
        .map(|(k, v)| (bv.unwrap::<i64>(*k), bv.unwrap::<i64>(*v)))
        .collect()
}

/// A solver's answer back as a renaming's entries.
pub(crate) fn value_map(bv: &BaseValues, m: BTreeMap<i64, i64>) -> BTreeMap<Value, Value> {
    m.into_iter()
        .map(|(k, v)| (bv.get::<i64>(k), bv.get::<i64>(v)))
        .collect()
}

/// The renamings a sequence of values names, as slot maps; `None` if one of them
/// is not a map.
pub(crate) fn slot_maps(
    state: &PureState<'_, '_>,
    values: impl IntoIterator<Item = Value>,
) -> Option<Vec<BTreeMap<i64, i64>>> {
    let (bv, cv) = (state.base_values(), state.container_values());
    values
        .into_iter()
        .map(|v| Some(slot_map(bv, &cv.get_val::<MapContainer>(v)?.data)))
        .collect()
}

/// The canonical spelling of a node's edges: its slots renumbered `0, 1, 2…` in order
/// of first occurrence, scanning the edges in order and each edge by child slot. Returns
/// the renumbered edges followed by the renaming from those numbers back to the node's
/// own names. Two nodes are equal up to a renaming of their slots exactly when their
/// shapes agree.
pub(crate) fn shape(edges: &[BTreeMap<i64, i64>]) -> Vec<BTreeMap<i64, i64>> {
    let mut number: BTreeMap<i64, i64> = BTreeMap::new();
    let mut out: Vec<BTreeMap<i64, i64>> = Vec::with_capacity(edges.len() + 1);
    for edge in edges {
        let mut spelled = BTreeMap::new();
        for (&child_slot, &node_slot) in edge {
            let next = number.len() as i64;
            spelled.insert(child_slot, *number.entry(node_slot).or_insert(next));
        }
        out.push(spelled);
    }
    out.push(number.into_iter().map(|(slot, n)| (n, slot)).collect());
    out
}

/// A node's canonical spelling and the symmetries it gives its class, from one walk of
/// the readings its children's symmetries allow.
///
/// Returns the canonical edges, then the renaming from that spelling back to the node's
/// own names, then one renaming per symmetry. A reading composes each column's edge
/// with a symmetry of that column's class; only a renaming that permutes the column's
/// own slots is one, so a stale symmetry is ignored. The least reading is the spelling
/// every reading agrees on, so two nodes equal up to their children's symmetries have
/// equal canonical edges. A reading that spells the node the way it already spells
/// itself says the class equals itself under the renaming between them, which is the
/// reference's `weak_shape` over `get_group_compatible_variants` and its
/// `determine_self_symmetries` in one pass.
pub(crate) fn node_shape(
    edges: &[BTreeMap<i64, i64>],
    groups: &[Vec<BTreeMap<i64, i64>>],
) -> Vec<BTreeMap<i64, i64>> {
    let own = shape(edges);
    let (own_canonical, own_back) = own.split_at(edges.len());
    let mut best: Option<Vec<BTreeMap<i64, i64>>> = None;
    let mut symmetries: Vec<BTreeMap<i64, i64>> = Vec::new();
    for variant in readings(edges, groups) {
        let spelled = shape(&variant);
        if spelled[..edges.len()] == *own_canonical {
            // variant = b . canonical and the node = own_back . canonical, so
            // b . own_back^-1 renames the node's slots onto themselves
            let symmetry: BTreeMap<i64, i64> = own_back[0]
                .iter()
                .filter_map(|(n, &slot)| spelled[edges.len()].get(n).map(|&image| (slot, image)))
                .collect();
            if symmetry.iter().any(|(from, to)| from != to) {
                symmetries.push(symmetry);
            }
        }
        if best
            .as_ref()
            .is_none_or(|b| spelled[..edges.len()] < b[..edges.len()])
        {
            best = Some(spelled);
        }
    }
    symmetries.sort();
    symmetries.dedup();
    let mut out = best.unwrap_or(own);
    out.append(&mut symmetries);
    out
}

/// Each column's edge, and the edge through every symmetry of its child's class: the
/// readings of a node that spell the same invocation. A renaming that does not permute
/// the column's own slots is not one of them, so a stale symmetry is ignored.
fn readings(
    edges: &[BTreeMap<i64, i64>],
    groups: &[Vec<BTreeMap<i64, i64>>],
) -> impl Iterator<Item = Vec<BTreeMap<i64, i64>>> {
    let columns: Vec<Vec<BTreeMap<i64, i64>>> = edges
        .iter()
        .enumerate()
        .map(|(i, edge)| {
            let domain: BTreeSet<i64> = edge.keys().copied().collect();
            let mut out = vec![edge.clone()];
            for g in groups.get(i).map(Vec::as_slice).unwrap_or_default() {
                if g.keys().copied().collect::<BTreeSet<_>>() == domain
                    && g.values().copied().collect::<BTreeSet<_>>() == domain
                {
                    out.push(g.iter().map(|(&s, &t)| (s, edge[&t])).collect());
                }
            }
            out.sort();
            out.dedup();
            out
        })
        .collect();
    let total: usize = columns.iter().map(Vec::len).product();
    (0..total).map(move |mut n| {
        let mut variant = Vec::with_capacity(columns.len());
        for column in &columns {
            variant.push(column[n % column.len()].clone());
            n /= column.len();
        }
        variant
    })
}

/// A solver's slot maps registered as renamings, in order, for a vector of them.
pub(crate) fn register_renamings(
    state: &mut PureState<'_, '_>,
    maps: impl IntoIterator<Item = BTreeMap<i64, i64>>,
) -> Vec<Value> {
    let bv = state.base_values();
    let renamings: Vec<BTreeMap<Value, Value>> =
        maps.into_iter().map(|m| value_map(bv, m)).collect();
    renamings
        .into_iter()
        .map(|n| state.register_container::<MapContainer>(MapContainer::renaming(n)))
        .collect()
}

impl ContainerValue for MapContainer {
    fn rebuild_contents(&mut self, rebuilder: &dyn ValueRebuilder) -> bool {
        let mut changed = false;
        if self.do_rebuild_keys {
            self.data = self
                .data
                .iter()
                .map(|(old, v)| {
                    let new = rebuilder.rebuild_val(*old);
                    changed |= *old != new;
                    (new, *v)
                })
                .collect();
        }
        if self.do_rebuild_vals {
            for old in self.data.values_mut() {
                let new = rebuilder.rebuild_val(*old);
                changed |= *old != new;
                *old = new;
            }
        }
        changed
    }
    fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        self.data.iter().flat_map(|(k, v)| [k, v]).copied()
    }
}

/// The entries of a flat `(map-of k0 v0 ...)` term as a Rust `BTreeMap` in
/// canonical key order, with `MapContainer`'s last-write-wins semantics on
/// duplicate keys; `None` for any other term.
fn map_term_to_btreemap<'a>(
    termdag: &'a TermDag,
    term_id: TermId,
) -> Option<BTreeMap<OrdTerm<'a>, TermId>> {
    match termdag.get(term_id) {
        Term::App(head, args) if head == "map-of" => map_of_args_to_btreemap(termdag, args),
        _ => None,
    }
}

/// Alternating `[k0, v0, ...]` `map-of` arguments as a `BTreeMap` (see
/// [`map_term_to_btreemap`]); `None` on odd arity.
fn map_of_args_to_btreemap<'a>(
    termdag: &'a TermDag,
    args: &[TermId],
) -> Option<BTreeMap<OrdTerm<'a>, TermId>> {
    if !args.len().is_multiple_of(2) {
        return None;
    }
    Some(
        args.chunks_exact(2)
            .map(|kv| (termdag.ord_term(kv[0]), kv[1]))
            .collect(),
    )
}

/// Flatten a map back to the `[k0, v0, k1, v1, ...]` argument list of its
/// canonical `(map-of ...)` term (sorted by key order, deduplicated).
fn map_term_args(map: BTreeMap<OrdTerm<'_>, TermId>) -> Vec<TermId> {
    map.into_iter().flat_map(|(k, v)| [k.id(), v]).collect()
}

/// Canonicalize alternating `[k0, v0, ...]` arguments to the flat
/// `(map-of ...)` term; `None` on odd arity.
fn normalize_map_term(termdag: &mut TermDag, args: &[TermId]) -> Option<TermId> {
    let flat = map_term_args(map_of_args_to_btreemap(termdag, args)?);
    Some(termdag.app("map-of".to_string(), flat))
}

/// `a ∘ b`, the map sending `x` to `a[b[x]]`: `b` applies first. Undefined
/// wherever either step is, so the result is keyed on
/// `{x ∈ dom(b) | b[x] ∈ dom(a)}`.
pub(crate) fn compose(
    a: &BTreeMap<Value, Value>,
    b: &BTreeMap<Value, Value>,
) -> BTreeMap<Value, Value> {
    b.iter()
        .filter_map(|(x, y)| a.get(y).map(|z| (*x, *z)))
        .collect()
}

/// `a ∘ b` where every key of `b` must survive; `None` if any is lost.
///
/// [`compose`] narrows silently when `b`'s image escapes `a`'s domain,
/// which is correct for composing partial maps but wrong wherever the result
/// becomes an *edge* of an e-node: an edge's domain must be its child's slot set,
/// so a narrowed edge misstates which slots the child has. Use this there, and
/// the rule declines instead of asserting something false.
fn compose_total(
    a: &BTreeMap<Value, Value>,
    b: &BTreeMap<Value, Value>,
) -> Option<BTreeMap<Value, Value>> {
    let out = compose(a, b);
    (out.len() == b.len()).then_some(out)
}

/// The inverse map; `None` unless the input is injective.
///
/// A renaming is a partial injection, so the inverse of a non-injective map is
/// not meaningful. Rejecting it turns a silently wrong answer into a rule that
/// does not fire.
fn inverse(m: &BTreeMap<Value, Value>) -> Option<BTreeMap<Value, Value>> {
    let out: BTreeMap<Value, Value> = m.iter().map(|(k, v)| (*v, *k)).collect();
    (out.len() == m.len()).then_some(out)
}

/// The identity map on `im(m)`.
///
/// A set of slots is represented as an identity renaming, so this is how to name
/// "the slots `m` maps onto" — the long way round being `(compose m (inverse m))`.
fn map_image(m: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    m.values().map(|v| (*v, *v)).collect()
}

/// The identity map on `dom(m)`; the counterpart of [`map_image`], spelled
/// the long way round as `(compose (inverse m) m)`.
fn map_domain(m: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    m.keys().map(|k| (*k, *k)).collect()
}

/// The entries two maps agree on.
///
/// A slot set is an identity renaming, so this is how one narrows: intersecting two
/// identity maps gives the identity on the intersection of their domains.
fn map_intersect(a: &BTreeMap<Value, Value>, b: &BTreeMap<Value, Value>) -> BTreeMap<Value, Value> {
    a.iter()
        .filter(|(k, v)| b.get(k) == Some(v))
        .map(|(k, v)| (*k, *v))
        .collect()
}

/// Union of partial maps; `None` if they disagree on a shared key.
fn map_union(
    a: &BTreeMap<Value, Value>,
    b: &BTreeMap<Value, Value>,
) -> Option<BTreeMap<Value, Value>> {
    let mut out = a.clone();
    for (k, v) in b {
        if out.insert(*k, *v).is_some_and(|old| old != *v) {
            return None;
        }
    }
    Some(out)
}

/// The least renaming `R` with `R ∘ second[i] = first[i]` for every `i`, given
/// the two halves flat as `[first..., second...]`.
///
/// Renamings are explicit partial maps, so a paired `(first[i], second[i])`
/// must carry exactly the same key set: a missing key means "no mapping", not
/// "identity". Each shared key `k` contributes `R(second[i][k]) = first[i][k]`.
///
/// `None` when the halves are unequal in length, when a pair's key sets
/// differ, or when the constraints make `R` non-functional or non-injective.
fn find_mapping<T: Copy + Ord>(maps: &[BTreeMap<T, T>]) -> Option<BTreeMap<T, T>> {
    if !maps.len().is_multiple_of(2) {
        return None;
    }
    let (first, second) = maps.split_at(maps.len() / 2);

    let mut mapping = BTreeMap::new();
    let mut inverse = BTreeMap::new();
    for (m1, m2) in first.iter().zip(second) {
        if m1.len() != m2.len() || !m1.keys().eq(m2.keys()) {
            return None;
        }
        for ((_, v1), (_, v2)) in m1.iter().zip(m2) {
            if mapping.insert(*v2, *v1).is_some_and(|prev| prev != *v1) {
                return None;
            }
            if inverse.insert(*v1, *v2).is_some_and(|prev| prev != *v2) {
                return None;
            }
        }
    }
    Some(mapping)
}

/// [`find_mapping`] extended to be *total* on a domain, minting a
/// fresh slot for every domain key the constraints leave unnamed.
///
/// Arguments come flat as `[avoid, domain, first..., second...]`. The
/// constraint part is solved exactly as in [`find_mapping`]; each
/// remaining key of `domain` is then named with the *smallest* non-negative
/// value not already spoken for, which keeps the result injective and disjoint
/// from `avoid`.
///
/// `None` on the same conditions as [`find_mapping`], or on fewer than
/// two leading maps.
fn find_mapping_total(maps: &[BTreeMap<i64, i64>]) -> Option<BTreeMap<i64, i64>> {
    let (head, pairs) = maps.split_at_checked(2)?;
    let (avoid, domain) = (&head[0], &head[1]);

    let mut mapping = find_mapping(pairs)?;

    let mut used: BTreeSet<i64> = mapping
        .values()
        .chain(avoid.keys())
        .chain(avoid.values())
        .copied()
        .collect();

    let mut next = 0;
    for k in domain.keys() {
        if mapping.contains_key(k) {
            continue;
        }
        while used.contains(&next) {
            next += 1;
        }
        used.insert(next);
        mapping.insert(*k, next);
    }
    Some(mapping)
}

pub(crate) const FIND_MAPPINGS_CAP: usize = 1024;

/// How many namings [`find_mappings_total`] would produce for `unnamed`
/// domain keys and `avail` reusable slots, without building any of them.
pub(crate) fn naming_count(unnamed: usize, avail: usize) -> u128 {
    // One key at a time: it either takes a fresh name, leaving the candidates
    // untouched, or one of the `avail` slots, leaving one fewer for the keys after it.
    match unnamed {
        0 => 1,
        u => naming_count(u - 1, avail).saturating_add(
            (avail as u128).saturating_mul(naming_count(u - 1, avail.saturating_sub(1))),
        ),
    }
}

/// What a naming chooses between: the mapping the constraints force, the domain
/// keys they leave unnamed, the slots those keys may reuse, and every slot already
/// spoken for.
///
/// Shared so the count and the enumeration cannot drift apart; a count that
/// disagreed with what was built would be worse than no count at all.
fn naming_parts(
    maps: &[BTreeMap<i64, i64>],
) -> Option<(BTreeMap<i64, i64>, Vec<i64>, Vec<i64>, BTreeSet<i64>)> {
    let (head, pairs) = maps.split_at_checked(2)?;
    let (avoid, domain) = (&head[0], &head[1]);
    let solved = find_mapping(pairs)?;

    let unnamed: Vec<i64> = domain
        .keys()
        .filter(|k| !solved.contains_key(k))
        .copied()
        .collect();
    let spoken_for: BTreeSet<i64> = solved
        .values()
        .chain(avoid.keys())
        .chain(avoid.values())
        .copied()
        .collect();
    // Reusing a slot this mapping already assigned would break injectivity, so the
    // candidates are the slots spoken for elsewhere.
    let candidates: Vec<i64> = spoken_for
        .iter()
        .filter(|s| !solved.values().any(|v| v == *s))
        .copied()
        .collect();
    Some((solved, unnamed, candidates, spoken_for))
}

/// How many namings [`find_mappings_total`] has to choose from, ignoring
/// its cap. Compare against the vector's length to see whether the cap truncated.
///
/// `None` on the same conditions as [`find_mapping`].
pub(crate) fn find_mappings_total_count(maps: &[BTreeMap<i64, i64>]) -> Option<u128> {
    let (_, unnamed, candidates, _) = naming_parts(maps)?;
    Some(naming_count(unnamed.len(), candidates.len()))
}

/// [`find_mapping_total`] with every naming it could have chosen, not
/// only the minting one.
///
/// Minting decides that an unnamed domain key is DIFFERENT from every slot
/// already spoken for, since a fresh name differs from everything. That is one
/// branch of a choice, and the other -- the key naming a slot the pattern
/// already used -- is a match the minting solution cannot express. Each unnamed
/// key may therefore take a fresh name, or any slot in `avoid` this mapping has
/// not already used; results stay injective, as a renaming must be.
///
/// Element 0 is the minting solution, so reading index 0 is exactly
/// [`find_mapping_total`]. The order of the rest is deterministic: an
/// index is only meaningful if it names the same mapping every run.
///
/// Empty when the constraints are unsatisfiable. At most `cap` elements are
/// built; compare against [`find_mappings_total_count`] to detect that a
/// caller's index space is too small to reach them all.
pub(crate) fn find_mappings_total(
    maps: &[BTreeMap<i64, i64>],
    cap: usize,
) -> Vec<BTreeMap<i64, i64>> {
    let Some((solved, unnamed, candidates, spoken_for)) = naming_parts(maps) else {
        return Vec::new();
    };

    let mut out = Vec::new();
    let mut mapping = solved;
    let mut used = spoken_for;
    // Depth-first over the keys in order, taking the fresh name first at every
    // level, which puts the all-minting solution at index 0.
    fn walk(
        keys: &[i64],
        candidates: &[i64],
        mapping: &mut BTreeMap<i64, i64>,
        used: &mut BTreeSet<i64>,
        cap: usize,
        out: &mut Vec<BTreeMap<i64, i64>>,
    ) {
        if out.len() >= cap {
            return;
        }
        let Some((&k, rest)) = keys.split_first() else {
            out.push(mapping.clone());
            return;
        };
        let mut fresh = 0;
        while used.contains(&fresh) {
            fresh += 1;
        }
        // `fresh` is the smallest slot not spoken for, so it is never a candidate and
        // the choices cannot repeat. Injectivity is the only thing left to check.
        for choice in std::iter::once(fresh).chain(candidates.iter().copied()) {
            if mapping.values().any(|v| *v == choice) {
                continue;
            }
            let added = used.insert(choice);
            mapping.insert(k, choice);
            walk(rest, candidates, mapping, used, cap, out);
            mapping.remove(&k);
            if added {
                used.remove(&choice);
            }
            if out.len() >= cap {
                return;
            }
        }
    }
    walk(
        &unnamed,
        &candidates,
        &mut mapping,
        &mut used,
        cap,
        &mut out,
    );
    out
}

#[derive(Clone, Debug)]
pub struct MapSort {
    name: String,
    key: ArcSort,
    value: ArcSort,
}

impl MapSort {
    pub fn key(&self) -> ArcSort {
        self.key.clone()
    }

    pub fn value(&self) -> ArcSort {
        self.value.clone()
    }
}

impl Presort for MapSort {
    fn presort_name() -> &'static str {
        "Map"
    }

    fn reserved_primitives() -> Vec<&'static str> {
        vec![
            "map-empty",
            "map-of",
            "map-insert",
            "map-get",
            "map-not-contains",
            "map-contains",
            "map-remove",
            "map-length",
        ]
    }

    fn make_sort(
        typeinfo: &mut TypeInfo,
        name: String,
        args: &[Expr],
    ) -> Result<ArcSort, TypeError> {
        if let [Expr::Var(k_span, k), Expr::Var(v_span, v)] = args {
            let k = typeinfo
                .get_sort_by_name(k)
                .ok_or(TypeError::UndefinedSort(k.clone(), k_span.clone()))?;
            let v = typeinfo
                .get_sort_by_name(v)
                .ok_or(TypeError::UndefinedSort(v.clone(), v_span.clone()))?;

            let out = Self {
                name,
                key: k.clone(),
                value: v.clone(),
            };
            Ok(out.to_arcsort())
        } else {
            panic!()
        }
    }
}

impl ContainerSort for MapSort {
    type Container = MapContainer;

    fn name(&self) -> &str {
        &self.name
    }

    fn inner_sorts(&self) -> Vec<ArcSort> {
        vec![self.key.clone(), self.value.clone()]
    }

    fn is_eq_container_sort(&self) -> bool {
        self.key.is_eq_sort()
            || self.value.is_eq_sort()
            || self.key.is_eq_container_sort()
            || self.value.is_eq_container_sort()
    }

    fn inner_values(
        &self,
        container_values: &ContainerValues,
        value: Value,
    ) -> Vec<(ArcSort, Value)> {
        let val = container_values
            .get_val::<MapContainer>(value)
            .unwrap()
            .clone();
        val.data
            .iter()
            .flat_map(|(k, v)| [(self.key.clone(), *k), (self.value.clone(), *v)])
            .collect()
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        let arc = self.clone().to_arcsort();

        // The proof "term form" of a map is the flat `(map-of k0 v0 k1 v1 ...)`
        // in canonical key order (like `set-of`/`vec-of`), matching
        // `reconstruct_termdag`. Each validator round-trips through a Rust
        // `BTreeMap` (see `map_term_to_btreemap`), so it evaluates map terms
        // with `MapContainer`'s semantics; `None` for a malformed map term
        // fails the proof.
        let map_empty_validator = |termdag: &mut TermDag, _args: &[TermId]| -> Option<TermId> {
            Some(termdag.app("map-of".into(), vec![]))
        };
        let map_insert_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [map, key, value] = args else {
                return None;
            };
            let mut map = map_term_to_btreemap(termdag, *map)?;
            map.insert(termdag.ord_term(*key), *value);
            let flat = map_term_args(map);
            Some(termdag.app("map-of".into(), flat))
        };
        let map_get_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [map, key] = args else { return None };
            map_term_to_btreemap(termdag, *map)?
                .get(&termdag.ord_term(*key))
                .copied()
        };
        let map_length_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [map] = args else { return None };
            let len = map_term_to_btreemap(termdag, *map)?.len() as i64;
            Some(termdag.lit(Literal::Int(len)))
        };
        let map_contains_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [map, key] = args else { return None };
            let contains =
                map_term_to_btreemap(termdag, *map)?.contains_key(&termdag.ord_term(*key));
            contains.then(|| termdag.lit(Literal::Unit))
        };
        let map_not_contains_validator =
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                let [map, key] = args else { return None };
                let contains =
                    map_term_to_btreemap(termdag, *map)?.contains_key(&termdag.ord_term(*key));
                (!contains).then(|| termdag.lit(Literal::Unit))
            };

        add_primitive_with_validator!(eg, "map-empty" = {self.clone(): MapSort} || -> @MapContainer (arc) { MapContainer {
            do_rebuild_keys: self.ctx.key.is_eq_sort() || self.ctx.key.is_eq_container_sort(),
            do_rebuild_vals: self.ctx.value.is_eq_sort() || self.ctx.value.is_eq_container_sort(),
            data: BTreeMap::new()
        } }, map_empty_validator);

        // `map-of` is the flat constructor used as the canonical term form. It
        // takes alternating key/value arguments, so it needs a custom type
        // constraint rather than the `add_primitive!` macro.
        eg.add_pure_primitive(
            MapOf {
                name: "map-of".to_string(),
                map: arc.clone(),
                key: self.key.clone(),
                value: self.value.clone(),
            },
            Some(std::sync::Arc::new(normalize_map_term)),
        );

        add_primitive_with_validator!(eg, "map-get"    = |    xs: @MapContainer (arc), x: # (self.key())                     | -?> # (self.value()) { xs.data.get(&x).copied() }, map_get_validator);
        add_primitive_with_validator!(eg, "map-insert" = |mut xs: @MapContainer (arc), x: # (self.key()), y: # (self.value())| -> @MapContainer (arc) {{ xs.data.insert(x, y); xs }}, map_insert_validator);
        add_primitive!(eg, "map-remove" = |mut xs: @MapContainer (arc), x: # (self.key())                     | -> @MapContainer (arc) {{ xs.data.remove(&x);   xs }});

        add_primitive_with_validator!(eg, "map-length"       = |xs: @MapContainer (arc)| -> i64 { xs.data.len() as i64 }, map_length_validator);
        add_primitive_with_validator!(eg, "map-contains"     = |xs: @MapContainer (arc), x: # (self.key())| -?> () { ( xs.data.contains_key(&x)).then_some(()) }, map_contains_validator);
        add_primitive_with_validator!(eg, "map-not-contains" = |xs: @MapContainer (arc), x: # (self.key())| -?> () { (!xs.data.contains_key(&x)).then_some(()) }, map_not_contains_validator);

        add_primitive!(eg, "map-union" = |xs: @MapContainer (arc), ys: @MapContainer (arc)| -?> @MapContainer (arc) { Some(MapContainer { data: map_union(&xs.data, &ys.data)?, ..xs }) });
        add_primitive!(eg, "map-intersect" = |xs: @MapContainer (arc), ys: @MapContainer (arc)| -> @MapContainer (arc) { MapContainer { data: map_intersect(&xs.data, &ys.data), ..xs } });

        // `map-contains` is a fact, so it cannot be combined with `or`/`and`; this
        // is the same test as a value, for use inside a `guard`.
        add_primitive!(eg, "bool-map-contains" = |xs: @MapContainer (arc), x: # (self.key())| -> bool { xs.data.contains_key(&x) });

        // With matching key and value sorts a map is a partial injection on one
        // space — a renaming, in the slotted-e-graph sense — so it composes and
        // inverts. `find-mapping` solves for the renaming carrying one tuple of
        // edges onto another; it is variadic, taking the two tuples flat.
        if self.key.name() == self.value.name() {
            add_primitive!(eg, "compose" = |a: @MapContainer (arc), b: @MapContainer (arc)| -> @MapContainer (arc) { MapContainer { data: compose(&a.data, &b.data), ..b } });
            add_primitive!(eg, "compose-total" = |a: @MapContainer (arc), b: @MapContainer (arc)| -?> @MapContainer (arc) { Some(MapContainer { data: compose_total(&a.data, &b.data)?, ..b }) });
            add_primitive!(eg, "inverse"     = |a: @MapContainer (arc)| -?> @MapContainer (arc) { Some(MapContainer { data: inverse(&a.data)?, ..a }) });
            add_primitive!(eg, "map-inverse" = |a: @MapContainer (arc)| -?> @MapContainer (arc) { Some(MapContainer { data: inverse(&a.data)?, ..a }) });
            add_primitive!(eg, "map-image"   = |a: @MapContainer (arc)| -> @MapContainer (arc) { MapContainer { data: map_image(&a.data), ..a } });
            add_primitive!(eg, "map-domain"  = |a: @MapContainer (arc)| -> @MapContainer (arc) { MapContainer { data: map_domain(&a.data), ..a } });
            add_primitive!(eg, "find-mapping" = {self.clone(): MapSort} [xs: @MapContainer (arc)] -?> @MapContainer (arc) {{
                let maps: Vec<BTreeMap<Value, Value>> = xs.map(|m| m.data).collect();
                Some(MapContainer {
                    do_rebuild_keys: self.ctx.key.is_eq_sort() || self.ctx.key.is_eq_container_sort(),
                    do_rebuild_vals: self.ctx.value.is_eq_sort() || self.ctx.value.is_eq_container_sort(),
                    data: find_mapping(&maps)?,
                })
            }});

            // Minting a fresh slot means naming one that is not in use, which
            // needs the slot space to be ordered and unbounded above.
            if self.key.name() == "i64" {
                // Slotted matching frames (`sort/frame.rs`) read renamings off matched
                // e-nodes and hand renamings back: the bindings an `atom` is made of,
                // a variable's renaming out of a frame, and a built node's slot set.
                add_primitive!(eg, "root" = |v: S, cs: @MapContainer (arc)| -> Bd {
                    Bd::new(Binding::Root { var: v.as_str().to_owned(), class_slots: slot_map(state.base_values(), &cs.data), sym: None })
                });
                add_primitive!(eg, "root" = |v: S, cs: @MapContainer (arc), sym: @MapContainer (arc)| -> Bd {{
                    let bv = state.base_values();
                    Bd::new(Binding::Root { var: v.as_str().to_owned(), class_slots: slot_map(bv, &cs.data), sym: Some(slot_map(bv, &sym.data)) })
                }});
                add_primitive!(eg, "child" = |v: S, e: @MapContainer (arc), cs: @MapContainer (arc)| -> Bd {{
                    let bv = state.base_values();
                    Bd::new(Binding::Child { var: v.as_str().to_owned(), edge: slot_map(bv, &e.data), class_slots: slot_map(bv, &cs.data), sym: None })
                }});
                add_primitive!(eg, "child" = |v: S, e: @MapContainer (arc), cs: @MapContainer (arc), sym: @MapContainer (arc)| -> Bd {{
                    let bv = state.base_values();
                    Bd::new(Binding::Child { var: v.as_str().to_owned(), edge: slot_map(bv, &e.data), class_slots: slot_map(bv, &cs.data), sym: Some(slot_map(bv, &sym.data)) })
                }});
                add_primitive!(eg, "lit" = |x: S, e: @MapContainer (arc)| -> Bd {
                    Bd::new(Binding::Lit { name: x.as_str().to_owned(), edge: slot_map(state.base_values(), &e.data), carried: true })
                });
                add_primitive!(eg, "bound" = |x: S, e: @MapContainer (arc)| -> Bd {
                    Bd::new(Binding::Lit { name: x.as_str().to_owned(), edge: slot_map(state.base_values(), &e.data), carried: false })
                });
                add_primitive!(eg, "leaf" = |e: @MapContainer (arc)| -> Bd {
                    Bd::new(Binding::Leaf { edge: slot_map(state.base_values(), &e.data) })
                });
                add_primitive!(eg, "ren" = |f: Fr, name: S| -?> @MapContainer (arc) {
                    Some(MapContainer::renaming(value_map(state.base_values(), f.ren(name.as_str())?)))
                });
                add_primitive!(eg, "without" = |f: Fr, slots: @MapContainer (arc), bound: Ns| -?> @MapContainer (arc) {{
                    let bv = state.base_values();
                    Some(MapContainer::renaming(value_map(bv, f.without(&slot_map(bv, &slots.data), &bound.0 .0)?)))
                }});
                add_primitive!(eg, "node-slots" = |f: Fr, uncovered: Ns, covered: Ns, bound: Ns| -?> @MapContainer (arc) {
                    Some(MapContainer::renaming(value_map(state.base_values(), f.node_slots(&uncovered.0 .0, &covered.0 .0, &bound.0 .0)?)))
                });
                add_primitive!(eg, "find-mapping-total" = {self.clone(): MapSort} [xs: @MapContainer (arc)] -?> @MapContainer (arc) {{
                    let bv = state.base_values();
                    let maps: Vec<BTreeMap<i64, i64>> = xs.map(|m| slot_map(bv, &m.data)).collect();
                    Some(MapContainer::renaming(value_map(bv, find_mapping_total(&maps)?)))
                }});

                // How many namings `find-mappings-total` chooses between, before its
                // cap. A rule comparing this against `vec-length` sees that the cap
                // truncated, which silently losing namings would not show.
                add_primitive!(eg, "find-mappings-total-count" = {self.clone(): MapSort} [xs: @MapContainer (arc)] -?> i64 {{
                    let bv = state.base_values();
                    let maps: Vec<BTreeMap<i64, i64>> = xs.map(|m| slot_map(bv, &m.data)).collect();
                    find_mappings_total_count(&maps).map(|n| n.min(i64::MAX as u128) as i64)
                }});

                // Substitution needs both a read (to extract a term) and a
                // write (to add the substituted one), so it is registered as a
                // `FullPrim`: see `crate::sort::slotted_subst`. Its result is an
                // invocation, so it takes two names to read one -- the class and
                // the renaming placing it in `body`'s frame.
                for half in [
                    crate::sort::slotted_subst::Half::Class,
                    crate::sort::slotted_subst::Half::Frame,
                ] {
                    eg.add_full_primitive(
                        crate::sort::slotted_subst::SlottedSubst {
                            half,
                            renaming: arc.clone(),
                            slot: self.key.clone(),
                        },
                        None,
                    );
                }
            }
        }
    }

    fn reconstruct_termdag(
        &self,
        _container_values: &ContainerValues,
        _value: Value,
        termdag: &mut TermDag,
        element_terms: Vec<TermId>,
    ) -> TermId {
        // Flat `(map-of k0 v0 k1 v1 ...)` in canonical key order, so proof
        // checking can reproduce it from terms alone (and the rebuild proof's
        // Congr indices are flat, like `set-of`/`vec-of`).
        normalize_map_term(termdag, &element_terms).expect("map elements come in key/value pairs")
    }

    fn rebuild_container_normalizer(&self) -> Option<(String, PrimitiveValidator)> {
        Some(("map-of".to_owned(), Arc::new(normalize_map_term)))
    }

    fn serialized_name(&self, _container_values: &ContainerValues, _: Value) -> String {
        "map-of".to_owned()
    }
}

/// The flat `map-of` constructor: takes alternating key/value arguments and
/// builds a map. Used as the canonical term form for maps (analogous to
/// `set-of`/`vec-of`). Needs a custom type constraint because its arguments
/// alternate between the key and value sorts.
#[derive(Clone)]
struct MapOf {
    name: String,
    map: ArcSort,
    key: ArcSort,
    value: ArcSort,
}

impl Primitive for MapOf {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(MapOfTypeConstraint {
            name: self.name.clone(),
            key: self.key.clone(),
            value: self.value.clone(),
            map: self.map.clone(),
            span: span.clone(),
        })
    }
}

impl PurePrim for MapOf {
    fn apply<'a, 'db>(&self, mut state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let mut data = BTreeMap::new();
        for chunk in args.chunks(2) {
            if let [k, v] = chunk {
                data.insert(*k, *v);
            }
        }
        let mc = MapContainer {
            do_rebuild_keys: self.key.is_eq_sort() || self.key.is_eq_container_sort(),
            do_rebuild_vals: self.value.is_eq_sort() || self.value.is_eq_container_sort(),
            data,
        };
        Some(state.register_container(mc))
    }
}

/// Type constraint for [`MapOf`]: an even number of inputs alternating between
/// the key and value sorts, producing the map sort.
struct MapOfTypeConstraint {
    name: String,
    key: ArcSort,
    value: ArcSort,
    map: ArcSort,
    span: Span,
}

impl TypeConstraint for MapOfTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        _typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let arity_mismatch = |expected: usize| {
            vec![constraint::impossible(
                constraint::ImpossibleConstraint::ArityMismatch {
                    atom: Atom {
                        span: self.span.clone(),
                        head: self.name.clone(),
                        args: arguments.to_vec(),
                    },
                    expected,
                },
            )]
        };
        let Some((out, inputs)) = arguments.split_last() else {
            return arity_mismatch(1);
        };
        if inputs.len() % 2 != 0 {
            return arity_mismatch(inputs.len() + 2);
        }
        let mut cs: Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> =
            vec![constraint::assign(out.clone(), self.map.clone())];
        for (i, arg) in inputs.iter().enumerate() {
            let sort = if i % 2 == 0 {
                self.key.clone()
            } else {
                self.value.clone()
            };
            cs.push(constraint::assign(arg.clone(), sort));
        }
        cs
    }
}

#[cfg(test)]
mod naming_tests {
    use super::*;

    fn m(pairs: &[(i64, i64)]) -> BTreeMap<i64, i64> {
        pairs.iter().copied().collect()
    }

    /// Reading index 0 must mean "did not refine", so that an index space too small to
    /// reach the rest degrades to today's behaviour rather than to an arbitrary merge.
    /// `allows_directed_union`: the slot being replaced may not be one the pattern
    /// writes, so two pattern slots have no direction available and never merge.
    /// A node's slots are pairwise distinct, so a group forbids merging within it --
    /// which is what keeps a merge map composable with a renaming without collapsing
    /// two of its keys.
    /// The case the whole thing exists for: a minted slot may be identified with a
    /// pattern slot, and the pattern slot must be the one that survives.
    /// A slot that is not a CANDIDATE never merges, and is still in the domain of what
    /// comes back -- the two are different questions. This is what keeps a binder's
    /// bound slot, which no bound variable carries, from being renamed onto an
    /// unrelated class's slot, while leaving it nameable afterwards.
    /// Two minted slots have both directions available, so they merge; which of the
    /// two survives is not observable, but the partition is.
    /// Three free slots give the five partitions of a 3-set (Bell(3)), and the first
    /// is the all-apart one.
    /// The cap truncates rather than growing without bound, and index 0 survives it.
    /// The shape of the `M3` divergence: two atoms share one slot, and the second
    /// atom's other slot may either take a fresh name or the one the first atom's
    /// other child already occupies.
    fn m3_args() -> Vec<BTreeMap<i64, i64>> {
        let avoid = m(&[(0, 0), (1, 1)]); // pattern slots already named
        let domain = m(&[(0, 0), (2, 2)]); // this atom's node slots
        let first = m(&[(0, 0)]); // pattern side of the shared-variable constraint
        let second = m(&[(0, 0)]); // node side
        vec![avoid, domain, first, second]
    }

    #[test]
    fn index_zero_is_the_minting_solution() {
        let args = m3_args();
        let all = find_mappings_total(&args, 64);
        assert_eq!(all[0], find_mapping_total(&args).unwrap());
    }

    #[test]
    fn the_identification_is_offered() {
        let all = find_mappings_total(&m3_args(), 64);
        // node slot 2 takes a fresh name, or pattern slot 1
        assert_eq!(all, vec![m(&[(0, 0), (2, 2)]), m(&[(0, 0), (2, 1)])]);
    }

    #[test]
    fn every_naming_stays_injective() {
        for naming in find_mappings_total(&m3_args(), 64) {
            let vals: BTreeSet<i64> = naming.values().copied().collect();
            assert_eq!(vals.len(), naming.len(), "not injective: {naming:?}");
        }
    }

    #[test]
    fn the_order_is_stable() {
        let a = find_mappings_total(&m3_args(), 64);
        let b = find_mappings_total(&m3_args(), 64);
        assert_eq!(a, b);
    }

    #[test]
    fn the_count_matches_what_is_enumerated() {
        // one unnamed key, one reusable slot
        assert_eq!(naming_count(1, 1), 2);
        assert_eq!(find_mappings_total(&m3_args(), 64).len(), 2);
        assert_eq!(naming_count(0, 5), 1);
        // These are injective assignments, not set partitions. Two keys over two
        // reusable slots: fresh/fresh, fresh/a, fresh/b, a/fresh, b/fresh, a/b, b/a.
        assert_eq!(naming_count(2, 2), 7);

        // and the formula agrees with what is actually built
        let avoid = m(&[(0, 0), (1, 1), (2, 2)]);
        let domain = m(&[(5, 5), (6, 6), (7, 7)]);
        // paired maps share the edge position as key; the values are the two sides'
        // slots, so this pins node slot 5 onto pattern slot 0
        let args = vec![avoid, domain, m(&[(0, 0)]), m(&[(0, 5)])];
        let all = find_mappings_total(&args, 999);
        assert_eq!(all.len() as u128, naming_count(2, 2));
    }

    #[test]
    fn the_cap_truncates_rather_than_lying() {
        let all = find_mappings_total(&m3_args(), 1);
        assert_eq!(all.len(), 1);
        assert_eq!(all[0], find_mapping_total(&m3_args()).unwrap());
    }

    /// The chain, not one call: each atom's avoid-set is the previous atoms' image,
    /// so a later atom may name a slot an earlier one minted. This is the claim the
    /// per-atom design rests on -- that composing the choices reaches every way the
    /// atoms' slots could coincide, without any call refining an earlier answer.
    #[test]
    fn chaining_reaches_every_partition_of_three_slots() {
        // three atoms, each with a single unconstrained node slot and no pairs
        fn step(avoid: &BTreeMap<i64, i64>) -> Vec<BTreeMap<i64, i64>> {
            find_mappings_total(&[avoid.clone(), m(&[(0, 0)])], 64)
        }

        let mut partitions: BTreeSet<Vec<usize>> = BTreeSet::new();
        for a in step(&m(&[])) {
            let sa = a[&0];
            let avoid_b: BTreeMap<i64, i64> = [(sa, sa)].into_iter().collect();
            for b in step(&avoid_b) {
                let sb = b[&0];
                let mut avoid_c = avoid_b.clone();
                avoid_c.insert(sb, sb);
                for c in step(&avoid_c) {
                    let sc = c[&0];
                    // the partition the three choices induce, as block indices
                    let mut blocks = Vec::new();
                    let mut seen: Vec<i64> = Vec::new();
                    for s in [sa, sb, sc] {
                        let idx = seen.iter().position(|x| *x == s).unwrap_or_else(|| {
                            seen.push(s);
                            seen.len() - 1
                        });
                        blocks.push(idx);
                    }
                    partitions.insert(blocks);
                }
            }
        }
        // Bell(3) = 5: all distinct, any one pair together (three ways), all together
        assert_eq!(partitions.len(), 5, "reached {partitions:?}");
        assert!(partitions.contains(&vec![0, 1, 2]));
        assert!(partitions.contains(&vec![0, 0, 0]));
        assert!(partitions.contains(&vec![0, 0, 1]));
        assert!(partitions.contains(&vec![0, 1, 0]));
        assert!(partitions.contains(&vec![0, 1, 1]));
    }

    #[test]
    fn unsatisfiable_constraints_give_nothing() {
        let avoid = m(&[(0, 0)]);
        let domain = m(&[(0, 0)]);
        // the same node slot forced onto two different pattern slots
        let args = vec![avoid, domain, m(&[(0, 0), (1, 1)]), m(&[(0, 5), (1, 5)])];
        assert!(find_mappings_total(&args, 64).is_empty());
    }
}

#[cfg(test)]
mod shape_tests {
    use super::shape;
    use std::collections::BTreeMap;

    fn m(pairs: &[(i64, i64)]) -> BTreeMap<i64, i64> {
        pairs.iter().copied().collect()
    }

    #[test]
    fn renamed_nodes_share_a_shape_and_back_undoes_it() {
        let a = shape(&[m(&[(0, 5)]), m(&[(0, 3)])]);
        let b = shape(&[m(&[(0, 1)]), m(&[(0, 2)])]);
        assert_eq!(a[..2], b[..2]);
        assert_eq!(a[0], m(&[(0, 0)]));
        assert_eq!(a[1], m(&[(0, 1)]));
        assert_eq!(a[2], m(&[(0, 5), (1, 3)]));
        assert_eq!(b[2], m(&[(0, 1), (1, 2)]));
    }

    #[test]
    fn a_shared_slot_is_a_different_node() {
        let same = shape(&[m(&[(0, 5)]), m(&[(0, 5)])]);
        let apart = shape(&[m(&[(0, 5)]), m(&[(0, 3)])]);
        assert_eq!(same[1], m(&[(0, 0)]));
        assert_ne!(same[..2], apart[..2]);
    }

    #[test]
    fn private_slots_of_one_column_may_be_permuted() {
        let xy = shape(&[m(&[(0, 0), (1, 1)]), m(&[(0, 2), (1, 3)])]);
        let yx = shape(&[m(&[(0, 0), (1, 1)]), m(&[(0, 3), (1, 2)])]);
        assert_eq!(xy[..2], yx[..2]);
        let shared_xy = shape(&[m(&[(0, 0)]), m(&[(0, 0), (1, 1)])]);
        let shared_yx = shape(&[m(&[(0, 0)]), m(&[(0, 1), (1, 0)])]);
        assert_ne!(shared_xy[..2], shared_yx[..2]);
    }
}
