//! Reference oracle for differential-testing the egglog slotted encoding's
//! multipattern matching against `slotted-egraphs`.
//!
//! Reads a spec on stdin and prints one `PARTITION <groups>` line: the probe
//! terms grouped by the e-graph's own equality after saturating the given rule.
//! The encoding side runs the same spec and the two lines are compared.
//!
//! Spec lines (`#` comments and blanks ignored):
//!
//! ```text
//! term   <sexpr>              add a term
//! union  <sexpr> <sexpr>      union two terms
//! atom   <root> <op> <c1> <c2>    one depth-1 multipattern atom (pvar names)
//! action <root> <op> <a> <b>  union ?root with (op ?a ?b)
//! probe  <sexpr>              term to include in the reported partition
//! rounds <n>                  saturation rounds (default 10)
//! ```

use slotted_egraphs::*;
use std::collections::BTreeSet;
use std::io::Read;

define_language! {
    pub enum L {
        Var(Slot) = "var",
        Null() = "null",
        // The machinery encodes this as `(App "lambda" {0->x} (Var 0) mb body)`,
        // so the bound slot rides in the first child's edge on that side.
        Lam(Bind<AppliedId>) = "lam",
        F(AppliedId, AppliedId) = "f",
        G(AppliedId, AppliedId) = "g",
        H(AppliedId, AppliedId) = "h",
        K(AppliedId, AppliedId) = "k",
        Sub(AppliedId, AppliedId) = "sub",
        Sub2(AppliedId, AppliedId) = "sub2",
        Add(AppliedId, AppliedId) = "add",
    }
}

type G = EGraph<L>;

struct Spec {
    terms: Vec<String>,
    unions: Vec<(String, String)>,
    atoms: Vec<String>,
    action: Option<(String, String, String, String)>,
    probes: Vec<String>,
    rounds: usize,
}

fn parse_spec(src: &str) -> Spec {
    let mut s = Spec {
        terms: vec![],
        unions: vec![],
        atoms: vec![],
        action: None,
        probes: vec![],
        rounds: 10,
    };
    for line in src.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (kind, rest) = line.split_once(char::is_whitespace).unwrap_or((line, ""));
        let rest = rest.trim();
        match kind {
            "term" => s.terms.push(rest.to_string()),
            "probe" => s.probes.push(rest.to_string()),
            "rounds" => s.rounds = rest.parse().unwrap(),
            "union" => {
                let (a, b) = split_two_sexprs(rest);
                s.unions.push((a, b));
            }
            // `?p == (op ?c1 ?c2)` is rebuilt from the four names, so the
            // generator does not have to agree on pattern syntax.
            // A child written `$v` is a slot literal and goes through as-is; a
            // binder's slot must be one, since `Bind` has no room for a pattern
            // variable there.
            "atom" => {
                let w: Vec<&str> = rest.split_whitespace().collect();
                let kid = |c: &str| {
                    if c.starts_with('$') { c.to_string() } else { format!("?{c}") }
                };
                s.atoms.push(format!(
                    "?{} == ({} {} {})",
                    w[0], w[1], kid(w[2]), kid(w[3])
                ));
            }
            "action" => {
                let w: Vec<&str> = rest.split_whitespace().collect();
                s.action = Some((
                    w[0].to_string(),
                    w[1].to_string(),
                    w[2].to_string(),
                    w[3].to_string(),
                ));
            }
            other => panic!("unknown spec line kind: {other}"),
        }
    }
    s
}

/// Split `"<sexpr> <sexpr>"` at the top-level boundary between the two.
fn split_two_sexprs(s: &str) -> (String, String) {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return (s[..=i].trim().to_string(), s[i + 1..].trim().to_string());
                }
            }
            ' ' if depth == 0 && i > 0 => {
                return (s[..i].trim().to_string(), s[i + 1..].trim().to_string());
            }
            _ => {}
        }
    }
    panic!("cannot split two s-exprs from {s:?}");
}

fn add(eg: &mut G, s: &str) -> AppliedId {
    eg.add_expr(RecExpr::<L>::parse(s).unwrap())
}

fn main() {
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    let spec = parse_spec(&src);

    let mut eg = G::default();
    for t in &spec.terms {
        add(&mut eg, t);
    }
    for (a, b) in &spec.unions {
        let x = add(&mut eg, a);
        let y = add(&mut eg, b);
        eg.union(&x, &y);
    }
    for p in &spec.probes {
        add(&mut eg, p);
    }

    if !spec.atoms.is_empty() {
        if let Some((root, op, a, b)) = &spec.action {
            let pat: MultiPattern<L> = MultiPattern::parse(&spec.atoms.join(", ")).unwrap();
            let from = Pattern::PVar(root.clone());
            // `action <root> = <x> <x>` equates two pattern variables directly,
            // so both sides can carry a non-identity renaming. Anything else
            // builds a node, which is always at the identity in pattern slots.
            let to: Pattern<L> = if op == "=" {
                Pattern::PVar(a.clone())
            } else {
                Pattern::parse(&format!("({op} ?{a} ?{b})")).unwrap()
            };
            let debug = std::env::var("XMULTI_DEBUG").is_ok();
            let mut saturated = false;
            for round in 0..spec.rounds {
                let before = eg.progress();
                let substs = multi_ematch(&pat, &eg);
                if debug {
                    eprintln!("round {round}: {} match(es)", substs.len());
                    for s in &substs {
                        let mut ks: Vec<&String> = s.keys().collect();
                        ks.sort();
                        let body: Vec<String> =
                            ks.iter().map(|k| format!("?{k}={:?}", s[*k])).collect();
                        eprintln!("    {}", body.join("  "));
                    }
                }
                for s in substs {
                    eg.union_instantiations(&from, &to, &s, None);
                }
                if before == eg.progress() {
                    saturated = true;
                    break;
                }
            }
            // A case that hit the round cap without settling means the two sides
            // ran different amounts of work, so comparing them says nothing.
            println!("SATURATED {}", if saturated { "yes" } else { "no" });
        }
    }

    println!("PARTITION {}", partition(&eg, &spec.probes));
}

/// Probe indices grouped by **e-class identity**, as a canonical string.
///
/// Deliberately not `eg.eq`, which is equality of *renamed ids* and so depends
/// on which slot names the invocation carries: after a redundancy two probe
/// terms can sit in one e-class while naming different surviving slots, and
/// `eg.eq` calls those unequal. The encoding side reads e-class identity out of
/// egglog, so this is the notion that makes the two comparable.
fn partition(eg: &G, probes: &[String]) -> String {
    let ids: Vec<Option<AppliedId>> = probes
        .iter()
        .map(|p| lookup_rec_expr(&RecExpr::<L>::parse(p).unwrap(), eg))
        .collect();

    let mut groups: Vec<BTreeSet<usize>> = Vec::new();
    let mut missing: Vec<usize> = Vec::new();
    for i in 0..probes.len() {
        let Some(a) = &ids[i] else {
            missing.push(i);
            continue;
        };
        let mut placed = false;
        for g in groups.iter_mut() {
            let j = *g.iter().next().unwrap();
            let b = ids[j].as_ref().unwrap();
            if eg.find_applied_id(a).id == eg.find_applied_id(b).id {
                g.insert(i);
                placed = true;
                break;
            }
        }
        if !placed {
            groups.push([i].into_iter().collect());
        }
    }
    let mut gs: Vec<String> = groups
        .iter()
        .map(|g| {
            let v: Vec<String> = g.iter().map(|i| i.to_string()).collect();
            format!("[{}]", v.join(","))
        })
        .collect();
    gs.sort();
    format!("{} missing[{:?}]", gs.join(""), missing)
}
