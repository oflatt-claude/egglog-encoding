//! Oracle for differential-testing the egglog slotted encoding's multipattern
//! matching against the reference `slotted-egraphs` implementation.
//!
//! Prints, per case, how many matches `multi_ematch` finds and what each
//! substitution binds, so the encoded rule can be diffed against it.

use slotted_egraphs::*;

define_language! {
    pub enum MP {
        Var(Slot) = "var",
        Add(AppliedId, AppliedId) = "add",
        Sub(AppliedId, AppliedId) = "sub",
        Sub2(AppliedId, AppliedId) = "sub2",
        Zero() = "zero",
    }
}

type G = EGraph<MP>;

fn add(eg: &mut G, s: &str) -> AppliedId {
    eg.add_expr(RecExpr::<MP>::parse(s).unwrap())
}

fn probe(eg: &G, p: &str) {
    let pat: MultiPattern<MP> = MultiPattern::parse(p).unwrap();
    let ms = multi_ematch(&pat, eg);
    println!("  {:>2} match   `{}`", ms.len(), p);
    for s in &ms {
        let mut ks: Vec<&String> = s.keys().collect();
        ks.sort();
        let body: Vec<String> = ks.iter().map(|k| format!("?{k}={:?}", s[*k])).collect();
        println!("        {}", body.join("  "));
    }
}

fn main() {
    // R1: one node with a redundant slot, reached through two atoms.
    let mut eg = G::default();
    let s = add(&mut eg, "(sub (var $9) (var $9))");
    let z = add(&mut eg, "zero");
    eg.union(&s, &z);
    add(&mut eg, "(add zero zero)");
    println!("R1: same node through both atoms");
    probe(&eg, "?p == (add ?a ?b), ?a == (sub ?u ?u), ?b == (sub ?u ?u)");

    // R2: two DIFFERENT nodes, each with its own redundant slot, named
    // differently. `?u` in both atoms forces the two to be identified.
    let mut eg = G::default();
    let s1 = add(&mut eg, "(sub (var $9) (var $9))");
    let z = add(&mut eg, "zero");
    eg.union(&s1, &z);
    let s2 = add(&mut eg, "(sub2 (var $7) (var $7))");
    eg.union(&s2, &z);
    add(&mut eg, "(add zero zero)");
    println!("R2: two different nodes, ?u forced equal across them");
    probe(&eg, "?p == (add ?a ?b), ?a == (sub ?u ?u), ?b == (sub2 ?u ?u)");
    println!("R2 control: distinct pvars");
    probe(&eg, "?p == (add ?a ?b), ?a == (sub ?u ?u), ?b == (sub2 ?v ?v)");
}
