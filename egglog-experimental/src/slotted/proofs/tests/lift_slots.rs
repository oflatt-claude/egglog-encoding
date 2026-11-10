use super::*;

#[test]
fn composition_preserves_scoped_alpha_and_edge_coordinates() {
    let mut program = ProofContext::default();
    program.add_constructor("Start", vec![]);
    program.add_constructor("Done", vec![]);
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor(
        "Let",
        vec![ColumnKind::Child, ColumnKind::Binder, ColumnKind::Child],
    );
    let mut dag = TermDag::default();
    program
        .add_union(&mut dag, "(Start)", "(Let (V $10) $10 (V $10))")
        .unwrap();
    program
        .add_union(&mut dag, "(Let (V $0) $1 (V $1))", "(Done)")
        .unwrap();
    program
        .add_union(&mut dag, "(Let (V $2) $1 (V $1))", "(Done)")
        .unwrap();
    let names = EncodingNames::default();
    let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
    let mut lifter = SlotLifter::new(&program, dag, &names, &egg);
    let [first, second, wrong] = program.unions.as_slice() else {
        unreachable!()
    };
    let left = lifter.out.fiat(first.lhs, first.rhs);
    let left = lifter
        .out
        .reframe(left, Renaming::new([(0, 10), (10, 0)]).unwrap());
    let right = lifter.out.fiat(second.lhs, second.rhs);
    let wrong = lifter.out.fiat(wrong.lhs, wrong.rhs);
    assert!(lifter.trans(left, wrong).is_err());
    let proof = lifter.trans(left, right).unwrap();
    let (mut store, proof) = lifter.out.finish(proof);
    super::super::checker::check_proof_in_program(&mut store, &program, proof).unwrap();
    assert_eq!(
        store.proposition(proof),
        &Proposition::new(first.lhs, second.rhs)
    );
}

#[test]
fn reflexivity_rejects_incompatible_shapes_before_alpha_conversion() {
    let mut program = ProofContext::default();
    program.add_constructor("Z", vec![]);
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_constructor("Triple", vec![ColumnKind::Child; 3]);
    let mut dag = TermDag::default();
    let vars: Vec<_> = (0..5)
        .map(|slot| {
            let slot = slot_term(&mut dag, slot);
            dag.app("V".into(), vec![slot])
        })
        .collect();
    let zero = dag.app("Z".into(), vec![]);
    let good = dag.app("Triple".into(), vec![vars[3], vars[4], zero]);
    let mut shared = zero;
    for _ in 0..32 {
        shared = dag.app("Pair".into(), vec![shared, shared]);
    }
    let bad = dag.app("Triple".into(), vec![vars[0], vars[0], shared]);
    let target = dag.app("Triple".into(), vec![vars[1], vars[2], zero]);
    program.lets.insert("good".into(), good);
    program.lets.insert("bad".into(), bad);
    // The bad candidate is visited first. Its early repeated-slot conflict must
    // not send the enormous, structurally different third child through Alpha.
    assert_eq!(program.built_terms(&dag)[0], bad);
    let names = EncodingNames::default();
    let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
    let mut lifter = SlotLifter::new(&program, dag, &names, &egg);
    let proof = lifter.reflexive(target).unwrap();
    let (mut store, proof) = lifter.out.finish(proof);
    super::super::checker::check_proof_in_program(&mut store, &program, proof).unwrap();
    assert_eq!(store.proposition(proof), &Proposition::new(target, target));
}

#[test]
fn variable_expansion_replays_its_construction_witness() {
    use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};
    use egglog::CommandOutput;

    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let encoded = compiler
        .compile_program(
            None,
            "(datatype E (Start) (Wrap E) (One))
             (let input (Start))
             (rewrite (Start) (Wrap (One)) :name build)
             (run 1)
             (check (= input (Wrap (One))))",
        )
        .unwrap();
    // Retain the ordinary proof before the source lifter visits the build rule.
    let commands = encoded.to_string().replace("(slotted-prove 0 ", "(prove ");
    let mut graph = new_egraph_with_proofs();
    let egg = graph
        .parse_and_run_program(None, &commands)
        .unwrap()
        .into_iter()
        .find_map(|output| match output {
            CommandOutput::ProveExists { proof_store, .. } => Some(proof_store),
            _ => None,
        })
        .unwrap();
    let request = encoded.proofs.values().next().unwrap();
    let mut dag = TermDag::default();
    let context = request
        .flattened
        .context(&mut dag, BTreeMap::new())
        .unwrap();
    let mut lifter = SlotLifter::new(&context, dag, &request.names, &egg);
    let (witness, class, target) = egg
        .proofs()
        .find_map(|(id, proof)| {
            if !matches!(proof.justification(), Justification::Rule { name, .. } if name == "build/apply")
                || proof.lhs() != proof.rhs()
                || !lifter.is_carrier_term(proof.lhs())
            {
                return None;
            }
            let target = lifter.dec(proof.lhs()).unwrap();
            lifter.reflexive(target).is_err().then_some((id, proof.lhs(), target))
        })
        .expect("a newly constructed term must have its own rule witness");
    let pattern = lifter.out.term_dag.var("total".into());
    let subst = IndexMap::default();
    let bridges = HashMap::default();
    let ctx = ExpandCtx {
        prems: &[witness],
        subst: &subst,
        names: HashMap::default(),
        classes: BTreeMap::new(),
        readings: BTreeMap::new(),
        rows: BTreeMap::new(),
        bridges: &bridges,
    };
    let expanded = lifter
        .expand(class, pattern, &[], &ctx, HashMap::default())
        .unwrap();
    let (mut store, proof) = lifter.out.finish(expanded.proof);
    super::super::check_proof(&mut store, &request.flattened, proof).unwrap();
    assert_eq!(store.proposition(proof), &Proposition::new(target, target));
}

#[test]
fn carrier_projections_replay_the_recorded_parent_and_column() {
    use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};
    use egglog::CommandOutput;

    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let encoded = compiler
        .compile_program(
            None,
            "(datatype E (Start) (V Var) (Wrap E) (Lam Var E :binder 0))
             (let input (Start))
             (rewrite (Start) (Lam $x (Wrap (V $x))) :name build)
             (run 1)
             (check (= input (Lam $y (Wrap (V $y)))))",
        )
        .unwrap();
    let commands = encoded.to_string().replace("(slotted-prove 0 ", "(prove ");
    let egg = new_egraph_with_proofs()
        .parse_and_run_program(None, &commands)
        .unwrap()
        .into_iter()
        .find_map(|output| match output {
            CommandOutput::ProveExists { proof_store, .. } => Some(proof_store),
            _ => None,
        })
        .unwrap();
    let request = encoded.proofs.values().next().unwrap();
    let mut dag = TermDag::default();
    let context = request
        .flattened
        .context(&mut dag, BTreeMap::new())
        .unwrap();
    let mut checked = 0;
    for (id, proof) in egg.proofs() {
        if !matches!(proof.justification(), Justification::Rule { name, .. } if name == "build/apply")
        {
            continue;
        }
        let mut lifter = SlotLifter::new(&context, dag.clone(), &request.names, &egg);
        let Some((head, args)) = lifter.app(proof.rhs()) else {
            continue;
        };
        let physical = match head {
            "Lam" => 2,
            "Wrap" => 1,
            _ => continue,
        };
        let child = args[physical];
        let expected = lifter.dec(child).unwrap();
        let lifted = lifter.project(id, physical).unwrap();
        let (mut store, lifted) = lifter.out.finish(lifted);
        super::super::check_proof(&mut store, &request.flattened, lifted).unwrap();
        assert_eq!(
            store.proposition(lifted),
            &Proposition::new(expected, expected)
        );
        checked += 1;
    }
    assert!(
        checked > 0,
        "the extracted proof must contain a constructed parent"
    );
}

#[test]
fn existence_proofs_respect_binder_scopes() {
    use crate::slotted::proofs::{check_proof, resolve_program};
    use egglog::ast::{Parser, parse_sexps};

    for (input, target, exists) in [
        (
            "(Pair (Lam $0 (V $0)) (V $0))",
            "(Pair (Lam $1 (V $1)) (V $0))",
            true,
        ),
        (
            "(Pair (Lam $0 (V $0)) (Lam $0 (V $0)))",
            "(Pair (Lam $1 (V $1)) (Lam $2 (V $2)))",
            true,
        ),
        ("(Lam $0 (V $1))", "(Lam $1 (V $1))", false),
    ] {
        let source =
            format!("(datatype E (V Var) (Lam Var E :binder 0) (Pair E E)) (let input {input})");
        let source = resolve_program(&parse_sexps(None, &source).unwrap()).unwrap();
        let mut dag = TermDag::default();
        let context = source.context(&mut dag, BTreeMap::new()).unwrap();
        let target = Parser::default()
            .get_expr_from_string(None, target)
            .unwrap();
        let target = context.ground_term(&mut dag, &target).unwrap();
        let names = EncodingNames::default();
        let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
        let mut lifter = SlotLifter::new(&context, dag, &names, &egg);
        let proof = lifter.reflexive(target);
        if !exists {
            assert!(
                proof.is_err(),
                "alpha conversion cannot capture a free slot"
            );
            continue;
        }
        let proof = proof.unwrap();
        let (mut store, proof) = lifter.out.finish(proof);
        check_proof(&mut store, &source, proof).unwrap();
        assert_eq!(store.proposition(proof), &Proposition::new(target, target));
    }
}

#[test]
fn slot_matching_preserves_shared_constraints_and_bijections() {
    let program = ProofContext::default();
    let names = EncodingNames::default();
    let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
    let mut dag = TermDag::default();
    let slots: Vec<_> = (0..3).map(|slot| slot_term(&mut dag, slot)).collect();
    let repeated = dag.app("Pair".into(), vec![slots[0], slots[0]]);
    let distinct = dag.app("Pair".into(), vec![slots[1], slots[2]]);
    let mut left = repeated;
    let mut right = dag.app("Pair".into(), vec![slots[1], slots[1]]);
    // These terms have billions of tree occurrences but only dozens of DAG
    // nodes. Matching must retain the slot constraint while sharing the walk.
    for _ in 0..32 {
        left = dag.app("Pair".into(), vec![left, left]);
        right = dag.app("Pair".into(), vec![right, right]);
    }
    let tr = SlotLifter::new(&program, dag, &names, &egg);
    let mut pairs = BTreeMap::new();
    assert!(tr.match_slots(left, right, &mut pairs).is_ok());
    assert_eq!(pairs, BTreeMap::from([(0, 1)]));
    assert!(Renaming::completing(pairs).is_some());

    let mut pairs = BTreeMap::new();
    assert!(tr.match_slots(repeated, distinct, &mut pairs).is_err());
    assert_eq!(
        tr.unify_slots(repeated, distinct, &mut BTreeMap::new())
            .unwrap_err(),
        "slot $0 would have to be both $1 and $2"
    );
    let mut pairs = BTreeMap::new();
    assert!(tr.match_slots(distinct, repeated, &mut pairs).is_ok());
    assert!(Renaming::completing(pairs).is_none());
    // An identical pair still constrains its slot to itself; skipping it would
    // incorrectly accept an incompatible mapping supplied by an earlier match.
    assert!(
        tr.match_slots(slots[0], slots[0], &mut BTreeMap::from([(0, 1)]))
            .is_err()
    );
    // A rejected structural candidate must not try to print the enormous DAG.
    assert!(
        tr.match_slots(left, slots[0], &mut BTreeMap::new())
            .is_err()
    );
}

#[test]
fn source_names_take_precedence_over_generated_rule_kinds() {
    let mut program = ProofContext::default();
    program.add_constructor("N", vec![]);
    program
        .add_rewrite(
            &mut TermDag::default(),
            "(rewrite (N) (N) :name slotted/group-shrink)",
        )
        .unwrap();
    assert_eq!(
        rule_kind(&program, "slotted/group-shrink"),
        RuleKind::Source("slotted/group-shrink")
    );
    assert_eq!(
        rule_kind(&program, "slotted/group-shrink/apply"),
        RuleKind::Apply("slotted/group-shrink")
    );
    assert_eq!(
        rule_kind(&program, "slotted/group-shrink/0"),
        RuleKind::GroupShrink
    );
    assert_eq!(
        rule_kind(&program, "slotted/unknown/0"),
        RuleKind::Unknown("slotted/unknown/0")
    );
}

pub(in crate::slotted::proofs) fn check_restricted_symmetries(
    program: &ProofContext,
    dag: TermDag,
    names: &EncodingNames,
    egg: &ProofStore,
) -> LiftResult<usize> {
    let mut tr = SlotLifter::new(program, dag, names, egg);
    let mut checked = 0;
    for (id, proof) in egg.proofs() {
        let Justification::Rule {
            name,
            substitution,
            premise_proofs,
        } = proof.justification()
        else {
            continue;
        };
        if rule_kind(program, name) != RuleKind::GroupShrink {
            continue;
        }
        let old = tr.group(substitution["_s"])?;
        let slots = tr.slot_map(substitution["_cs"])?;
        if old
            .iter()
            .all(|g| g.keys().all(|slot| slots.contains_key(slot)))
        {
            continue;
        }
        let restored = egg
            .proofs()
            .find_map(|(restored, proof)| match proof.justification() {
                Justification::Rule {
                    name,
                    premise_proofs,
                    ..
                } if rule_kind(program, name) == RuleKind::GroupRestore
                    && premise_proofs.first() == Some(&id) =>
                {
                    Some(restored)
                }
                _ => None,
            })
            .ok_or("restricted group has no restore proof")?;
        let (_, args) = tr.app(proof.lhs()).ok_or("expected staged group row")?;
        let class = args[0];
        for generator in old {
            let restricted = compose(&slots, &compose(&generator, &slots));
            if is_identity(&restricted) || restricted.len() == generator.len() {
                continue;
            }
            let symmetry = tr.product_symmetry(
                class,
                &restricted,
                &[(generator, premise_proofs[0])],
                Some(&slots),
            )?;
            let proof = tr.out.proof(symmetry);
            crate::slotted::proofs::checker::check_proof_in_program(&mut tr.out, program, proof)
                .map_err(|e| e.to_string())?;
            checked += 1;
        }
        for g in tr.group(args[1])? {
            if is_identity(&g) {
                continue;
            }
            let symmetry = tr.symmetry(class, &g, restored)?;
            let proof = tr.out.proof(symmetry);
            crate::slotted::proofs::checker::check_proof_in_program(&mut tr.out, program, proof)
                .map_err(|e| e.to_string())?;
        }
    }
    Ok(checked)
}

#[test]
fn equal_decoded_endpoints_preserve_a_nontrivial_class_equality() {
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    let mut dag = TermDag::default();
    program
        .add_union(&mut dag, "(Pair (V $0) (V $1))", "(Pair (V $1) (V $0))")
        .unwrap();
    let term = program.unions[0].lhs;
    let mut encoded = TermDag::default();
    let mut map = |entries: &[i64]| {
        let entries = entries
            .iter()
            .map(|&n| encoded.lit(Literal::Int(n)))
            .collect();
        encoded.app("map-of".into(), entries)
    };
    let identity = map(&[0, 0]);
    let redundant = map(&[0, 0, 7, 9]);
    let shifted = map(&[0, 1]);
    let variable = encoded.app("V".into(), vec![identity]);
    let left = encoded.app("Pair".into(), vec![identity, variable, shifted, variable]);
    let right = encoded.app("Pair".into(), vec![redundant, variable, shifted, variable]);
    let egg = ProofStore::new(encoded, HashMap::default(), HashSet::default());
    let names = EncodingNames::default();
    let mut lifter = SlotLifter::new(&program, dag, &names, &egg);
    assert_ne!(left, right);
    assert_eq!(lifter.dec(left).unwrap(), term);
    assert_eq!(lifter.dec(right).unwrap(), term);
    let proof = lifter.out.fiat(term, program.unions[0].rhs);
    let swap = Renaming::new([(0, 1), (1, 0)]).unwrap();
    let proof = lifter.out.reframe(proof, swap.clone());
    let oriented = lifter.orient(proof, left, right).unwrap();
    assert_eq!(lifter.out.edge(oriented).renaming, swap);
    let reflexive = lifter.orient(proof, left, left).unwrap();
    assert!(lifter.out.edge(reflexive).renaming.is_identity());
    let (mut store, proof) = lifter.out.finish(oriented);
    super::super::checker::check_proof_in_program(&mut store, &program, proof).unwrap();
}
