#[cfg(test)]
mod tests {
    use crate::ast::{
        GenericAction, GenericNCommand, Literal, ResolvedAction, ResolvedCommand, ResolvedExpr,
        RuleEvalMode, sanitize_internal_names,
    };
    use crate::core::ResolvedCall;
    use crate::proofs::proof_checker::process_actions;
    use crate::proofs::proof_extraction::ProveExistsError;
    use crate::proofs::proof_sites::{
        ConclusionSite, SiteConclusion, SiteIndex, action_sites, conclusion_sites,
    };
    use crate::util::{HashMap, HashSet};
    use crate::{
        CommandOutput, EGraph, Error, ProofEncodingUnsupportedReason, TermDag, TermId,
        add_primitive_with_validator,
    };

    fn term_encode(source: &str) -> Vec<ResolvedCommand> {
        let mut egraph = crate::EGraph::new_with_term_encoding();
        egraph.resolve_program(None, source).unwrap()
    }

    /// Render what each site concludes, in the order it was enumerated.
    fn describe_sites(sites: &[ConclusionSite<'_>]) -> Vec<String> {
        sites
            .iter()
            .map(|site| match &site.conclusion {
                SiteConclusion::Reflexive(expr) => format!("exists {expr}"),
                SiteConclusion::Equality(lhs, rhs) => format!("equal {lhs} {rhs}"),
            })
            .collect()
    }

    /// The site descriptions a rule head must produce, derived independently of
    /// `conclusion_sites`: actions in order, each contributing the pre-order of
    /// its expressions, and a `union` also contributing its equality first.
    fn expected_site_descriptions(actions: &[ResolvedAction]) -> Vec<String> {
        fn preorder(expr: &ResolvedExpr, out: &mut Vec<String>) {
            out.push(format!("exists {expr}"));
            if let ResolvedExpr::Call(_, _, args) = expr {
                for arg in args {
                    preorder(arg, out);
                }
            }
        }
        let mut out = vec![];
        for action in actions {
            match action {
                GenericAction::Let(_, _, expr) | GenericAction::Expr(_, expr) => {
                    preorder(expr, &mut out)
                }
                GenericAction::Union(_, lhs, rhs) => {
                    out.push(format!("equal {lhs} {rhs}"));
                    preorder(lhs, &mut out);
                    preorder(rhs, &mut out);
                }
                GenericAction::Set(span, func, args, value) => {
                    let mut row = args.to_vec();
                    row.push(value.clone());
                    let row = ResolvedExpr::Call(span.clone(), func.clone(), row);
                    out.push(format!("exists {row}"));
                    for arg in args {
                        preorder(arg, &mut out);
                    }
                    preorder(value, &mut out);
                }
                GenericAction::Panic(..) | GenericAction::Change(..) => {}
            }
        }
        out
    }

    /// Stand a distinct constant in for every variable a rule head reads but
    /// does not itself bind, so the head can be processed without a match.
    fn head_input_bindings(
        actions: &[ResolvedAction],
        term_dag: &mut TermDag,
    ) -> HashMap<String, TermId> {
        fn read(expr: &ResolvedExpr, bound: &HashSet<String>, inputs: &mut Vec<String>) {
            expr.visit_vars(&mut |_, var| {
                if !bound.contains(&var.name) && !inputs.contains(&var.name) {
                    inputs.push(var.name.clone());
                }
            });
        }
        let mut bound: HashSet<String> = HashSet::default();
        let mut inputs = vec![];
        for action in actions {
            match action {
                GenericAction::Let(_, var, expr) => {
                    read(expr, &bound, &mut inputs);
                    bound.insert(var.name.clone());
                }
                GenericAction::Expr(_, expr) => read(expr, &bound, &mut inputs),
                GenericAction::Union(_, lhs, rhs) => {
                    read(lhs, &bound, &mut inputs);
                    read(rhs, &bound, &mut inputs);
                }
                GenericAction::Set(_, _, args, value) => {
                    for arg in args {
                        read(arg, &bound, &mut inputs);
                    }
                    read(value, &bound, &mut inputs);
                }
                GenericAction::Panic(..) | GenericAction::Change(..) => {}
            }
        }
        inputs
            .into_iter()
            .map(|name| {
                let term = term_dag.app(name.clone(), vec![]);
                (name, term)
            })
            .collect()
    }

    /// A rule head's conclusion sites are the one enumeration the proof checker
    /// and the proof encoder both index into, so nothing may recompute the
    /// order. Pin it: the sites are exactly the pre-order of each action's
    /// expressions (plus one equality per `union`), they are numbered densely
    /// from zero, and processing the head resolves each of them, in that same
    /// order, to a proposition the head implies.
    #[test]
    fn conclusion_sites_index_every_rule_head_proposition() {
        let source = r#"
            (datatype Math (Num i64) (Add Math Math) (Neg Math))
            (relation Seen (Math))
            (function Cost (Math) i64 :no-merge)

            (Add (Num 1) (Num 2))

            (rule ((= e (Add a b)))
                  ((union e (Add b a)))
                  :name "commute")

            (rule ((= e (Add a b)))
                  ((let inner (Neg a))
                   (let outer (Add inner b))
                   (union e outer)
                   (Seen outer))
                  :name "nest")

            (rule ((= e (Num n)))
                  ((set (Cost e) 1))
                  :name "cost")

            ;; A `union` neither of whose operands is a matched variable, so the
            ;; orientation check has to read both operands' own sites.
            (rule ((Seen s))
                  ((union (Neg s) (Add s s)))
                  :name "both_built")

            (run 2)
            (prove (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))
        "#;

        let mut egraph = EGraph::new_with_proofs();
        egraph.parse_and_run_program(None, source).unwrap();

        let rules: Vec<_> = egraph
            .proof_check_program
            .iter()
            .filter_map(|cmd| match cmd {
                GenericNCommand::NormRule { rule } => Some(rule),
                _ => None,
            })
            .collect();
        let names: Vec<_> = rules.iter().map(|rule| rule.name.as_str()).collect();
        for expected in ["commute", "nest", "cost", "both_built"] {
            assert!(
                names.contains(&expected),
                "rule '{expected}' not in {names:?}"
            );
        }

        for rule in rules {
            let actions = &rule.head.0;
            let sites = conclusion_sites(actions.iter());
            let described = describe_sites(&sites);

            assert_eq!(
                described,
                expected_site_descriptions(actions),
                "rule '{}' enumerates the wrong conclusion sites",
                rule.name
            );
            let per_action = action_sites(actions.iter());
            let mut term_dag = TermDag::default();
            let inputs = head_input_bindings(actions, &mut term_dag);
            let action_refs: Vec<_> = actions.iter().collect();
            let ctx = process_actions(&rule.name, inputs.clone(), &action_refs, &mut term_dag)
                .unwrap_or_else(|e| panic!("rule '{}' head did not process: {e}", rule.name));

            assert_eq!(
                ctx.site_propositions.len(),
                sites.len(),
                "rule '{}' resolved a different number of sites than it enumerates",
                rule.name
            );
            for (position, (site, (index, prop))) in
                sites.iter().zip(&ctx.site_propositions).enumerate()
            {
                let site_name = format!("rule '{}' site {}", rule.name, index.0);
                assert_eq!(
                    *index,
                    SiteIndex(position),
                    "{site_name} resolved out of order"
                );
                assert!(
                    ctx.propositions.contains(prop),
                    "{site_name} concluded a proposition the head does not imply"
                );
                match &site.conclusion {
                    SiteConclusion::Reflexive(_) => {
                        assert_eq!(prop.lhs(), prop.rhs(), "{site_name} is not reflexive")
                    }
                    // An equality site concludes its operands in the order
                    // written. Each operand's own site is reflexive over the term
                    // that operand evaluates to, so those pin the orientation
                    // whatever the operands are written as.
                    SiteConclusion::Equality(..) => {
                        let [lhs_site, rhs_site] = per_action[site.action].operands[..] else {
                            panic!("{site_name}: a union numbers both its operands");
                        };
                        assert_eq!(
                            prop.lhs(),
                            ctx.site_propositions[lhs_site.0].1.lhs(),
                            "{site_name} did not conclude its lhs operand on the left"
                        );
                        assert_eq!(
                            prop.rhs(),
                            ctx.site_propositions[rhs_site.0].1.lhs(),
                            "{site_name} did not conclude its rhs operand on the right"
                        );
                    }
                }
            }
        }
    }

    /// A rule proof records no terms, so a body variable bound to a value the
    /// body computed — a primitive's result, a container's — reaches the
    /// checker only by replaying the rule. Each case below binds one that way
    /// and proves a conclusion that needs it.
    #[test]
    fn rule_proofs_check_with_computed_body_values() {
        let cases = [
            // a computed String
            r#"(relation Strings (String String))
               (Strings "hello" "world")
               (rule ((Strings a b) (= res (+ a " " b)))
                     ((Strings "found" "hello world")) :name "concat")
               (run 1)
               (prove (Strings "found" "hello world"))"#,
            // a non-eq container matched in the body and read
            r#"(sort IVec (Vec i64))
               (relation HasVec (IVec))
               (relation VLen (i64))
               (HasVec (vec-of 1 2 3))
               (rule ((HasVec v) (= n (vec-length v))) ((VLen n)) :name "vec-len")
               (run 1)
               (prove (VLen 3))"#,
            // a non-eq container whose read computes a base value
            r#"(sort SMap (Map String i64))
               (relation HasMap (SMap))
               (relation MapVal (i64))
               (HasMap (map-insert (map-empty) "a" 7))
               (rule ((HasMap m) (= v (map-get m "a"))) ((MapVal v)) :name "map-get")
               (run 1)
               (prove (MapVal 7))"#,
        ];

        for source in cases {
            let mut egraph = EGraph::new_with_proofs();
            egraph
                .parse_and_run_program(None, source)
                .unwrap_or_else(|e| panic!("{source}\nfailed: {e}"));
        }
    }

    /// The encoding reads `@UF` and `term_proof` from rule actions under
    /// `:unsafe-seminaive` — in user rule heads and in the indexed rebuild
    /// rule. Assert this produces the same database as the safe baseline (the
    /// same rules annotated `:naive`), for a hardcoded handful of files
    /// (running it across all tests would be too slow).
    #[test]
    fn unsafe_seminaive_matches_naive() {
        let files = [
            "tests/calc.egg",
            "tests/integer_math.egg",
            "tests/fibonacci-demand.egg",
            "tests/until.egg",
        ];

        for file in files {
            let source = std::fs::read_to_string(file)
                .unwrap_or_else(|e| panic!("couldn't read {file}: {e}"));

            let encode = |naive: bool| -> String {
                let mut egraph = crate::EGraph::new_with_proofs();
                egraph.proof_state.force_proof_naive = naive;
                egraph
                    .resolve_program(Some(file.to_string()), &source)
                    .unwrap_or_else(|e| panic!("{file} resolve (naive={naive}) failed: {e}"))
                    .iter()
                    .map(|cmd| cmd.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
            };

            // Guard against a vacuous comparison: both `:unsafe-seminaive`
            // sites must be present, and the knob must flip every one of them,
            // since a rule left `:unsafe-seminaive` runs identically on both
            // sides. Only the rebuild rules carry `:internal-include-subsumed`.
            let unsafe_encoding = encode(false);
            let (rebuild, rule_head): (Vec<&str>, Vec<&str>) = unsafe_encoding
                .lines()
                .filter(|line| line.contains(":unsafe-seminaive"))
                .partition(|line| line.contains(":internal-include-subsumed"));
            assert!(
                !rule_head.is_empty(),
                "expected {file} to encode a rule head `:unsafe-seminaive`"
            );
            assert!(
                !rebuild.is_empty(),
                "expected {file} to encode the rebuild rule `:unsafe-seminaive`"
            );
            assert!(
                !encode(true).contains(":unsafe-seminaive"),
                "`force_proof_naive` left `:unsafe-seminaive` in {file}, so the \
                 comparison does not cover those rules"
            );

            // `print-size` summarizes the whole database (per-function row
            // counts, sorted) deterministically.
            let program = format!("{source}\n(print-size)");

            let run = |naive: bool| -> Vec<CommandOutput> {
                let mut egraph = crate::EGraph::new_with_proofs();
                egraph.proof_state.force_proof_naive = naive;
                egraph
                    .parse_and_run_program(Some(file.to_string()), &program)
                    .unwrap_or_else(|e| panic!("{file} (naive={naive}) failed: {e}"))
            };

            let unsafe_seminaive = CommandOutput::snapshot_stable_under_proof_encoding(&run(false));
            let naive = CommandOutput::snapshot_stable_under_proof_encoding(&run(true));

            assert_eq!(
                unsafe_seminaive, naive,
                ":unsafe-seminaive and :naive proof encodings disagree for {file}"
            );
        }
    }

    /// A user rule marked `:naive` must stay `:naive` through proof encoding;
    /// dropping it would silently switch the rule to seminaive evaluation.
    #[test]
    fn proof_encoding_preserves_naive() {
        // The second case binds an eq-sort body var, whose `term_proof` RHS
        // read would otherwise force `:unsafe-seminaive`. Both must stay naive.
        let cases = [
            r#"(relation r (i64))
               (relation s (i64))
               (rule ((r x)) ((s x)) :naive :name "keep")"#,
            r#"(sort Math)
               (constructor Num (i64) Math)
               (constructor Neg (Math) Math)
               (relation seen (Math))
               (rule ((Neg m)) ((seen m)) :naive :name "keep")"#,
        ];
        for source in cases {
            let mut egraph = crate::EGraph::new_with_proofs();
            let resolved = egraph.resolve_program(None, source).unwrap();
            let rule = resolved
                .iter()
                .find_map(|c| match c {
                    ResolvedCommand::Rule { rule } if rule.name == "keep" => Some(rule),
                    _ => None,
                })
                .expect("instrumented rule not found");
            assert_eq!(
                rule.eval_mode,
                RuleEvalMode::Naive,
                "proof encoding did not preserve :naive for:\n{source}"
            );
        }
    }

    #[test]
    fn proof_encoding_hoists_unnamed_rule_name_in_actions() {
        let source = r#"
            (datatype VeryLongExpressionForRuleNameHoisting
              (VeryLongLeafConstructorForRuleNameHoisting i64)
              (VeryLongUnaryConstructorForRuleNameHoisting VeryLongExpressionForRuleNameHoisting)
              (VeryLongBinaryConstructorForRuleNameHoisting
                VeryLongExpressionForRuleNameHoisting
                VeryLongExpressionForRuleNameHoisting))
            (relation VeryLongSeedRelationForRuleNameHoisting
              (VeryLongExpressionForRuleNameHoisting))

            (VeryLongSeedRelationForRuleNameHoisting
              (VeryLongLeafConstructorForRuleNameHoisting 1))

            (rule
              ((VeryLongSeedRelationForRuleNameHoisting original))
              ((let wrapped
                 (VeryLongUnaryConstructorForRuleNameHoisting original))
               (let paired
                 (VeryLongBinaryConstructorForRuleNameHoisting wrapped original))
               (union wrapped paired)))

            (run 1)
            (prove
              (= (VeryLongUnaryConstructorForRuleNameHoisting
                   (VeryLongLeafConstructorForRuleNameHoisting 1))
                 (VeryLongBinaryConstructorForRuleNameHoisting
                   (VeryLongUnaryConstructorForRuleNameHoisting
                     (VeryLongLeafConstructorForRuleNameHoisting 1))
                   (VeryLongLeafConstructorForRuleNameHoisting 1))))
        "#;

        let mut egraph = EGraph::new_with_proofs();
        let commands = egraph.resolve_program(None, source).unwrap();
        // Only the rows carrying premises inline name the rule; a later site's
        // link reads the name off the row it chains onto.
        let names = &egraph.proof_state.proof_names;
        let rule_constructors: HashSet<String> = names
            .rule_fused_declared
            .iter()
            .map(|arity| names.fused_rule(*arity))
            .collect();
        let rule = commands
            .iter()
            .find_map(|command| match command {
                ResolvedCommand::Rule { rule }
                    if rule
                        .name
                        .contains("VeryLongSeedRelationForRuleNameHoisting") =>
                {
                    Some(rule)
                }
                _ => None,
            })
            .expect("instrumented unnamed rule not found");
        assert!(
            rule.name.len() > 256,
            "expected a long synthesized rule name"
        );

        let rule_name_vars = rule
            .head
            .0
            .iter()
            .filter_map(|action| match action {
                ResolvedAction::Let(_, var, ResolvedExpr::Lit(_, Literal::String(value)))
                    if value == &rule.name =>
                {
                    Some(var.name.as_str())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            rule_name_vars.len(),
            1,
            "the synthesized rule name should be bound once in the actions"
        );
        let rule_name_var = rule_name_vars[0];

        // Proof constructors are relations, so each rule proof is emitted as a
        // `(set (@Rule_1 <rule-name> <premise> <site> <id>) ())` action — the rule
        // has one body fact — not a call expression. Count those set actions and
        // check they reuse the hoisted rule-name variable as their first argument.
        let rule_uses = rule
            .head
            .0
            .iter()
            .filter(|action| match action {
                ResolvedAction::Set(_, ResolvedCall::Func(func), args, _)
                    if rule_constructors.contains(&func.name) =>
                {
                    assert!(
                        matches!(
                            args.first(),
                            Some(ResolvedExpr::Var(_, var)) if var.name == rule_name_var
                        ),
                        "generated Rule constructor did not reuse the rule-name variable"
                    );
                    true
                }
                _ => false,
            })
            .count();
        assert!(
            rule_uses > 1,
            "expected the multi-action rule to emit multiple Rule constructors"
        );

        EGraph::new_with_proofs()
            .parse_and_run_program(None, source)
            .expect("hoisted rule-name proof should pass the checker");
    }

    /// A rule proof carries its premises inline, in a constructor declared per
    /// premise count ahead of the program that needs it. A program run in pieces
    /// must therefore declare the arities each piece introduces, not just the
    /// first.
    #[test]
    fn rule_premise_arities_are_declared_per_program() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Math (Add Math Math) (Num i64))
                 (rewrite (Add a b) (Add b a))",
            )
            .unwrap();
        assert!(
            !egraph
                .proof_state
                .proof_names
                .rule_fused_declared
                .contains(&2),
            "the first program has no two-premise rule, so it must not declare that arity"
        );
        // Two body facts, so a premise count the first program never declared.
        egraph
            .parse_and_run_program(
                None,
                "(relation Seed (Math))
                 (rule ((Seed x) (= x (Add a b))) ((union x (Add b (Add a b)))))
                 (Seed (Add (Num 1) (Num 2)))
                 (run 2)
                 (prove (= (Add (Num 1) (Num 2))
                           (Add (Num 2) (Add (Num 1) (Num 2)))))",
            )
            .unwrap();
        assert!(
            egraph
                .proof_state
                .proof_names
                .rule_fused_declared
                .contains(&2),
            "the second program's two-premise rule should have declared that arity"
        );
    }

    /// The encoder records one premise per body fact of the rule *after*
    /// `remove_globals` appends a lookup fact per global the head mentions, while
    /// the proof checker replays the rule as written, without those facts. Proof
    /// conversion pairs premises with written facts by position, so the premise
    /// count must cover the written body — the extras are exactly the trailing
    /// ones.
    #[test]
    fn rule_premises_cover_the_written_body_facts() {
        let source = r#"
            (datatype Math (Add Math Math) (Num i64))
            (relation Seen (Math))
            (let g (Num 7))
            ;; One written body fact, and a head that reads a global.
            (rule ((Seen x)) ((Seen (Add x g))) :name "with_global")
            ;; Two written body facts and no global.
            (rule ((Seen x) (= x (Add a b))) ((Seen a)) :name "without_global")
            (Seen (Num 1))
            (run 2)
            (prove (Seen (Add (Num 1) (Num 7))))
        "#;

        // The rules as the checker replays them: before `remove_globals`.
        let mut checker = EGraph::new_with_proofs();
        checker.parse_and_run_program(None, source).unwrap();
        let written: HashMap<String, usize> = checker
            .proof_check_program
            .iter()
            .filter_map(|cmd| match cmd {
                GenericNCommand::NormRule { rule } => Some((rule.name.clone(), rule.body.len())),
                _ => None,
            })
            .collect();

        // The rules as the encoder emits them: the premise count is the arity of
        // the `Rule_<k>` constructor each head writes.
        let mut encoder = EGraph::new_with_proofs();
        let commands = encoder.resolve_program(None, source).unwrap();
        let names = encoder.proof_state.proof_names.clone();
        let mut recorded: HashMap<String, usize> = HashMap::default();
        for command in &commands {
            let ResolvedCommand::Rule { rule } = command else {
                continue;
            };
            if !written.contains_key(&rule.name) {
                continue;
            }
            let premises = rule
                .head
                .0
                .iter()
                .filter_map(|action| match action {
                    ResolvedAction::Set(_, ResolvedCall::Func(func), _, _) => {
                        names.fused_rule_arity(&func.name)
                    }
                    _ => None,
                })
                .max()
                .unwrap_or_else(|| panic!("rule '{}' wrote no inline rule proof", rule.name));
            recorded.insert(rule.name.clone(), premises);
        }

        // Holds for every rule the checker replays, including the one `prove`
        // generates.
        for (name, premises) in &recorded {
            let facts = written[name];
            assert!(
                *premises >= facts,
                "rule '{name}' recorded {premises} premises for a body of {facts} written facts"
            );
        }
        // Pin both sides of the inequality, so neither half can drift unnoticed:
        // the global reference adds exactly one trailing lookup fact, and a rule
        // without one records exactly its written facts.
        assert_eq!(
            recorded.get("with_global").copied(),
            Some(written["with_global"] + 1),
            "a head reading a global should record one extra premise"
        );
        assert_eq!(
            recorded.get("without_global").copied(),
            Some(written["without_global"]),
            "a rule mentioning no global should record one premise per written fact"
        );
    }

    #[test]
    fn proof_mode_allows_eq_sort_primitive_results_in_facts() {
        let mut egraph = EGraph::default();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-id" = |x: #| -> # { x },
            validator
        );
        let mut egraph = egraph.with_proofs_enabled();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math
                  (Done)
                  (Num i64))
                (relation Seed (Math))

                (Seed (Num 1))

                (rule ((Seed y)
                       (= x (proof-id y)))
                      ((Done))
                      :name "use-proof-id")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    #[test]
    fn proof_support_rejects_naive_eq_sort_primitive_results_in_facts() {
        let mut egraph = EGraph::default();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-id" = |x: #| -> # { x },
            validator
        );
        let mut egraph = egraph.with_proofs_enabled();

        let err = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math
                  (Done)
                  (Num i64))
                (relation Seed (Math))

                (rule ((Seed y)
                       (= x (proof-id y)))
                      ((Done))
                      :naive
                      :name "naive-use-proof-id")
                "#,
            )
            .unwrap_err();

        assert!(
            matches!(
                err,
                Error::UnsupportedProofCommand {
                    reason: ProofEncodingUnsupportedReason::NaiveEqSortPrimitiveFact,
                    ..
                }
            ),
            "expected NaiveEqSortPrimitiveFact, got {err:?}"
        );
    }

    #[test]
    fn proof_mode_allows_eq_container_primitive_results_in_facts() {
        // A real (presort-declared) eq-container sort, so the term/proof
        // encoding builds its rebuild primitive. A custom identity primitive
        // returns an existing eq-container value, exercising the
        // eq-container-primitive-result-in-a-fact path under proofs.
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                "#,
            )
            .unwrap();

        let eq_container_sort = egraph
            .type_info
            .get_sort_by_name("EqContainer")
            .expect("EqContainer sort")
            .clone();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-container-id" = |x: # (eq_container_sort)| -> # (eq_container_sort) { x },
            validator
        );

        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation SeedContainer (EqContainer))
                (relation Done ())

                (SeedContainer (vec-of (Mk)))

                (rule ((SeedContainer ys)
                       (= xs (proof-container-id ys)))
                      ((Done))
                      :name "use-proof-container-id")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    #[test]
    #[should_panic(expected = "Primitive 'proof-container-reject' validation failed")]
    fn proof_checker_validates_container_primitive_facts() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                "#,
            )
            .unwrap();

        let eq_container_sort = egraph
            .type_info
            .get_sort_by_name("EqContainer")
            .expect("EqContainer sort")
            .clone();
        let validator = |_: &mut TermDag, _: &[TermId]| -> Option<TermId> { None };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-container-reject" = |x: # (eq_container_sort)| -> # (eq_container_sort) { x },
            validator
        );

        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation SeedContainer (EqContainer))
                (relation Done ())

                (SeedContainer (vec-of (Mk)))

                (rule ((SeedContainer ys)
                       (proof-container-reject ys))
                      ((Done))
                      :name "reject-invalid-container-fact")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    #[test]
    fn proof_extraction_skips_container_primitive_validation() {
        let mut egraph = EGraph::default().with_proof_extraction();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                "#,
            )
            .unwrap();

        let eq_container_sort = egraph
            .type_info
            .get_sort_by_name("EqContainer")
            .expect("EqContainer sort")
            .clone();
        let validator = |_: &mut TermDag, _: &[TermId]| -> Option<TermId> { None };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-container-reject" = |x: # (eq_container_sort)| -> # (eq_container_sort) { x },
            validator
        );

        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (relation SeedContainer (EqContainer))
                (relation Done ())

                (SeedContainer (vec-of (Mk)))

                (rule ((SeedContainer ys)
                       (proof-container-reject ys))
                      ((Done))
                      :name "reject-invalid-container-fact")

                (run 1)
                (check (Done))
                "#,
            )
            .unwrap();
        assert!(
            outputs
                .iter()
                .any(|output| matches!(output, CommandOutput::ProveExists { .. }))
        );
    }

    #[test]
    fn proof_extraction_still_rejects_a_false_check() {
        let error = EGraph::default()
            .with_proof_extraction()
            .parse_and_run_program(
                None,
                r#"
                (relation Done ())
                (check (Done))
                "#,
            )
            .unwrap_err();

        assert!(
            matches!(
                error,
                Error::ProofError {
                    error: ProveExistsError::QueryDidNotMatch { .. },
                    ..
                }
            ),
            "expected QueryDidNotMatch, got {error:?}"
        );
    }

    // A container constructed in the query body and not used in an action: the
    // binding fact's proof is the container's reflexive `Eval`, which the rule
    // check re-derives with the typed primitive.
    #[test]
    fn proof_mode_query_constructed_container_not_used_in_action() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                (relation SeedElem (E))
                (relation Done ())

                (SeedElem (Mk))

                (rule ((SeedElem e)
                       (= xs (vec-of e)))
                      ((Done))
                      :name "new-container-in-body")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    // A container constructed in the query is a side condition with no carryable
    // proof (just an `Eval` marker), so it can't be used in an action. Proof mode
    // rejects such a rule rather than producing an unsound proof.
    #[test]
    fn proof_support_rejects_query_constructed_container_used_in_action() {
        let mut egraph = EGraph::new_with_proofs();
        let err = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                (relation SeedElem (E))
                (relation Out (EqContainer))

                (rule ((SeedElem e)
                       (= xs (vec-of e)))
                      ((Out xs))
                      :name "new-container-in-action")
                "#,
            )
            .unwrap_err();
        assert!(
            matches!(
                err,
                Error::UnsupportedProofCommand {
                    reason: ProofEncodingUnsupportedReason::ContainerCreatedInQueryUsedInAction,
                    ..
                }
            ),
            "expected ContainerCreatedInQueryUsedInAction, got {err:?}"
        );
    }

    #[test]
    fn doc_example_add_function2() {
        let commands = term_encode(
            r#"
            (function add (i64 i64) i64 :merge old)
            (check (= (add 0 0) 0))
            "#,
        );

        let snapshot = sanitize_internal_names(&commands)
            .iter()
            .map(|cmd| cmd.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        insta::assert_snapshot!("doc_example_add_function2", snapshot);
    }

    #[test]
    fn doc_example_add_function1() {
        let commands = term_encode(
            r#"
(sort Math)
(constructor Add (i64 i64) Math)
(Add 1 2)
(rule ((Add a b))
      ((union (Add a b) (Add b a)))
     :name "commutativity")
(check (= (Add 1 2) (Add 2 1)))
            "#,
        );

        let snapshot = sanitize_internal_names(&commands)
            .iter()
            .map(|cmd| cmd.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        insta::assert_snapshot!("doc_example_add_function1", snapshot);
    }
}
