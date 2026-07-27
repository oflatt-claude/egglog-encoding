//! Maintenance-rule generation for the term/proof encoding: the rebuild rules
//! that keep each function's view and subsumed tables canonical, plus the rules
//! that execute requested deletes/subsumptions. (`@UF` path compression stays
//! in [`super::proof_encoding`].)

use super::proof_encoding::{ProofInstrumentor, Stmts, ViewIndex};
use crate::typechecking::FuncType;
use crate::*;

/// How a maintenance-rebuild rule is evaluated.
///
/// `EncodingState::force_proof_naive` does not apply to these rules. It swaps an
/// RHS-reading rule for a `:naive` equivalent so tests can compare the two, which
/// only holds for a rule that does not write the tables its own body joins. A
/// rebuild rule re-keys the very view and index rows it matches, so its `:naive`
/// form stops after one pass per match instead of iterating that feedback to a
/// fixpoint, and the two forms saturate at different databases.
enum RebuildEval {
    /// The rule's body sees every atom it depends on.
    Seminaive,
    /// A primitive in the rule reads `@UF` tables the body does not join on, and
    /// no delta on them drives the rule.
    Naive,
    /// A primitive in the rule's *action* reads `@UF`, but the body joins the
    /// driving `@UF` delta, which makes that read sound.
    UnsafeSeminaive,
}

/// Which FD-view value column [`ProofInstrumentor::fd_value_rebuild_rule`] rebuilds.
enum ValueRebuild {
    /// The value is the term's e-class (constructors and globals).
    Eclass,
    /// A custom function's eq-sort output at child index `out_idx`.
    CustomOutput { out_idx: usize },
    /// A custom function's eq-container output at child index `out_idx`,
    /// canonicalized by the container rebuild primitive (containers have no
    /// `@UF` to chase).
    ContainerOutput { out_idx: usize },
}

impl ProofInstrumentor<'_> {
    /// Rules that execute deletion and subsumption based on the tables requesting the deletion/subsumption.
    pub(super) fn delete_and_subsume(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
        let child_vars: Vec<String> = (0..fdecl.schema.input.len())
            .map(|i| format!("c{i}_"))
            .collect();
        let child_names = child_vars.join(" ");
        let to_delete_name = self.delete_name(&fdecl.name);
        let subsumed_name = self.subsumed_name(&fdecl.name);
        let view_name = self.view_name(&fdecl.name);
        let delete_subsume_ruleset = self.proof_names().delete_subsume_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("delete_rule");

        // The view is keyed by children only, so match its value tuple to
        // delete/subsume by key (the bridge re-reads every value column when
        // subsuming a tuple-output view). Deletion removes the row by key, taking
        // its rebuild-index entries with it; subsumption keeps the row (excluded
        // from matching but retained for size/proofs), so the index is untouched.
        let e = self.fresh_var();
        let pf = self.fresh_var();
        let e2 = self.fresh_var();
        let pf2 = self.fresh_var();
        let index_deletes = self.view_index_deletes(&fdecl.name, &child_vars);
        format!(
            "(rule (({to_delete_name} {child_names})
                    (= (values {e} {pf}) ({view_name} {child_names})))
                   ((delete ({view_name} {child_names}))
                    {index_deletes}
                    (delete ({to_delete_name} {child_names})))
                    :ruleset {delete_subsume_ruleset}
                    :name \"{fresh_name}\")
             (rule (({subsumed_name} {child_names})
                    (= (values {e2} {pf2}) ({view_name} {child_names})))
                   ((subsume ({view_name} {child_names})))
                    :ruleset {delete_subsume_ruleset}
                    :name \"{fresh_name}_subsume\")"
        )
    }

    /// Wrap one maintenance-rebuild rule (`facts` -> `actions`) with the rebuilding
    /// ruleset, a fresh name, and `:internal-include-subsumed` (so stale rows are
    /// rebuilt too).
    fn rebuild_rule(&mut self, facts: &str, actions: &str, eval: RebuildEval) -> String {
        let ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        let eval = match eval {
            RebuildEval::Seminaive => "",
            RebuildEval::Naive => ":naive ",
            RebuildEval::UnsafeSeminaive => ":unsafe-seminaive ",
        };
        format!(
            "(rule ({facts})\n     ({actions})\n     :ruleset {ruleset} {eval}:name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
    }

    /// Rebuild rules that keep a view canonical, plus a rule for the FD view's
    /// value column.
    ///
    /// The view's eq-sort children are canonicalized by one rule per distinct
    /// child eq-sort ([`Self::eq_sort_rebuild_rule`]), driven by an `@UF` delta
    /// joined against that sort's rebuild index. Container children keep a
    /// per-column `:naive` rule ([`Self::container_child_rebuild_rule`]): a
    /// container has no `@UF` row to drive a rule, and its rebuild primitive
    /// reads `@UF` tables the body does not join on. The value column is
    /// canonicalized by [`Self::fd_value_rebuild_rule`].
    ///
    /// A child update re-keys the row (`set` at the canonicalized children, then
    /// `delete`, index entries following the row); a collision on the new key runs
    /// the view's `:merge`. In proof mode each rule composes the updated view
    /// proof, and a container update records the rebuilt container's `<CSort>Proof`.
    pub(super) fn rebuilding_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        // A global's output *is* its e-class (like a constructor's), so it takes the
        // e-class rebuild below (union-tracking) — not the custom-output rebuild
        // (congruence), which would emit a nonsensical `Congr` on its nullary term.
        let output_is_eclass = self.output_is_eclass(fdecl);
        let types = fdecl.resolved_schema.view_types();
        let n = types.len();
        let child = |i: usize| format!("c{i}_");
        // Key columns of the view row: the children (the value tuple is unkeyed).
        let n_keys = n - 1;
        let key_vars: Vec<String> = (0..n_keys).map(child).collect();

        let mut rules = String::new();
        for (i, ty) in types[..n_keys].iter().enumerate() {
            if ty.is_eq_container_sort() {
                rules.push_str(&self.container_child_rebuild_rule(fdecl, &key_vars, i, ty));
            }
        }
        let indexes = self
            .egraph
            .proof_state
            .view_index
            .get(&fdecl.name)
            .cloned()
            .unwrap_or_default();
        for vi in &indexes {
            rules.push_str(&self.eq_sort_rebuild_rule(fdecl, &key_vars, &types, vi));
        }
        // FD view value column (see [`Self::fd_value_rebuild_rule`]). A
        // constructor/global's value *is* its e-class; a custom function's
        // eq-sort or eq-container output takes the delete-then-reinsert path.
        // A base-sort custom output never goes stale, so nothing is emitted.
        if output_is_eclass {
            rules.push_str(&self.fd_value_rebuild_rule(fdecl, &key_vars, ValueRebuild::Eclass));
        } else if fdecl.subtype == FunctionSubtype::Custom && !self.is_encoded_global(fdecl) {
            if types[n - 1].is_eq_sort() {
                rules.push_str(&self.fd_value_rebuild_rule(
                    fdecl,
                    &key_vars,
                    ValueRebuild::CustomOutput { out_idx: n - 1 },
                ));
            } else if types[n - 1].is_eq_container_sort() {
                rules.push_str(&self.fd_value_rebuild_rule(
                    fdecl,
                    &key_vars,
                    ValueRebuild::ContainerOutput { out_idx: n - 1 },
                ));
            }
        }
        self.parse_program(&rules)
    }

    /// The `:naive` per-column rebuild for a container child at key position `i`:
    /// rebuild the container with its primitive, then re-key the row (`set` at the
    /// rebuilt children, `delete` the old key) and move the row's index entries
    /// with it. In proof mode the row proof gains a `Congr` at position `i` and
    /// the rebuilt container gets its reflexive `<CSort>Proof` anchor.
    fn container_child_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        i: usize,
        ty: &ArcSort,
    ) -> String {
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(key_vars, " "));
        let index_deletes = self.view_index_deletes(&fdecl.name, key_vars);
        let ci = &key_vars[i];
        let canon = format!("c{i}_canon_");
        let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, key_vars);
        let value_prim = self.container_rebuild_prim(ty);
        let canon_fact = format!("(= {canon} ({value_prim} {ci}))");
        let (proof_lets, pf_arg, cproof_set) = if self.proofs_enabled() {
            let congr = self.proof_names().congr_constructor.clone();
            let trans = self.proof_names().eq_trans_constructor.clone();
            let sym = self.proof_names().eq_sym_constructor.clone();
            let proof_sort = self.proof_sort();
            let proof_prim = self.container_rebuild_proof_prim(ty);
            let rebuild_pf = self.fresh_var();
            let cproof = self.term_proof_name(ty.name());
            // proof_lets: bind the container rebuild proof, then mint the congr proof.
            let mut lets = Stmts::new();
            lets.push(format!("(let {rebuild_pf} ({proof_prim} {ci}))"));
            let new_pf = self.mint(
                &mut lets,
                &congr,
                &format!("{view_prf} {i} {rebuild_pf}"),
                &proof_sort,
            );
            // cproof_set: mint (Sym rebuild_pf), (Trans .. rebuild_pf), then record it.
            let mut cproof_stmts = Stmts::new();
            let sym_pf = self.mint(&mut cproof_stmts, &sym, &rebuild_pf, &proof_sort);
            let trans_pf = self.mint(
                &mut cproof_stmts,
                &trans,
                &format!("{sym_pf} {rebuild_pf}"),
                &proof_sort,
            );
            cproof_stmts.push(format!("(set ({cproof} {canon}) {trans_pf})"));
            (
                lets.join("\n                      "),
                new_pf,
                cproof_stmts.join("\n                      "),
            )
        } else {
            (String::new(), "()".to_string(), String::new())
        };
        let mut updated = key_vars.to_vec();
        updated[i] = canon.clone();
        let updated_view = self.update_fd_view(&fdecl.name, &updated, &value_var, &pf_arg);
        let facts = format!("{query_view}\n{canon_fact}\n(!= {ci} {canon})");
        let actions = format!(
            "{proof_lets}\n{updated_view}\n{cproof_set}\n(delete ({view_name} {keys_str}))\n{index_deletes}"
        );
        self.rebuild_rule(&facts, &actions, RebuildEval::Naive)
    }

    /// The single rule that canonicalizes every eq-sort child of a view row, for
    /// the child sort `vi` indexes.
    ///
    /// An `@UF_<S>` edge on some term is joined against `vi`'s index to reach the
    /// rows mentioning that term by key lookup — the same access pattern a native
    /// rebuild uses when it walks the e-nodes referencing a changed e-class. The
    /// action then re-canonicalizes *all* the row's eq-sort children with
    /// `uf_canon`, so one firing fixes the whole row rather than one column of it.
    /// In proof mode it folds one `@Congr` per eq-sort child onto the row proof;
    /// the steps for children that did not move are reflexive and collapse in the
    /// proof simplifier.
    fn eq_sort_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        types: &[ArcSort],
        vi: &ViewIndex,
    ) -> String {
        let proofs = self.proofs_enabled();
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(key_vars, " "));
        let index_deletes = self.view_index_deletes(&fdecl.name, key_vars);

        // Body: an `@UF_<S>` edge on the referenced term, the index entry naming a
        // row that mentions it, and that row's value tuple.
        let follower = self.fresh_var();
        let leader = self.fresh_var();
        let leader_pf = self.fresh_var();
        let uf_name = self.uf_name(&vi.sort_name);
        let uf_atom = format!("(= (values {leader} {leader_pf}) ({uf_name} {follower}))");
        let index_atom = format!("({} {follower} {keys_str})", vi.name);
        let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, key_vars);

        // Action: canonicalize every eq-sort key column, folding its congruence
        // step onto the row proof. Other columns carry over unchanged.
        let mut lets = Stmts::new();
        let mut updated = key_vars.to_vec();
        let mut proof_acc = view_prf;
        for j in 0..key_vars.len() {
            if !types[j].is_eq_sort() || types[j].is_eq_container_sort() {
                continue;
            }
            let canon = format!("c{j}_canon_");
            let cj = &key_vars[j];
            let uf_j = self.uf_name(types[j].name());
            let canon_prim = crate::proofs::proof_container_rebuild::uf_canon_prim_name(&uf_j);
            // Fallback `cj`: a child with no `@UF` row is already a root.
            lets.push(format!("(let {canon} ({canon_prim} {cj} {cj}))"));
            if proofs {
                let proof_prim =
                    crate::proofs::proof_container_rebuild::uf_canon_proof_prim_name(&uf_j);
                let congr = self.proof_names().congr_constructor.clone();
                let proof_sort = self.proof_sort();
                // Fallback: the reflexive `cj = cj`, anchored when `cj` was built.
                let term_proof = self.term_proof_name(types[j].name());
                let refl_pf = self.fresh_var();
                let step_pf = self.fresh_var();
                lets.push(format!("(let {refl_pf} ({term_proof} {cj}))"));
                lets.push(format!("(let {step_pf} ({proof_prim} {cj} {refl_pf}))"));
                proof_acc = self.mint(
                    &mut lets,
                    &congr,
                    &format!("{proof_acc} {j} {step_pf}"),
                    &proof_sort,
                );
            }
            updated[j] = canon;
        }
        let pf_arg = if proofs { proof_acc } else { "()".to_string() };
        let updated_view = self.update_fd_view(&fdecl.name, &updated, &value_var, &pf_arg);
        let facts = format!("{uf_atom}\n(!= {follower} {leader})\n{index_atom}\n{query_view}");
        let actions = format!(
            "{}\n{updated_view}\n(delete ({view_name} {keys_str}))\n{index_deletes}",
            lets.join("\n                      ")
        );
        self.rebuild_rule(&facts, &actions, RebuildEval::UnsafeSeminaive)
    }

    /// One rule that canonicalizes an FD view's stale value column.
    ///
    /// * [`ValueRebuild::Eclass`] (constructors/globals): the value *is* the
    ///   e-class, so re-`set` the same key and let the congruence `:merge` keep the
    ///   min. The row proof `canon = f(children)` is `Trans(Sym(key = leader), key =
    ///   f(children))`.
    /// * [`ValueRebuild::CustomOutput`] (a custom function's eq-sort output):
    ///   `delete` the stale row first, so the re-`set` inserts without re-running
    ///   the user merge. The row proof rewrites the output child by `Congr` at its
    ///   position.
    /// * [`ValueRebuild::ContainerOutput`] (a custom function's eq-container
    ///   output): like `CustomOutput`, but the value canonicalizes via the
    ///   container rebuild primitive (`:naive` — it reads `@UF` tables the rule
    ///   doesn't join on), and the rebuilt container gets a reflexive
    ///   `<CSort>Proof` anchor for later rebuilds.
    fn fd_value_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        kind: ValueRebuild,
    ) -> String {
        if let ValueRebuild::ContainerOutput { out_idx } = kind {
            return self.fd_container_value_rebuild_rule(fdecl, key_vars, out_idx);
        }
        let value_uf_name = self.uf_name(fdecl.resolved_schema.output().name());
        let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, key_vars);
        let canon = self.fresh_var();
        let uf_prf = self.fresh_var();
        let (proof_lets, pf_arg) = if self.proofs_enabled() {
            let proof_sort = self.proof_sort();
            let mut lets = Stmts::new();
            let pf = match kind {
                ValueRebuild::Eclass => {
                    let sym = self.proof_names().eq_sym_constructor.clone();
                    let trans = self.proof_names().eq_trans_constructor.clone();
                    let sym_pf = self.mint(&mut lets, &sym, &uf_prf, &proof_sort);
                    self.mint(
                        &mut lets,
                        &trans,
                        &format!("{sym_pf} {view_prf}"),
                        &proof_sort,
                    )
                }
                ValueRebuild::CustomOutput { out_idx } => {
                    let congr = self.proof_names().congr_constructor.clone();
                    self.mint(
                        &mut lets,
                        &congr,
                        &format!("{view_prf} {out_idx} {uf_prf}"),
                        &proof_sort,
                    )
                }
                ValueRebuild::ContainerOutput { .. } => unreachable!("handled above"),
            };
            (lets.join("\n                      "), pf)
        } else {
            (String::new(), "()".to_string())
        };
        let set_canon = self.update_fd_view(&fdecl.name, key_vars, &canon, &pf_arg);
        let actions = match kind {
            ValueRebuild::Eclass => format!("{proof_lets}\n{set_canon}"),
            ValueRebuild::CustomOutput { .. } => {
                let view_name = self.view_name(&fdecl.name);
                let keys_str = ListDisplay(key_vars, " ").to_string();
                format!("{proof_lets}\n(delete ({view_name} {keys_str}))\n{set_canon}")
            }
            ValueRebuild::ContainerOutput { .. } => unreachable!("handled above"),
        };
        let facts = format!(
            "{query_view}\n(= (values {canon} {uf_prf}) ({value_uf_name} {value_var}))\n(!= {value_var} {canon})"
        );
        self.rebuild_rule(&facts, &actions, RebuildEval::Seminaive)
    }

    /// The [`ValueRebuild::ContainerOutput`] arm of
    /// [`Self::fd_value_rebuild_rule`]: canonicalize a custom function's
    /// container-valued output with the container rebuild primitive,
    /// delete-then-reinsert the row (dodging the user merge), and in proof mode
    /// compose the row proof with a `Congr` at the output position and anchor
    /// the rebuilt container's reflexive `<CSort>Proof`.
    fn fd_container_value_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        out_idx: usize,
    ) -> String {
        let out_ty = fdecl.resolved_schema.output().clone();
        let value_prim = self.container_rebuild_prim(&out_ty);
        let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, key_vars);
        let canon = self.fresh_var();
        let canon_fact = format!("(= {canon} ({value_prim} {value_var}))");
        let (proof_lets, pf_arg, cproof_set) = if self.proofs_enabled() {
            let congr = self.proof_names().congr_constructor.clone();
            let trans = self.proof_names().eq_trans_constructor.clone();
            let sym = self.proof_names().eq_sym_constructor.clone();
            let proof_sort = self.proof_sort();
            let proof_prim = self.container_rebuild_proof_prim(&out_ty);
            let rebuild_pf = self.fresh_var();
            let cproof = self.term_proof_name(out_ty.name());
            let mut lets = Stmts::new();
            lets.push(format!("(let {rebuild_pf} ({proof_prim} {value_var}))"));
            let new_pf = self.mint(
                &mut lets,
                &congr,
                &format!("{view_prf} {out_idx} {rebuild_pf}"),
                &proof_sort,
            );
            let mut cproof_stmts = Stmts::new();
            let sym_pf = self.mint(&mut cproof_stmts, &sym, &rebuild_pf, &proof_sort);
            let trans_pf = self.mint(
                &mut cproof_stmts,
                &trans,
                &format!("{sym_pf} {rebuild_pf}"),
                &proof_sort,
            );
            cproof_stmts.push(format!("(set ({cproof} {canon}) {trans_pf})"));
            (
                lets.join("\n                      "),
                new_pf,
                cproof_stmts.join("\n                      "),
            )
        } else {
            (String::new(), "()".to_string(), String::new())
        };
        let set_canon = self.update_fd_view(&fdecl.name, key_vars, &canon, &pf_arg);
        let view_name = self.view_name(&fdecl.name);
        let keys_str = ListDisplay(key_vars, " ").to_string();
        let facts = format!("{query_view}\n{canon_fact}\n(!= {value_var} {canon})");
        let actions =
            format!("{proof_lets}\n(delete ({view_name} {keys_str}))\n{set_canon}\n{cproof_set}");
        self.rebuild_rule(&facts, &actions, RebuildEval::Naive)
    }

    /// Rules that update the to_subsume tables when children change. One rule per
    /// eq-sort child (no proof needed for subsumed rows).
    pub(super) fn rebuilding_subsumed_rules(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
    ) -> Vec<Command> {
        let ResolvedCall::Func(FuncType { input, .. }) = &fdecl.resolved_schema else {
            panic!("cannot create subsumed rules for primitives")
        };

        // Check if there are any eq-sort columns at all; if not, no rebuild rule needed.
        if !input.iter().any(|t| t.is_eq_sort()) {
            return vec![];
        }

        self.rebuilding_subsumed_rules_fanout(fdecl, input.clone())
    }

    /// Subsumed-table rebuild: one rule per eq-sort column, mirroring
    /// [`Self::rebuilding_rules`] (the single-key `@UF` has no row for a
    /// canonical node, so a per-column lookup only fires when there is work).
    /// The `@UF` proof column is unused for subsumed rows.
    fn rebuilding_subsumed_rules_fanout(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        input: Vec<ArcSort>,
    ) -> Vec<Command> {
        let subsumed_name = self.subsumed_name(&fdecl.name);
        let child = |i: usize| format!("c{i}_");
        let children_vec: Vec<String> = (0..input.len()).map(child).collect();
        let children = format!("{}", ListDisplay(&children_vec, " "));
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();

        let mut rules = String::new();
        for (i, ty) in input.iter().enumerate() {
            if !ty.is_eq_sort() {
                continue;
            }
            let ci = child(i);
            let leader = format!("c{i}_leader_");
            let uf_name = self.uf_name(ty.name());
            let uf_lookup = {
                let proof_var = self.fresh_var();
                format!("(= (values {leader} {proof_var}) ({uf_name} {ci}))")
            };
            let mut updated = children_vec.clone();
            updated[i] = leader.clone();
            let updated_view = ListDisplay(&updated, " ");
            let fresh_name = self
                .egraph
                .parser
                .symbol_gen
                .fresh("rebuild_to_subsume_rule");
            rules.push_str(&format!(
                "(rule (({subsumed_name} {children})
                        {uf_lookup}
                        (!= {ci} {leader}))
                     (
                      (set ({subsumed_name} {updated_view}) ())
                      (delete ({subsumed_name} {children}))
                     )
                      :ruleset {rebuilding_ruleset} :name \"{fresh_name}\" :internal-include-subsumed)\n"
            ));
        }
        self.parse_program(&rules)
    }
}
