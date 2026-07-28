//! Maintenance-rule generation for the term/proof encoding: the rebuild rules
//! that keep each function's view and subsumed tables canonical, plus the rules
//! that execute requested deletes/subsumptions. (`@UF` path compression stays
//! in [`super::proof_encoding`].)

use super::proof_encoding::{ProofInstrumentor, ViewIndex};
use crate::typechecking::FuncType;
use crate::*;

/// Which FD-view value column [`ProofInstrumentor::fd_value_rebuild_rule`] rebuilds.
enum ValueRebuild {
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
        let child_names = fdecl
            .schema
            .input
            .iter()
            .enumerate()
            .map(|(i, _)| format!("c{i}_"))
            .collect::<Vec<_>>()
            .join(" ");
        let to_delete_name = self.delete_name(&fdecl.name);
        let subsumed_name = self.subsumed_name(&fdecl.name);
        let view_name = self.view_name(&fdecl.name);
        let delete_subsume_ruleset = self.proof_names().delete_subsume_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("delete_rule");

        // The view is keyed by children only, so match its value tuple to
        // delete/subsume by key (the bridge re-reads every value column when
        // subsuming a tuple-output view). Deletion removes the row by key;
        // subsumption marks it subsumed (kept for size/proofs but excluded from
        // matching).
        let e = self.fresh_var();
        let pf = self.fresh_var();
        let e2 = self.fresh_var();
        let pf2 = self.fresh_var();
        format!(
            "(rule (({to_delete_name} {child_names})
                    (= (values {e} {pf}) ({view_name} {child_names})))
                   ((delete ({view_name} {child_names}))
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
    /// rebuilt too). `naive` marks rules whose primitives read `@UF` tables the rule
    /// body doesn't join on.
    fn rebuild_rule(&mut self, facts: &str, actions: &str, naive: bool) -> String {
        let ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        let naive = if naive { ":naive " } else { "" };
        format!(
            "(rule ({facts})\n     ({actions})\n     :ruleset {ruleset} {naive}:name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
    }

    /// Rebuild rules that keep a view canonical: one rule per rebuildable child
    /// column (a canonical column has no `@UF` row, so the rule simply doesn't
    /// match), plus a rule for the FD view's value column. A stale eq-sort column is
    /// replaced by its `@UF` leader, a stale container by its rebuilt value.
    ///
    /// A child update re-keys the row (`set` at the canonicalized children, then
    /// `delete`); a collision on the new key runs the view's `:merge`. The value
    /// column is canonicalized by [`Self::fd_value_rebuild_rule`]. In proof mode
    /// each rule composes the updated view proof, and a container update records the
    /// rebuilt container's `<CSort>Proof`.
    pub(super) fn rebuilding_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let proofs = self.proofs_enabled();
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
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(&key_vars, " "));

        let mut rules = String::new();
        // One rule per rebuildable key column (re-keys the row via set + delete).
        for (i, ty) in types[..n_keys].iter().enumerate() {
            let is_container = ty.is_eq_container_sort();
            // Eq-sort children are handled by the index-driven rule below, which
            // fixes the whole row in one firing.
            if !is_container {
                continue;
            }
            let ci = child(i);
            let canon = format!("c{i}_canon_");
            let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, &key_vars);
            // Canonicalize the column with the container rebuild primitive or a `@UF`
            // lookup, and build the proof pieces. Container-reading rules are `:naive`
            // (the primitive reads `@UF` tables the rule doesn't join on).
            let (canon_fact, proof_lets, pf_arg, cproof_set) = if is_container {
                let value_prim = self.container_rebuild_prim(ty);
                let canon_fact = format!("(= {canon} ({value_prim} {ci}))");
                if proofs {
                    let congr = self.proof_names().congr_constructor.clone();
                    let trans = self.proof_names().eq_trans_constructor.clone();
                    let sym = self.proof_names().eq_sym_constructor.clone();
                    let proof_sort = self.proof_sort();
                    let proof_prim = self.container_rebuild_proof_prim(ty);
                    let rebuild_pf = self.fresh_var();
                    let cproof = self.term_proof_name(ty.name());
                    // proof_lets: bind the container rebuild proof, then mint the congr proof.
                    let mut lets = vec![format!("(let {rebuild_pf} ({proof_prim} {ci}))")];
                    let new_pf = self.mint(
                        &mut lets,
                        &congr,
                        &format!("{view_prf} {i} {rebuild_pf}"),
                        &proof_sort,
                    );
                    // cproof_set: mint (Sym rebuild_pf), (Trans .. rebuild_pf), then record it.
                    let mut cproof_stmts = vec![];
                    let sym_pf = self.mint(&mut cproof_stmts, &sym, &rebuild_pf, &proof_sort);
                    let trans_pf = self.mint(
                        &mut cproof_stmts,
                        &trans,
                        &format!("{sym_pf} {rebuild_pf}"),
                        &proof_sort,
                    );
                    cproof_stmts.push(format!("(set ({cproof} {canon}) {trans_pf})"));
                    (
                        canon_fact,
                        lets.join("\n                             "),
                        new_pf,
                        cproof_stmts.join("\n                             "),
                    )
                } else {
                    (canon_fact, String::new(), "()".to_string(), String::new())
                }
            } else {
                unreachable!("non-container children take the index-driven rule")
            };
            let mut updated = key_vars.clone();
            updated[i] = canon.clone();
            let updated_view = self.update_fd_view(&fdecl.name, &updated, &value_var, &pf_arg);
            let facts = format!("{query_view}\n{canon_fact}\n(!= {ci} {canon})");
            let actions = format!(
                "{proof_lets}\n{updated_view}\n{cproof_set}\n(delete ({view_name} {keys_str}))"
            );
            rules.push_str(&self.rebuild_rule(&facts, &actions, is_container));
        }
        // FD view value column (see [`Self::fd_value_rebuild_rule`]). A
        // constructor/global's value *is* its e-class; a custom function's
        // eq-sort or eq-container output takes the delete-then-reinsert path.
        // A base-sort custom output never goes stale, so nothing is emitted.
        for vi in self
            .egraph
            .proof_state
            .view_index
            .get(&fdecl.name)
            .cloned()
            .unwrap_or_default()
        {
            rules.push_str(&self.indexed_rebuild_rule(fdecl, &key_vars, &types, &vi));
        }
        if output_is_eclass {
            // Covered by the index rule above, which indexes the e-class column too.
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

    /// The rebuild rule for one child eq-sort, driven by an `@UF_<S>` edge joined
    /// against that sort's declared index.
    ///
    /// The index reaches every row mentioning the moved term — at any child
    /// position or at the e-class — by lookup rather than by matching the view,
    /// and its atom binds the whole row, so nothing else need be read. The action
    /// then re-canonicalizes *every* eq-sort column with `uf_canon`, so one firing
    /// yields the fully canonical row. Two children moving in the same iteration
    /// therefore fire twice with the same result, rather than each producing a
    /// differently half-rewritten row for a later pass to merge.
    ///
    /// `uf_canon` reads `@UF_<S>` in the action, which is what makes the rule
    /// `:unsafe-seminaive`; the driving `@UF` delta in the body is what makes that
    /// read sound.
    fn indexed_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        types: &[ArcSort],
        vi: &ViewIndex,
    ) -> String {
        use crate::proofs::proof_container_rebuild::{
            uf_canon_prim_name, uf_canon_proof_prim_name,
        };
        let proofs = self.proofs_enabled();
        let view_name = self.view_name(&fdecl.name);
        let keys_str = format!("{}", ListDisplay(key_vars, " "));
        let n_keys = key_vars.len();

        let follower = self.fresh_var();
        let leader = self.fresh_var();
        let leader_pf = self.fresh_var();
        let eclass = format!("e{}_", n_keys);
        let row_pf = self.fresh_var();
        let uf_name = self.uf_name(&vi.sort_name);
        let uf_atom = format!("(= (values {leader} {leader_pf}) ({uf_name} {follower}))");
        // The index relation is `(value, children…, eclass, proof)`.
        let index_atom = format!("({} {follower} {keys_str} {eclass} {row_pf})", vi.name);

        // Canonicalize every eq-sort column, folding its congruence step onto the
        // row proof. A column that did not move canonicalizes to itself and its
        // step is reflexive, which the proof simplifier drops.
        let mut lets: Vec<String> = Vec::new();
        let mut updated = key_vars.to_vec();
        let mut proof_acc = row_pf.clone();
        for j in 0..n_keys {
            if types[j].is_eq_container_sort() || !types[j].is_eq_sort() {
                continue;
            }
            let cj = &key_vars[j];
            let uf_j = self.uf_name(types[j].name());
            let canon = format!("c{j}_canon_");
            lets.push(format!(
                "(let {canon} ({} {cj} {cj}))",
                uf_canon_prim_name(&uf_j)
            ));
            if proofs {
                let term_proof = self.term_proof_name(types[j].name());
                let refl = self.fresh_var();
                let step = self.fresh_var();
                let congr = self.proof_names().congr_constructor.clone();
                let proof_sort = self.proof_sort();
                lets.push(format!("(let {refl} ({term_proof} {cj}))"));
                lets.push(format!(
                    "(let {step} ({} {cj} {refl}))",
                    uf_canon_proof_prim_name(&uf_j)
                ));
                proof_acc = self.mint(
                    &mut lets,
                    &congr,
                    &format!("{proof_acc} {j} {step}"),
                    &proof_sort,
                );
            }
            updated[j] = canon;
        }
        // Only an e-class is canonicalized here, and it moves the other way round
        // from a child: the row proof reads `eclass = f(children)`, so a new leader
        // composes as `Trans(Sym(eclass = leader), …)`. A custom function's value
        // column is an ordinary output, not an e-class — that composition would be
        // wrong for it, so it keeps [`Self::fd_value_rebuild_rule`], which rewrites
        // it by `Congr` at its position.
        let out_ty = &types[n_keys];
        let value_var = if self.output_is_eclass(fdecl)
            && out_ty.is_eq_sort()
            && !out_ty.is_eq_container_sort()
        {
            let uf_out = self.uf_name(out_ty.name());
            let canon = format!("e{n_keys}_canon_");
            lets.push(format!(
                "(let {canon} ({} {eclass} {eclass}))",
                uf_canon_prim_name(&uf_out)
            ));
            if proofs {
                let term_proof = self.term_proof_name(out_ty.name());
                let refl = self.fresh_var();
                let step = self.fresh_var();
                let sym = self.proof_names().eq_sym_constructor.clone();
                let trans = self.proof_names().eq_trans_constructor.clone();
                let proof_sort = self.proof_sort();
                lets.push(format!("(let {refl} ({term_proof} {eclass}))"));
                lets.push(format!(
                    "(let {step} ({} {eclass} {refl}))",
                    uf_canon_proof_prim_name(&uf_out)
                ));
                let sym_pf = self.mint(&mut lets, &sym, &step, &proof_sort);
                proof_acc = self.mint(
                    &mut lets,
                    &trans,
                    &format!("{sym_pf} {proof_acc}"),
                    &proof_sort,
                );
            }
            canon
        } else {
            eclass.clone()
        };

        let pf_arg = if proofs { proof_acc } else { "()".to_string() };
        let updated_view = self.update_fd_view(&fdecl.name, &updated, &value_var, &pf_arg);
        let facts = format!("{uf_atom}\n(!= {follower} {leader})\n{index_atom}");
        // Delete before re-inserting. When only the e-class moved the canonical
        // key equals the old one, so deleting afterwards would drop the row it
        // just wrote; deleting first lets the insert win, as the custom-output
        // value rebuild already does.
        let actions = format!(
            "{}\n(delete ({view_name} {keys_str}))\n{updated_view}",
            lets.join("\n                      ")
        );
        let ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        format!(
            "(rule ({facts})\n     ({actions})\n     :ruleset {ruleset} :unsafe-seminaive :name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
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
            let mut lets = vec![];
            let pf = match kind {
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
        self.rebuild_rule(&facts, &actions, false)
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
            let mut lets = vec![format!("(let {rebuild_pf} ({proof_prim} {value_var}))")];
            let new_pf = self.mint(
                &mut lets,
                &congr,
                &format!("{view_prf} {out_idx} {rebuild_pf}"),
                &proof_sort,
            );
            let mut cproof_stmts = vec![];
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
        self.rebuild_rule(&facts, &actions, true)
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
