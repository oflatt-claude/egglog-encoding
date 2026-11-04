//! Shared program processing.

use crate::*;

impl EGraph {
    /// Run a program and return its outputs, or resolve it without execution.
    /// Only resolution retains the lowered commands in the returned value.
    pub(super) fn process_program_internal(
        &mut self,
        program: Vec<Command>,
        run_commands: bool,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        let mut outputs = Vec::new();
        let mut desugared_before_proofs = Vec::new();
        let mut desugared = Vec::new();

        for before_expanded_command in program {
            // First do user-provided macro expansion for this command,
            // which may rely on type information from previous commands.
            let macro_type_info = self
                .proof_state
                .original_typechecking
                .as_ref()
                .map(|egraph| &egraph.type_info)
                .unwrap_or(&self.type_info);
            let macro_timer = Instant::now();
            let macro_expanded = self.command_macros.apply(
                before_expanded_command,
                &mut self.parser.symbol_gen,
                macro_type_info,
            );
            self.overall_report.frontend_other += macro_timer.elapsed();
            let macro_expanded = macro_expanded?;

            for command in macro_expanded {
                // handle include specially- we keep them as-is for desugaring
                if let Command::Include(span, file) = &command {
                    let include_timer = Instant::now();
                    let s = std::fs::read_to_string(file)
                        .map_err(|e| Error::IoError(file.clone().into(), e, span.clone()));
                    self.overall_report.frontend_other += include_timer.elapsed();
                    let s = s?;
                    let included_program = self.parse_program_timed(Some(file.clone()), &s)?;
                    // run program internal on these include commands
                    let resolved = self.process_program_internal(included_program, run_commands)?;
                    outputs.extend(resolved.outputs);
                    desugared.extend(resolved.resolved);
                    desugared_before_proofs.extend(resolved.resolved_before_proofs);
                } else {
                    let resolved = self.resolve_command(command)?;
                    // Execution callers discard resolved trees; retaining them here
                    // duplicates large proof programs. Keep only the checker's history.
                    if run_commands {
                        if self.are_proofs_enabled() {
                            self.proof_check_program
                                .extend(resolved.desugared_before_proofs);
                        }
                    } else {
                        desugared_before_proofs.extend(resolved.desugared_before_proofs);
                        desugared.extend(resolved.desugared.clone());
                    }

                    for processed in resolved.desugared {
                        // even in desugar mode we still run push and pop
                        if run_commands
                            || matches!(
                                processed,
                                ResolvedNCommand::Push(_) | ResolvedNCommand::Pop(_, _)
                            )
                        {
                            let result = self.run_command(processed)?;
                            outputs.extend(result);
                        }
                    }
                }
            }
        }

        Ok(ResolvedNCommandsWithOutput {
            outputs,
            resolved_before_proofs: desugared_before_proofs,
            resolved: desugared,
        })
    }

    pub(super) fn run_command(
        &mut self,
        command: ResolvedNCommand,
    ) -> Result<Vec<CommandOutput>, Error> {
        enum CommandPhase {
            Install,
            Actions,
            Check,
            Other,
        }

        let phase = match &command {
            ResolvedNCommand::Sort { .. }
            | ResolvedNCommand::Function(_)
            | ResolvedNCommand::Index { .. }
            | ResolvedNCommand::AddRuleset(..)
            | ResolvedNCommand::UnstableCombinedRuleset(..)
            | ResolvedNCommand::NormRule { .. } => CommandPhase::Install,
            ResolvedNCommand::CoreAction(_)
            | ResolvedNCommand::CoreActions(_)
            | ResolvedNCommand::Input { .. } => CommandPhase::Actions,
            ResolvedNCommand::Check(..) => CommandPhase::Check,
            _ => CommandPhase::Other,
        };
        let command_timer = Instant::now();
        let process_before = self.overall_report.process_time();
        let iteration_before = self.overall_report.run.iterations.len();
        let result = self.run_command_inner(command);
        let nested_process = self
            .overall_report
            .process_time()
            .saturating_sub(process_before);
        let nested_rulesets = self.overall_report.run.iterations[iteration_before..]
            .iter()
            .map(|iteration| iteration.report.total_time())
            .sum();
        let own_time = command_timer
            .elapsed()
            .saturating_sub(nested_process + nested_rulesets);
        match phase {
            CommandPhase::Install => self.overall_report.frontend_install += own_time,
            CommandPhase::Actions => self.overall_report.commands_actions += own_time,
            CommandPhase::Check => self.overall_report.commands_check += own_time,
            CommandPhase::Other => self.overall_report.commands_other += own_time,
        }
        result
    }

    fn run_command_inner(
        &mut self,
        command: ResolvedNCommand,
    ) -> Result<Vec<CommandOutput>, Error> {
        match command {
            // Sorts are already declared during typechecking
            ResolvedNCommand::Sort {
                name,
                uf,
                proof_constructors,
                ..
            } => {
                // Restore the sort's UF metadata into proof_state.
                if let Some((uf_ctor, _uf_index)) = uf {
                    self.proof_state
                        .uf_parent
                        .insert(name.clone(), uf_ctor.clone());
                }
                // The Proof sort's :internal-proof-names records the global proof
                // constructors; restore them so container rebuild can recover them.
                if let Some(pc) = proof_constructors {
                    let names = &mut self.proof_state.proof_names;
                    names.proof_datatype = name.clone();
                    names.congr_constructor = pc.congr;
                    names.congr_all_constructor = pc.congr_all;
                    names.eq_trans_constructor = pc.trans;
                    names.eq_sym_constructor = pc.sym;
                    names.container_normalize_constructor = pc.normalize;
                    // Recovered so `native_input` can build `(input …)` base-fact
                    // proofs when replaying an encoded program in a fresh e-graph.
                    names.fiat_prefix = pc.fiat;
                    names.proj_constructor = pc.proj;
                    names.proj_prim_prefix = pc.proj_prim;
                }
                log::info!("Declared sort {name}.")
            }
            ResolvedNCommand::Function(fdecl) => {
                self.declare_function(&fdecl)?;
                log::info!("Declared {} {}.", fdecl.subtype, fdecl.name)
            }
            ResolvedNCommand::Index { name, function, .. } => {
                // Nothing to build: storage creates the occurrence index the
                // first time a rule probes it. Typechecking already registered
                // the relation the atoms resolve against.
                log::info!("Declared index {name} over {function}.");
            }
            ResolvedNCommand::AddRuleset(_span, name) => {
                self.add_ruleset(name.clone());
                log::info!("Declared ruleset {name}.");
            }
            ResolvedNCommand::UnstableCombinedRuleset(span, name, others) => {
                self.add_combined_ruleset(&span, name.clone(), others)?;
                log::info!("Declared ruleset {name}.");
            }
            ResolvedNCommand::NormRule { rule } => {
                let name = rule.name.clone();
                self.add_rule(rule)?;
                log::info!("Declared rule {name}.")
            }
            ResolvedNCommand::RunSchedule(sched) => {
                let report = self.run_schedule(&sched)?;
                log::info!("Ran schedule {sched}.");
                log::info!("Report: {report}");
                // Already recorded by `step_rules`, per iteration.
                return Ok(vec![CommandOutput::RunSchedule(report)]);
            }
            ResolvedNCommand::PrintOverallStatistics(span, file) => match file {
                None => {
                    log::info!("Printed overall statistics");
                    return Ok(vec![CommandOutput::OverallStatistics(
                        self.overall_report.run.clone(),
                    )]);
                }
                Some(path) => {
                    let mut file = std::fs::File::create(&path)
                        .map_err(|e| Error::IoError(path.clone().into(), e, span.clone()))?;
                    log::info!("Printed overall statistics to json file {path}");

                    serde_json::to_writer(&mut file, &self.overall_report.run).map_err(|e| {
                        Error::BackendError(format!("failed writing statistics: {e}"))
                    })?;
                }
            },
            ResolvedNCommand::Check(span, facts) => {
                self.check_facts(&span, &facts)?;
                log::info!("Checked fact {facts:?}.");
            }
            ResolvedNCommand::CoreAction(action) => match &action {
                ResolvedAction::Let(_, name, contents) => {
                    panic!("Globals should have been desugared away: {name} = {contents}")
                }
                _ => {
                    if let Some(prepared) = self.prepare_resolved_ground_action(&action) {
                        self.eval_ground_actions(vec![prepared])?;
                    } else {
                        self.eval_actions(&ResolvedActions::new(vec![action.clone()]))?;
                    }
                }
            },
            // One `eval_actions` call, so the block's `let`s stay local.
            ResolvedNCommand::CoreActions(actions) => {
                self.eval_actions(&actions)?;
            }
            ResolvedNCommand::LetBegin(..) => {
                unreachable!("LetBegin is removed by remove_globals")
            }
            ResolvedNCommand::ProveExtract(_, expr, variants) => {
                return self.run_prove_extract(&expr, &variants);
            }
            ResolvedNCommand::Extract(span, expr, variants) => {
                let sort = expr.output_type();

                let x = self.eval_resolved_expr(span.clone(), &expr)?;
                let n = self.eval_resolved_expr(span, &variants)?;
                let n: i64 = self.backend.base_values().unwrap(n);

                if n < 0 {
                    return Err(Error::ExtractError(
                        "cannot extract a negative number of variants".to_string(),
                    ));
                }
                let output = self.extract_command(sort, x, n as usize)?;
                // Avoid rendering terms when messages are disabled.
                if log_enabled!(Level::Info) {
                    match &output {
                        CommandOutput::ExtractBest(termdag, cost, term) => {
                            log::info!("extracted with cost {cost}: {}", termdag.to_string(*term));
                        }
                        CommandOutput::ExtractVariants(_, terms) => {
                            let expr_str = expr.to_string();
                            log::info!("extracted {} variants for {expr_str}", terms.len());
                        }
                        _ => unreachable!(),
                    }
                }
                return Ok(vec![output]);
            }
            ResolvedNCommand::Push(n) => {
                (0..n).for_each(|_| self.push());
                log::info!("Pushed {n} levels.")
            }
            ResolvedNCommand::Pop(span, n) => {
                for _ in 0..n {
                    self.pop().map_err(|err| {
                        if let Error::Pop(_) = err {
                            Error::Pop(span.clone())
                        } else {
                            err
                        }
                    })?;
                }
                log::info!("Popped {n} levels.")
            }
            ResolvedNCommand::PrintFunction(span, f, n, file, mode) => {
                let file = file
                    .map(|file| {
                        let path: PathBuf = file.into();
                        match std::fs::File::create(&path) {
                            Ok(f) => Ok((f, path)),
                            Err(e) => Err(Error::IoError(path, e, span.clone())),
                        }
                    })
                    .transpose()?;
                return self
                    .print_function(&f, n, file, span.clone(), mode)
                    .map_err(|e| match e {
                        Error::TypeError(TypeError::UnboundFunction(f, _)) => {
                            Error::TypeError(TypeError::UnboundFunction(f, span.clone()))
                        }
                        // This case is currently impossible
                        _ => e,
                    })
                    .map(|opt| opt.into_iter().collect());
            }
            ResolvedNCommand::PrintSize(span, f) => {
                let res = self.print_size(f.as_deref()).map_err(|e| match e {
                    Error::TypeError(TypeError::UnboundFunction(f, _)) => {
                        Error::TypeError(TypeError::UnboundFunction(f, span.clone()))
                    }
                    // This case is currently impossible
                    _ => e,
                })?;
                return Ok(vec![res]);
            }
            ResolvedNCommand::Fail(span, cmds) => {
                // A single check is read-only, so avoid cloning the e-graph for
                // the overwhelmingly common negative-assertion form.
                if matches!(cmds.as_slice(), [ResolvedNCommand::Check(..)]) {
                    let check = cmds.into_iter().next().unwrap();
                    return match self.run_command(check) {
                        Err(error) => {
                            log::info!("Command failed as expected: {error}");
                            Ok(vec![])
                        }
                        Ok(_) => Err(Error::ExpectFail(span)),
                    };
                }

                self.push();
                let failure = cmds
                    .into_iter()
                    .find_map(|command| self.run_command(command).err());
                self.pop()
                    .expect("the snapshot pushed for `fail` must still be present");
                return match failure {
                    Some(error) => {
                        log::info!("Command failed as expected: {error}");
                        Ok(vec![])
                    }
                    None => Err(Error::ExpectFail(span)),
                };
            }
            ResolvedNCommand::Input {
                span,
                name,
                file,
                proof_base,
            } => {
                // An encoded program (term/proof mode, or a replayed desugared
                // program) declares nothing under the function's own name, so the
                // name resolving to a view is what says the rows go into the
                // encoded tables; a plain program targets a user
                // relation/constructor loaded by the relation loader.
                if self.functions.get(&name).is_some_and(|f| f.is_fd_view()) {
                    self.native_input(span, &name, file, proof_base)?;
                } else {
                    self.input_file(span, &name, file)?;
                }
            }
            ResolvedNCommand::Output { span, file, exprs } => {
                let mut filename = self.fact_directory.clone().unwrap_or_default();
                filename.push(file.as_str());

                // Preserve the command's file-error ordering: reject an invalid
                // output path before evaluating expressions.
                use std::io::Write;
                let mut f = File::options()
                    .append(true)
                    .create(true)
                    .open(&filename)
                    .map_err(|e| Error::IoError(filename.clone(), e, span.clone()))?;

                // Evaluation may mutate the e-graph, so finish it before
                // extraction takes a shared borrow for its prepared costs.
                let roots = exprs
                    .iter()
                    .map(|expr| {
                        let value = self.eval_resolved_expr(span.clone(), expr)?;
                        Ok((expr.output_type(), value))
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                let extracted = self.extract_best(roots)?;
                for root in extracted.terms {
                    let root = root.ok_or_else(|| {
                        Error::ExtractError(
                            "Unable to find any valid extraction (likely due to subsume or delete)"
                                .to_string(),
                        )
                    })?;
                    writeln!(f, "{}", extracted.termdag.to_string(root.term))
                        .map_err(|e| Error::IoError(filename.clone(), e, span.clone()))?;
                }

                log::info!("Output to '{filename:?}'.")
            }
            ResolvedNCommand::UserDefined(_span, name, exprs) => {
                let command = self
                    .commands
                    .get(&name)
                    .ok_or_else(|| {
                        NotFoundError(format!("Unrecognized user-defined command: {name}"))
                    })?
                    .clone();
                return command.update(self, &exprs);
            }

            ResolvedNCommand::ProveExists(span, resolved_call) => {
                let mut instrument = ProofInstrumentor::new(self);
                let (proof_store, proof_id) =
                    instrument
                        .prove_exists(&resolved_call)
                        .map_err(|error| Error::ProofError {
                            span: span.clone(),
                            error,
                        })?;
                return Ok(vec![CommandOutput::ProveExists {
                    proof_store,
                    proof_id,
                }]);
            }
        };

        Ok(vec![])
    }
}
