//! Disequality as ordinary rules and relations, before term/proof encoding.
//!
//! NE detects a self-edge after congruence; EE implements the paper's five-rule
//! equality embedding. Neither changes union-find or infers new inequalities
//! from missing equalities. The private rules run only at `check-contradiction`.

use std::{
    collections::{BTreeMap, BTreeSet, HashSet, VecDeque},
    str::FromStr,
    sync::Arc,
};

use egglog::{
    ArcSort, AtomTerm, CommandMacro, Context, Core, EGraph, Error, Primitive, RawValues, Read,
    ReadPrim, ReadState, TypeError, TypeInfo, Value,
    ast::{
        Action, Actions, Command, Expr, Fact, Macro, ParseError, Parser, Rule, RuleEvalMode,
        RunConfig, Schedule, Schema, Sexp, Span,
    },
    constraint::{Constraint, TypeConstraint},
    sort::S,
    util::{FreshGen, SymbolGen},
};

const PLACEHOLDER: &str = "@disequal";
const RULESET: &str = "@disequality";
const CONTRADICTION: &str = "@disequality-contradiction";
const TRUTH: &str = "@disequality-truth";
const TRUE: &str = "@disequality-true";
const FALSE: &str = "@disequality-false";

/// Encodings from Dis-Equality Graphs, with a relation for NE's private terms.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DisequalityEncoding {
    /// A private relation per equality sort; a self-edge derives contradiction.
    #[default]
    Nee,
    /// Equality embedding into a private truth sort (the paper's five rules).
    Ee,
}

impl FromStr for DisequalityEncoding {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "nee" => Ok(Self::Nee),
            "ee" => Ok(Self::Ee),
            _ => Err(format!(
                "unknown disequality encoding `{value}`; expected nee or ee"
            )),
        }
    }
}

/// Install syntax and its lowering pass before enabling term/proof encoding.
/// Call once on a fresh graph; the encoding is fixed for that graph.
pub(crate) fn add_disequality_support(egraph: &mut EGraph, encoding: DisequalityEncoding) {
    egraph.add_read_primitive(KnownDisequal(encoding), None);
    egraph.parser.add_action_macro(Arc::new(Disequal));
    egraph
        .parser
        .add_command_macro(Arc::new(CheckContradiction(encoding)));
    egraph
        .command_macros_mut()
        .register(Arc::new(LowerDisequality(encoding)));
}

/// Read-only witness search. No validator is registered: proof support for this
/// query is separate from the ordinary rules encoding asserted disequalities.
#[derive(Clone)]
struct KnownDisequal(DisequalityEncoding);

impl Primitive for KnownDisequal {
    fn name(&self) -> &str {
        "known-disequal?"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(KnownDisequalConstraint(span.clone()))
    }
}

struct KnownDisequalConstraint(Span);

impl TypeConstraint for KnownDisequalConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        types: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let unit = types.get_sort_by_name("Unit").unwrap();
        let mut sorts = types.get_arcsorts_by(|sort| types.is_sort_unionable(sort));
        sorts.sort_by_key(|sort| sort.name().to_owned());
        crate::type_constraints::exact_signatures(
            "known-disequal?",
            &self.0,
            arguments,
            3,
            sorts
                .into_iter()
                .map(|sort| vec![sort.clone(), sort, unit.clone()]),
        )
    }
}

impl ReadPrim for KnownDisequal {
    fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [lhs, rhs] = args else {
            unreachable!("known-disequal? arity is checked before execution")
        };
        match known_disequal(&state, self.0, *lhs, *rhs) {
            Ok(true) => Some(state.base_to_value(())),
            Ok(false) => None,
            Err(error) => {
                log::error!("known-disequal?: {error}");
                None
            }
        }
    }
}

/// Search a finite graph of pair goals. Every edge is a single sound forward
/// or unary reverse implication, so reaching an explicit assertion or a native
/// primitive mismatch is a witness. Cycles without such a seed prove nothing.
fn known_disequal<'db>(
    state: &ReadState<'_, 'db>,
    encoding: DisequalityEncoding,
    lhs: Value,
    rhs: Value,
) -> Result<bool, Error> {
    let mut sorts = BTreeSet::new();
    // The common explicit-assertion case needs no structural search.
    for name in state.tables() {
        let assertion_table = match encoding {
            DisequalityEncoding::Nee => name.starts_with("@disequality-ne-"),
            DisequalityEncoding::Ee => {
                name == "@disequality-eq" || name.starts_with("@disequality-eq-")
            }
        };
        if assertion_table {
            let schema = state.constructor_schema(name)?;
            let sort = schema.input[0].name();
            if asserted_disequal(state, encoding, sort, lhs, rhs)? {
                return Ok(true);
            }
            sorts.insert(sort.to_owned());
        }
    }
    let mut names = Vec::new();
    if state
        .table_size(crate::injectivity::MARKED_CONSTRUCTORS)
        .is_some()
    {
        state.function_entries(crate::injectivity::MARKED_CONSTRUCTORS, |entry| {
            names.push(state.value_to_base::<S>(entry.inputs[0]).0);
        })?;
    }
    let mut constructors = Vec::new();
    for name in &names {
        let schema = state.constructor_schema(name)?;
        sorts.insert(schema.output().name().to_owned());
        for sort in &schema.input {
            if sort.is_eq_sort() {
                sorts.insert(sort.name().to_owned());
            }
        }
        constructors.push((name.as_str(), schema));
    }
    // ReadPrim does not receive its resolved input type. Eq-sort IDs share one
    // global counter (as in unstable-subst), so probing another sort cannot
    // match the root pair. Descendant and parent goals have exact schema types.
    let mut pending: VecDeque<_> = sorts.into_iter().map(|sort| (sort, lhs, rhs)).collect();
    let mut visited = HashSet::new();
    while let Some((sort, mut left, mut right)) = pending.pop_front() {
        if left > right {
            std::mem::swap(&mut left, &mut right);
        }
        if !visited.insert((sort.clone(), left, right)) {
            continue;
        }
        if asserted_disequal(state, encoding, &sort, left, right)? {
            return Ok(true);
        }
        for &(name, schema) in &constructors {
            if schema.output().name() == sort {
                let mut left_rows = Vec::new();
                let mut right_rows = Vec::new();
                state.constructor_enodes_for_eclass(name, left, |node| {
                    left_rows.push(node.children.to_vec())
                })?;
                state.constructor_enodes_for_eclass(name, right, |node| {
                    right_rows.push(node.children.to_vec())
                })?;
                for a in &left_rows {
                    for b in &right_rows {
                        for ((&a, &b), input) in a.iter().zip(b).zip(&schema.input) {
                            if input.is_eq_sort() {
                                pending.push_back((input.name().to_owned(), a, b));
                            } else if a != b {
                                return Ok(true);
                            }
                        }
                    }
                }
            }
            if let [input] = schema.input.as_slice()
                && input.name() == sort
                && input.is_eq_sort()
            {
                // Constructor lookup is read-only and includes subsumed rows.
                // Missing applications supply no reverse implication.
                if let (Some(a), Some(b)) = (
                    state.eclass_of(name, RawValues(vec![left]))?,
                    state.eclass_of(name, RawValues(vec![right]))?,
                ) {
                    pending.push_back((schema.output().name().to_owned(), a, b));
                }
            }
        }
    }
    Ok(false)
}

/// Inspect existing encoded facts, including either orientation.
/// Missing lazy support is an empty set of assertions, not a declaration error.
fn asserted_disequal(
    state: &ReadState<'_, '_>,
    encoding: DisequalityEncoding,
    sort: &str,
    lhs: Value,
    rhs: Value,
) -> Result<bool, Error> {
    match encoding {
        DisequalityEncoding::Nee => {
            let name = format!("@disequality-ne-{sort}");
            if state.table_size(&name).is_none() {
                return Ok(false);
            }
            Ok(state.contains(&name, RawValues(vec![lhs, rhs]))?
                || state.contains(&name, RawValues(vec![rhs, lhs]))?)
        }
        DisequalityEncoding::Ee => {
            let name = equality_name(sort);
            if state.table_size(&name).is_none() || state.table_size(FALSE).is_none() {
                return Ok(false);
            }
            let Some(false_value) = state.eclass_of(FALSE, RawValues(vec![]))? else {
                return Ok(false);
            };
            Ok(
                state.eclass_of(&name, RawValues(vec![lhs, rhs]))? == Some(false_value)
                    || state.eclass_of(&name, RawValues(vec![rhs, lhs]))? == Some(false_value),
            )
        }
    }
}

struct Disequal;

impl Macro<Vec<Action>> for Disequal {
    fn name(&self) -> &str {
        "disequal"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Action>, ParseError> {
        let [lhs, rhs] = args else {
            return Err(ParseError(span, "usage: (disequal <expr> <expr>)".into()));
        };
        Ok(vec![Action::Expr(
            span.clone(),
            Expr::Call(
                span,
                PLACEHOLDER.into(),
                vec![parser.parse_expr(lhs)?, parser.parse_expr(rhs)?],
            ),
        )])
    }
}

struct CheckContradiction(DisequalityEncoding);

impl Macro<Vec<Command>> for CheckContradiction {
    fn name(&self) -> &str {
        "check-contradiction"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        _parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        if !args.is_empty() {
            return Err(ParseError(span, "usage: (check-contradiction)".into()));
        }
        Ok(vec![
            Command::RunSchedule(Schedule::Saturate(
                span.clone(),
                Box::new(Schedule::Run(
                    span.clone(),
                    RunConfig {
                        ruleset: RULESET.into(),
                        until: None,
                    },
                )),
            )),
            Command::Check(
                span.clone(),
                vec![match self.0 {
                    DisequalityEncoding::Nee => {
                        Fact::Fact(Expr::Call(span, CONTRADICTION.into(), vec![]))
                    }
                    DisequalityEncoding::Ee => Fact::Eq(
                        span.clone(),
                        Expr::Call(span.clone(), TRUE.into(), vec![]),
                        Expr::Call(span, FALSE.into(), vec![]),
                    ),
                }],
            ),
        ])
    }
}

struct LowerDisequality(DisequalityEncoding);

impl CommandMacro for LowerDisequality {
    fn transform(
        &self,
        command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let expanded = crate::fresh_macro::FreshMacro::new().transform(command, symbols, types)?;
        let needs_inference = expanded
            .iter()
            .any(|c| matches!(c, Command::Rule { rule } if contains_disequal(&rule.head)));
        let mut local_types = std::borrow::Cow::Borrowed(types);
        let mut result = Vec::new();
        for command in expanded {
            // FreshMacro emits a constructor before its rule. Make that signature
            // visible to this pass without installing anything in the live graph.
            if needs_inference
                && let Command::Constructor {
                    span,
                    name,
                    schema,
                    cost,
                    unextractable,
                    injective: _,
                    hidden,
                    let_binding,
                } = &command
            {
                let mut declaration = egglog::ast::FunctionDecl::constructor(
                    span.clone(),
                    name.clone(),
                    schema.clone(),
                    *cost,
                    *unextractable,
                    *hidden,
                );
                declaration.internal_let = *let_binding;
                local_types
                    .to_mut()
                    .typecheck_function(symbols, &declaration)?;
                result.push(command);
            } else {
                result.extend(self.lower(command, symbols, &local_types)?);
            }
        }
        Ok(result)
    }
}

impl LowerDisequality {
    fn lower(
        &self,
        mut command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let mut sorts = BTreeMap::new();
        let mut support_span = None;
        self.lower_command(&mut command, symbols, types, &mut sorts, &mut support_span)?;
        let Some(span) = support_span else {
            return Ok(vec![command]);
        };
        let mut commands = Vec::new();
        if self.0 == DisequalityEncoding::Nee && types.get_func_type(CONTRADICTION).is_none() {
            commands.push(Command::AddRuleset(span.clone(), RULESET.into()));
            commands.push(Command::Relation {
                span: span.clone(),
                name: CONTRADICTION.into(),
                inputs: vec![],
            });
        }
        if self.0 == DisequalityEncoding::Ee && types.get_sort_by_name(TRUTH).is_none() {
            commands.push(Command::AddRuleset(span.clone(), RULESET.into()));
            commands.push(Command::Sort {
                span: span.clone(),
                name: TRUTH.into(),
                presort_and_args: None,
                uf: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
            });
            commands.push(constructor(&span, TRUE.into(), vec![], TRUTH));
            commands.push(constructor(&span, FALSE.into(), vec![], TRUTH));
            commands.extend(equality_rules(&span, TRUTH));
        }
        for (sort, span) in sorts {
            let name = match self.0 {
                DisequalityEncoding::Nee => format!("@disequality-ne-{sort}"),
                DisequalityEncoding::Ee => equality_name(&sort),
            };
            if types.get_func_type(&name).is_some() {
                continue;
            }
            match self.0 {
                DisequalityEncoding::Nee => {
                    commands.push(Command::Relation {
                        span: span.clone(),
                        name: name.clone(),
                        inputs: vec![sort.clone(), sort.clone()],
                    });
                    let x = Expr::Var(span.clone(), "x".into());
                    commands.push(rule(
                        &span,
                        format!("ne-self-{sort}"),
                        vec![Fact::Fact(Expr::Call(
                            span.clone(),
                            name,
                            vec![x.clone(), x],
                        ))],
                        vec![Action::Expr(
                            span.clone(),
                            Expr::Call(span.clone(), CONTRADICTION.into(), vec![]),
                        )],
                    ));
                }
                DisequalityEncoding::Ee => commands.extend(equality_rules(&span, &sort)),
            }
        }
        // Proof history survives pop, so a reinstalled rule needs a fresh identity.
        for generated in &mut commands {
            if let Command::Rule { rule } = generated {
                rule.name = symbols.fresh(&rule.name);
            }
        }
        commands.push(command);
        Ok(commands)
    }
}

impl LowerDisequality {
    fn lower_command(
        &self,
        command: &mut Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
        sorts: &mut BTreeMap<String, Span>,
        support_span: &mut Option<Span>,
    ) -> Result<(), Error> {
        match command {
            Command::Rule { rule } if contains_disequal(&rule.head) => {
                // Union has the same operand constraints as disequal. Use it only
                // for inference, never execution, so head uses can constrain the body.
                let mut probe = rule.clone();
                probe.head = union_probe(&rule.head);
                let resolved = types.typecheck_rule(symbols, &probe, false)?;
                for (action, typed) in rule.head.0.iter_mut().zip(resolved.head.0) {
                    if let Action::Expr(span, Expr::Call(_, head, args)) = action
                        && head == PLACEHOLDER
                    {
                        let egglog::ast::GenericAction::Union(_, lhs, _) = typed else {
                            unreachable!()
                        };
                        let sort = match lhs {
                            egglog::ast::ResolvedExpr::Var(_, var) => var.sort,
                            egglog::ast::ResolvedExpr::Call(_, call, _) => call.output().clone(),
                            egglog::ast::ResolvedExpr::Lit(_, literal) => {
                                egglog::sort::literal_sort(&literal)
                            }
                        };
                        if !sort.is_eq_sort() {
                            return Err(TypeError::NonEqsortUnion(sort, span.clone()).into());
                        }
                        if !types.is_sort_unionable(&sort) {
                            return Err(TypeError::NonUnionableSort(sort, span.clone()).into());
                        }
                        sorts.insert(sort.name().into(), span.clone());
                        *action = self.encoded_action(span, args, sort.name());
                    }
                }
            }
            Command::Action(Action::Expr(_, Expr::Call(_, head, _))) if head == PLACEHOLDER => {
                let Command::Action(action) = command else {
                    unreachable!()
                };
                let mut actions = Actions::singleton(action.clone());
                self.lower_actions(&mut actions, vec![], symbols, types, sorts)?;
                *action = actions.0.remove(0);
            }
            Command::LetBegin(span, _, actions) if matches!(actions.0.last(), Some(Action::Expr(_, Expr::Call(_, head, _))) if head == PLACEHOLDER) =>
            {
                return Err(Error::DesugarError(
                    span.clone(),
                    "let-begin must end with a value, not disequal".into(),
                ));
            }
            Command::Actions(actions) | Command::LetBegin(_, _, actions)
                if contains_disequal(actions) =>
            {
                let resolved = types.typecheck_standalone_actions(
                    symbols,
                    &union_probe(actions),
                    &Default::default(),
                    Context::Full,
                )?;
                let bindings = resolved
                    .0
                    .into_iter()
                    .filter_map(|action| match action {
                        egglog::ast::GenericAction::Let(span, var, _) => {
                            Some((var.name, span, var.sort))
                        }
                        _ => None,
                    })
                    .collect();
                self.lower_actions(actions, bindings, symbols, types, sorts)?;
            }
            Command::Fail(_, commands) => {
                for command in commands {
                    self.lower_command(command, symbols, types, sorts, support_span)?;
                }
            }
            Command::RunSchedule(Schedule::Saturate(span, schedule)) if matches!(schedule.as_ref(), Schedule::Run(_, config) if config.ruleset == RULESET) =>
            {
                *support_span = Some(span.clone());
            }
            _ => {}
        }
        if let Some(span) = sorts.values().next() {
            *support_span = Some(span.clone());
        }
        Ok(())
    }

    fn lower_actions(
        &self,
        actions: &mut Actions,
        bindings: Vec<(String, Span, ArcSort)>,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
        sorts: &mut BTreeMap<String, Span>,
    ) -> Result<(), Error> {
        for action in &mut actions.0 {
            match action {
                Action::Expr(span, Expr::Call(_, head, args)) if head == PLACEHOLDER => {
                    let [lhs, rhs] = args.as_slice() else {
                        unreachable!("parser checks disequal arity")
                    };
                    let left = operand_sort(types, symbols, lhs, &bindings)?;
                    let right = operand_sort(types, symbols, rhs, &bindings)?;
                    if left.name() != right.name() {
                        return Err(TypeError::Mismatch {
                            expr: rhs.clone(),
                            expected: left,
                            actual: right,
                        }
                        .into());
                    }
                    if !left.is_eq_sort() {
                        return Err(TypeError::NonEqsortUnion(left, span.clone()).into());
                    }
                    if !types.is_sort_unionable(&left) {
                        return Err(TypeError::NonUnionableSort(left, span.clone()).into());
                    }
                    sorts.insert(left.name().into(), span.clone());
                    *action = self.encoded_action(span, args, left.name());
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn encoded_action(&self, span: &Span, args: &[Expr], sort: &str) -> Action {
        match self.0 {
            DisequalityEncoding::Nee => Action::Expr(
                span.clone(),
                Expr::Call(
                    span.clone(),
                    format!("@disequality-ne-{sort}"),
                    args.to_vec(),
                ),
            ),
            DisequalityEncoding::Ee => Action::Union(
                span.clone(),
                Expr::Call(span.clone(), equality_name(sort), args.to_vec()),
                Expr::Call(span.clone(), FALSE.into(), vec![]),
            ),
        }
    }
}

/// Use union's operand constraints without ever executing the inferred action.
fn union_probe(actions: &Actions) -> Actions {
    egglog::ast::GenericActions(
        actions
            .0
            .iter()
            .map(|action| match action {
                Action::Expr(span, Expr::Call(_, head, args)) if head == PLACEHOLDER => {
                    Action::Union(span.clone(), args[0].clone(), args[1].clone())
                }
                _ => action.clone(),
            })
            .collect(),
    )
}

/// Declared calls already determine their result sort. Avoid solving the full
/// expression twice; the emitted action still validates all argument types.
fn operand_sort(
    types: &TypeInfo,
    symbols: &mut SymbolGen,
    expr: &Expr,
    bindings: &[(String, Span, ArcSort)],
) -> Result<ArcSort, TypeError> {
    let declared = match expr {
        Expr::Var(_, name) => bindings
            .iter()
            .find_map(|(n, _, s)| (n == name).then_some(s))
            .or_else(|| types.get_global_sort(name)),
        Expr::Call(_, head, _) if !types.is_primitive(head) => {
            types.get_func_type(head).map(|f| f.output())
        }
        _ => None,
    };
    match declared {
        Some(sort) => Ok(sort.clone()),
        None => types.infer_expr_sort(symbols, expr, bindings, Context::Full),
    }
}

fn contains_disequal(actions: &Actions) -> bool {
    actions
        .0
        .iter()
        .any(|a| matches!(a, Action::Expr(_, Expr::Call(_, head, _)) if head == PLACEHOLDER))
}

fn equality_name(sort: &str) -> String {
    if sort == TRUTH {
        "@disequality-eq".into()
    } else {
        format!("@disequality-eq-{sort}")
    }
}

fn constructor(span: &Span, name: String, input: Vec<String>, output: &str) -> Command {
    Command::Constructor {
        span: span.clone(),
        name,
        schema: Schema::new(input, output.into()),
        cost: None,
        unextractable: true,
        injective: false,
        hidden: true,
        let_binding: false,
    }
}

fn rule(span: &Span, name: String, body: Vec<Fact>, head: Vec<Action>) -> Command {
    Command::Rule {
        rule: Rule {
            span: span.clone(),
            name: format!("@disequality-{name}"),
            ruleset: RULESET.into(),
            body,
            head: Actions::new(head),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        },
    }
}

fn equality_rules(span: &Span, sort: &str) -> Vec<Command> {
    let eq = equality_name(sort);
    let x = Expr::Var(span.clone(), "x".into());
    let y = Expr::Var(span.clone(), "y".into());
    let t = Expr::Call(span.clone(), TRUE.into(), vec![]);
    let f = Expr::Call(span.clone(), FALSE.into(), vec![]);
    let xy = Expr::Call(span.clone(), eq.clone(), vec![x.clone(), y.clone()]);
    vec![
        constructor(span, eq.clone(), vec![sort.into(), sort.into()], TRUTH),
        rule(
            span,
            format!("ee-lift-{sort}"),
            vec![Fact::Eq(span.clone(), xy.clone(), t.clone())],
            vec![Action::Union(span.clone(), x.clone(), y.clone())],
        ),
        rule(
            span,
            format!("ee-symmetry-{sort}"),
            vec![Fact::Eq(span.clone(), xy.clone(), f.clone())],
            vec![Action::Union(
                span.clone(),
                Expr::Call(span.clone(), eq.clone(), vec![y.clone(), x.clone()]),
                f.clone(),
            )],
        ),
        rule(
            span,
            format!("ee-double-negation-{sort}"),
            vec![Fact::Eq(
                span.clone(),
                Expr::Call(
                    span.clone(),
                    equality_name(TRUTH),
                    vec![xy.clone(), f.clone()],
                ),
                f.clone(),
            )],
            vec![Action::Union(span.clone(), x.clone(), y.clone())],
        ),
        rule(
            span,
            format!("ee-reflexive-left-{sort}"),
            vec![Fact::Eq(span.clone(), xy.clone(), f.clone())],
            vec![Action::Union(
                span.clone(),
                Expr::Call(span.clone(), eq.clone(), vec![x.clone(), x]),
                t.clone(),
            )],
        ),
        rule(
            span,
            format!("ee-reflexive-right-{sort}"),
            vec![Fact::Eq(span.clone(), xy, f)],
            vec![Action::Union(
                span.clone(),
                Expr::Call(span.clone(), eq, vec![y.clone(), y]),
                t,
            )],
        ),
    ]
}
