use egglog_experimental::slotted::{Compiler, Options};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

const LANGUAGE: &str = "(datatype U ($Var) (Null) (F U U) (G U U) (H U U) (Lam U U :binder 0))";

fn evaluate(compiler: &mut Compiler, graph: &mut egglog::EGraph, source: &str) {
    let encoded = compiler.compile(None, source).unwrap();
    graph.parse_and_run_program(None, &encoded).unwrap();
}

#[test]
fn string_payloads_preserve_quotes_and_backslashes() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(
        &mut compiler,
        &mut graph,
        r#"(datatype U ($Var) (Text String)) (let value (Text "a\"b\\c"))"#,
    );
    graph
        .parse_and_run_program(None, r#"(check (= text (Text "a\"b\\c")))"#)
        .unwrap();
}

#[test]
fn transformation_emits_ordinary_egglog() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (rewrite (F a b) (G b a) :when () :name "swap")
        (let start (F $1 $2))
        (run 1)
        (check (= start (G $2 $1)))
        (check (!= start (G $1 $2)))
        (check (slots start $1 $2))
    "#,
    );
}

#[test]
fn named_slots_persist_across_inputs_and_scopes() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    evaluate(&mut compiler, &mut graph, "(let a (F $a $a0))");
    evaluate(
        &mut compiler,
        &mut graph,
        "(push) (let local (F $temp $-9223372036854775808)) (pop)",
    );
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (let b (F $a $-9223372036854775808))
        (run 0)
        (check (= a (F $a $a0)))
        (check (slots a $a $a0))
        (check (slots b $a $-9223372036854775808))
        (check (!= a b))
        (check (!= $a $-9223372036854775808))
    "#,
    );
    assert!(
        compiler
            .compile(None, "(let bad (F $fresh missing))")
            .is_err()
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(let valid (F $fresh $a)) (run 0) (check (slots valid $fresh $a))",
    );
}

#[test]
fn binder_columns_require_slots() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    for source in [
        "(let bad (Lam (Null) (Null)))",
        "(let alias (F $a $a)) (let bad (Lam alias (Null)))",
        "(rewrite (Lam x a) a)",
        "(rewrite (F x a) (Lam x a))",
        "(let bad (F $9223372036854775808 $a))",
        "(let bad (F $ $a))",
    ] {
        assert!(
            compiler.compile(None, source).is_err(),
            "accepted: {source}"
        );
    }
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (constructor Tagged (String U U) U :binder 0)
        (let id (Tagged "lambda" $a $a))
        (run 0)
        (check (= id (Tagged "lambda" $b $b)))
        (check (slots id))
    "#,
    );
}

#[test]
fn slots_require_an_explicit_variant_and_follow_scopes() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(
        &mut compiler,
        &mut graph,
        "(datatype Expr (Null) (F Expr Expr))",
    );
    for source in [
        "(let bad (F $a (Null)))",
        "(check (= $a $a))",
        "(union (Null) $a)",
        "(rewrite (F a b) $fresh)",
        "(rewrite (F a b) (subst a $x b))",
        "(constructor Lam (Expr Expr) Expr :binder 0)",
        "(constructor $Var (Expr) Expr)",
        "(constructor $Var () Expr :binder 0)",
        "(constructor $Var () Missing)",
        "(constructor $Other () Expr)",
        "(constructor $Var () Expr) (let bad missing)",
    ] {
        assert!(
            compiler.compile(None, source).is_err(),
            "accepted: {source}"
        );
        assert!(compiler.compile(None, "(let bad (F $a $b))").is_err());
    }
    evaluate(
        &mut compiler,
        &mut graph,
        "(push) (constructor $Var () Expr) (let a (F $a $b)) (run 0)",
    );
    assert_eq!(graph.get_size("SlottedVar_0"), 1);
    assert!(
        compiler
            .compile(None, "(constructor $Var () Expr)")
            .is_err()
    );
    evaluate(&mut compiler, &mut graph, "(pop)");
    assert_eq!(graph.get_size("SlottedVar_0"), 0);
    assert!(compiler.compile(None, "(let bad (F $a $b))").is_err());
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (constructor $Var () Expr)
        (constructor Lam (Expr Expr) Expr :binder 0)
        (let id (Lam $a $a))
        (let value (F $a (Null)))
        (run 0)
        (check (= id (Lam $b $b)))
        (check (slots value $a))
    "#,
    );
}

#[test]
fn variable_variants_are_per_sort_and_var_is_an_ordinary_name() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (datatype*
            (Expr (Lam Expr Expr :binder 0) ($Var))
            (Var (Name String) (Wrap Var))
            (Ty ($Var) (Pair Ty Ty)))
        (let id (Lam $a $a))
        (let name (Wrap (Name "x")))
        (let ty (Pair $a $b))
        (run 0)
        (check (= id (Lam $b $b)))
        (check (slots name))
        (check (slots ty $a $b))
    "#,
    );
    assert_eq!(graph.get_size("SlottedVar_0"), 1);
    assert_eq!(graph.get_size("SlottedVar_1"), 0);
    assert_eq!(graph.get_size("SlottedVar_2"), 1);
    assert!(compiler.compile(None, "(let bad (Wrap $a))").is_err());
    assert!(compiler.compile(None, "(let bad ($Var))").is_err());
    assert!(
        compiler
            .compile(None, "(datatype Bad ($Var) ($Var))")
            .is_err()
    );
}

#[test]
fn scopes_restore_declarations_globals_and_rules() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (push)
        (datatype U ($Var) (F U))
        (let local (F $0))
        (rewrite (F a) (F (F a)))
        (pop)
        (datatype U ($Var) (F U U))
        (let local (F $1 $2))
        (run 0)
        (check (slots local $1 $2))
    "#,
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(push) (datatype V ($Var) (Zero)) (let n (Zero)) (run 0)",
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(pop) (datatype V ($Var) (One)) (let n (One)) (run 0)",
    );
    assert!(compiler.compile(None, "(let bad (Zero))").is_err());
}

#[test]
fn compilation_errors_are_transactional_and_located() {
    let mut compiler = Compiler::default();
    let error = compiler
        .compile(
            Some("bad.egg".into()),
            "(datatype U ($Var) (F U))\n(let x missing)",
        )
        .unwrap_err();
    assert!(error.to_string().contains("bad.egg"));
    assert!(compiler.compile(None, LANGUAGE).is_ok());
    for source in [
        "(ruleset slotted-group)",
        r#"(datatype "bad)" (Zero))"#,
        r#"(constructor "bad)" () U)"#,
        "(let x (F $0 $1)) (let x x)",
        "(constructor SlottedVar_0 () U)",
        "(sort Idx) (constructor $Var () Idx)",
        "(rewrite (F a b) a :when (= a b))",
        "(rewrite (Lam x a) a)",
        "(constructor Broken (U U) U :binder 18446744073709551615)",
    ] {
        assert!(
            compiler.compile(None, source).is_err(),
            "accepted: {source}"
        );
    }
}

#[test]
fn matching_policy_changes_aliasing_and_checks_remain_unrestricted() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options { no_aliasing });
        let mut graph = egglog_experimental::slotted::new_egraph();
        evaluate(&mut compiler, &mut graph, LANGUAGE);
        evaluate(
            &mut compiler,
            &mut graph,
            r#"
            (union (G $0 (Null)) (Null))
            (let start (F $1 (Null)))
            (rewrite (F a (G b n)) (H a b))
            (run 1)
        "#,
        );
        let claim = "(check (= start (H $1 $1)))";
        let claim = if no_aliasing {
            format!("(fail {claim})")
        } else {
            claim.to_owned()
        };
        evaluate(&mut compiler, &mut graph, &claim);
    }
}

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "slotted-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}
fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
}

#[test]
fn cli_reuses_files_includes_serialization_and_timing_reports() {
    let temp = Temp::new();
    std::fs::write(temp.0.join("language.egg"), LANGUAGE).unwrap();
    std::fs::write(
        temp.0.join("first.egg"),
        "(include \"language.egg\")\n(let input (F $a $a0))",
    )
    .unwrap();
    std::fs::write(
        temp.0.join("second.egg"),
        "(rewrite (F a b) (G b a))\n(run 1)\n(check (= input (G $a0 $a)))",
    )
    .unwrap();
    let result = cli()
        .current_dir(&temp.0)
        .args([
            "--slotted",
            "--to-json",
            "--timing-summary",
            "timing.json",
            "first.egg",
            "second.egg",
        ])
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    for file in ["first.json", "second.json", "timing.json"] {
        let data = std::fs::read(temp.0.join(file)).unwrap();
        serde_json::from_slice::<serde_json::Value>(&data).unwrap();
    }
}

fn repl(source: &str) -> std::process::Output {
    let mut child = cli()
        .args(["--slotted", "--mode", "interactive"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    writeln!(input, "{source}").unwrap();
    drop(input);
    child.wait_with_output().unwrap()
}

#[test]
fn cli_transforms_complete_stdin_commands() {
    let result = repl(&format!(
        "{LANGUAGE}\n(let input (F $a\n $a0))\n(run 0)\n(check (slots input $a $a0))"
    ));
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert!(!stdout.contains("(error)"), "{stdout}");
    assert_eq!(stdout.matches("(done)").count(), 4, "{stdout}");
}

#[test]
fn cli_recovers_compiler_and_egraph_after_failed_inputs() {
    let result = repl(
        "(datatype U ($Var) (Null)) (function broken)\n\
         (datatype U ($Var) (Null) (One))\n\
         (let transient (Null)) (check (= (Null) (One))) (let later (One))\n\
         (fail (check (= (Null) (Null))))\n\
         (let transient (One)) (let later (Null)) (run 0)\n\
         (check (holds transient One)) (check (holds later Null))\n\
         (push)\n\
         (pop) (datatype V ($Var) (Gone)) (check (= (Null) (One)))\n\
         (pop)\n\
         (datatype V ($Var) (Kept)) (let x (Kept)) (run 0) (check (holds x Kept))\n\
         (datatype W ($Var) (BadCtor)) (function cost (Missing) i64 :no-merge)\n\
         (datatype W ($Var) (GoodCtor))\n\
         (let typed (GoodCtor)) (run 0) (check (holds typed GoodCtor))",
    );
    let stdout = String::from_utf8(result.stdout).unwrap();
    let stderr = String::from_utf8(result.stderr).unwrap();
    assert!(result.status.success(), "{stdout}\n{stderr}");
    assert_eq!(stdout.matches("(error)").count(), 4, "{stdout}\n{stderr}");
    assert_eq!(stdout.matches("(done)").count(), 9, "{stdout}\n{stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
}

#[test]
fn cli_explains_flags_and_rejects_incompatible_modes() {
    let help = cli().arg("--help").output().unwrap();
    assert!(help.status.success());
    assert!(
        String::from_utf8(help.stdout)
            .unwrap()
            .contains("--slotted")
    );
    for flags in [vec!["--slotted-no-aliasing"], vec!["--slotted", "--proofs"]] {
        let result = cli().args(flags).output().unwrap();
        assert_eq!(result.status.code(), Some(2));
        assert!(
            !String::from_utf8(result.stderr)
                .unwrap()
                .contains("panicked")
        );
    }
}

#[test]
fn side_patterns_can_bind_the_rewrite_root() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (let start (F (G $a $b) (Null)))
        (rewrite child (H $x $y) :when ((= parent (F child n)) (= child (G $x $y))))
        (run 1)
        (check (= (G $a $b) (H $a $b)))
        (check (!= (G $a $b) (H $b $a)))
    "#,
    );
    for source in [
        "(rewrite missing (Null))",
        "(rewrite missing (Null) :when ((= other (Null))))",
    ] {
        assert!(compiler.compile(None, source).is_err(), "{source}");
    }
}
