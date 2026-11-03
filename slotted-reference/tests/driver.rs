//! Exercise the workload-driver protocol used by the shared benchmark runner.
use std::process::Command;

#[test]
fn matcher_and_substitution_flags_drive_the_selected_frozen_representation() {
    let input = tempfile::NamedTempFile::new().unwrap();
    let head = "rounds 1\nterm (app (lam $0 (g (var $0) (null))) (null))\nunion (g (var $0) (null)) (f (var $0) (null))\nrule\n";
    let multi = format!("{head}atom root app lam t\natom lam lam $x body\nrhs root ?body[(var $x) := ?t]\ngoal (f (null) (null))\n");
    let nested = format!("{head}nested (app (lam $x ?body) ?t)\nrhs root ?body[(var $x) := ?t]\ngoal (g (null) (null))\n");
    std::fs::write(
        input.path(),
        serde_json::to_vec(&serde_json::json!({"multi":multi,"nested":nested})).unwrap(),
    )
    .unwrap();
    for (matcher, substitution) in [("multi", "snapshot"), ("nested", "syntactic")] {
        let output = Command::new(env!("CARGO_BIN_EXE_slotted-reference"))
            .args(["--matcher", matcher, "--substitution", substitution])
            .arg(input.path())
            .env("XMULTI_SUBST", "invalid-ambient-policy")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("GOAL yes"));
        assert!(stdout.contains("SIZES "));
    }
    // A policy that does not reach the frozen target is a failed workload.
    let failed = Command::new(env!("CARGO_BIN_EXE_slotted-reference"))
        .args(["--matcher", "nested", "--substitution", "snapshot"])
        .arg(input.path())
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(String::from_utf8_lossy(&failed.stdout).contains("GOAL no"));
}

#[test]
fn driver_advertises_workload_arguments_without_a_timing_summary_interface() {
    let output = Command::new(env!("CARGO_BIN_EXE_slotted-reference"))
        .arg("--help")
        .output()
        .unwrap();
    assert!(output.status.success());
    let help = String::from_utf8(output.stdout).unwrap();
    assert!(
        help.contains("--matcher")
            && help.contains("--substitution")
            && help.contains("--memory-limit-bytes")
    );
    assert!(!help.contains("timing-summary"));
}
