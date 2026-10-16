use egglog_experimental::slotted::{Compiler, Options};
use libtest_mimic::Trial;
use std::path::Path;

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    // Includes resolve from the invocation directory, as in the CLI.
    std::env::set_current_dir(root).unwrap();
    let mut tests = Vec::new();
    for pattern in ["slotted/tests/**/*.egg", "slotted/languages/*.egg"] {
        for path in glob::glob(pattern).unwrap() {
            let path = path.unwrap();
            let name = path
                .strip_prefix("slotted")
                .unwrap()
                .to_str()
                .unwrap()
                .to_owned();
            let snapshot = name.trim_end_matches(".egg").replace('/', "__");
            tests.push(Trial::test(name, move || {
                let source = std::fs::read_to_string(&path)?;
                let mut compiler = Compiler::new(Options {
                    no_aliasing: path.starts_with("slotted/tests/nested"),
                });
                let encoded = compiler.compile(Some(path.display().to_string()), &source)?;
                let mut settings = insta::Settings::clone_current();
                settings.set_snapshot_path("../../slotted/tests/snapshots");
                settings.set_prepend_module_to_snapshot(false);
                settings.set_input_file(&path);
                settings.bind(|| insta::assert_snapshot!(snapshot, encoded));
                Ok(())
            }));
        }
    }
    assert!(!tests.is_empty(), "no slotted fixtures found");
    libtest_mimic::run(&args, tests).exit();
}
