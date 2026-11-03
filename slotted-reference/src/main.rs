//! Frozen-workload driver. The shared Python runner owns all timing and RSS measurement.
use slotted_reference::{run_spec, select_frozen_spec, Matcher, Substitution};

#[global_allocator]
static ALLOCATOR: benchmark_memory::LimitedAllocator = benchmark_memory::LimitedAllocator;

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    let args = benchmark_memory::configure(std::env::args_os());
    let mut args = args.into_iter().skip(1);
    let mut matcher = Matcher::Multi;
    let mut policy = Substitution::Snapshot;
    let mut file = None;
    while let Some(arg) = args.next() {
        match arg.to_str() {
            Some("--help" | "-h") => {
                println!("slotted-reference [--matcher multi|nested] [--substitution snapshot|syntactic|extraction] [--memory-limit-bytes N] FILE.ref");
                return Ok(());
            }
            Some("--matcher") => {
                matcher = match args.next().as_deref().and_then(|v| v.to_str()) {
                    Some("multi") => Matcher::Multi,
                    Some("nested") => Matcher::Nested,
                    _ => return Err("--matcher requires multi or nested".into()),
                }
            }
            Some("--substitution") => {
                policy = match args.next().as_deref().and_then(|v| v.to_str()) {
                    Some("snapshot") => Substitution::Snapshot,
                    Some("syntactic") => Substitution::Syntactic,
                    Some("extraction") => Substitution::Extraction,
                    _ => {
                        return Err(
                            "--substitution requires snapshot, syntactic or extraction".into()
                        )
                    }
                }
            }
            Some(value) if value.starts_with('-') => {
                return Err(format!("unknown option: {value}"))
            }
            _ if file.is_none() => file = Some(std::path::PathBuf::from(arg)),
            _ => return Err("expected one frozen workload file".into()),
        }
    }
    let file = file.ok_or("expected a frozen workload file")?;
    let source =
        std::fs::read_to_string(&file).map_err(|error| format!("{}: {error}", file.display()))?;
    let spec = select_frozen_spec(&source, matcher)?;
    println!(
        "CONFIG checks={} matcher={matcher:?} substitution={policy:?}",
        slotted_reference::CHECKS_ENABLED
    );
    let outcome = run_spec(&spec, policy)?;
    if let Some(saturated) = outcome.saturated {
        println!("SATURATED {}", if saturated { "yes" } else { "no" });
    }
    let missing_goal = outcome.goals.iter().any(|reached| !reached);
    for reached in outcome.goals {
        println!("GOAL {}", if reached { "yes" } else { "no" });
    }
    println!("SIZES {} {}", outcome.classes, outcome.nodes);
    println!("PARTITION {}", outcome.partition);
    if let Some(graph) = outcome.graph {
        println!(
            "GRAPH {}",
            serde_json::to_string(&graph).map_err(|error| error.to_string())?
        );
    }
    if missing_goal {
        return Err("reference did not establish the prescribed target".into());
    }
    Ok(())
}
