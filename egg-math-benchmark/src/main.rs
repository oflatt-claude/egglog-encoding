use anyhow::Result;
use clap::{Parser, ValueEnum};
use egg_math_benchmark::{ProofMode, run_math, write_timing_summary};
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
enum ProofModeArg {
    #[default]
    Off,
    Enabled,
    Extract,
    Check,
}

impl From<ProofModeArg> for ProofMode {
    fn from(value: ProofModeArg) -> Self {
        match value {
            ProofModeArg::Off => Self::Off,
            ProofModeArg::Enabled => Self::Enabled,
            ProofModeArg::Extract => Self::Extract,
            ProofModeArg::Check => Self::Check,
        }
    }
}

#[derive(Debug, Parser)]
#[command(about = "Run the fixed PLDI 2023 Math workload with current egg")]
struct Args {
    #[arg(long)]
    iterations: usize,
    #[arg(long)]
    check_left: String,
    #[arg(long)]
    check_right: String,
    #[arg(long, value_enum, default_value_t)]
    proof_mode: ProofModeArg,
    #[arg(long)]
    timing_summary: Option<PathBuf>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let result = run_math(
        args.iterations,
        &args.check_left,
        &args.check_right,
        args.proof_mode.into(),
    )?;
    if let Some(path) = args.timing_summary {
        write_timing_summary(&path, &result.timing)?;
    }
    Ok(())
}
