use std::ffi::OsString;

// Match the standard egglog executable when comparing experimental encodings.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    let (slotted, encoded, no_aliasing, args) = extract_slotted_args(std::env::args_os())
        .unwrap_or_else(|err| {
            eprintln!("error: {err}");
            std::process::exit(2);
        });
    if args
        .iter()
        .take_while(|arg| *arg != "--")
        .any(|arg| arg == "--help" || arg == "-h")
    {
        println!(
            "Experimental options:\n  --slotted              Transform slotted source before evaluation\n  --slotted-encoded      Evaluate already lowered slotted code\n  --slotted-no-aliasing  Restrict matching to the nested reference's aliasing policy\n"
        );
    }
    let proof_mode = args.iter().take_while(|arg| *arg != "--").any(|arg| {
        matches!(
            arg.to_str(),
            Some("--proofs" | "--proof-testing" | "--proof-extraction" | "--term-encoding")
        )
    });
    if (slotted || encoded) && proof_mode {
        eprintln!("error: --slotted cannot be combined with term/proof encoding");
        std::process::exit(2);
    }
    let egraph = if slotted || encoded {
        egglog_experimental::slotted::new_egraph()
    } else if proof_mode {
        egglog_experimental::new_experimental_egraph_with_native_schedule()
    } else {
        egglog_experimental::new_experimental_egraph()
    };
    if slotted {
        let mut compiler =
            egglog_experimental::slotted::Compiler::new(egglog_experimental::slotted::Options {
                no_aliasing,
            });
        egglog::cli_with_preprocessor(egraph, args, move |filename, source| {
            compiler.compile(filename, source).map_err(Into::into)
        });
    } else {
        egglog::cli_with_args(egraph, args)
    }
}

fn extract_slotted_args(
    args: impl IntoIterator<Item = OsString>,
) -> Result<(bool, bool, bool, Vec<OsString>), String> {
    let (mut slotted, mut encoded, mut no_aliasing) = (false, false, false);
    let mut filtered = Vec::new();
    let mut positional = false;
    for arg in args {
        match arg.to_str() {
            Some("--") => {
                positional = true;
                filtered.push(arg);
            }
            Some("--slotted") if !positional => slotted = true,
            Some("--slotted-encoded") if !positional => encoded = true,
            Some("--slotted-no-aliasing") if !positional => no_aliasing = true,
            _ => filtered.push(arg),
        }
    }
    if no_aliasing && !slotted {
        return Err("--slotted-no-aliasing requires --slotted".into());
    }
    if slotted && encoded {
        return Err("--slotted and --slotted-encoded are mutually exclusive".into());
    }
    Ok((slotted, encoded, no_aliasing, filtered))
}
