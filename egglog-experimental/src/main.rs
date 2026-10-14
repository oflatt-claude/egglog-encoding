use std::ffi::OsString;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Backend {
    Main,
    #[cfg(feature = "dd-backend")]
    Dd,
}

fn main() {
    let (slotted, no_aliasing, args) =
        extract_slotted_args(std::env::args_os()).unwrap_or_else(|err| {
            eprintln!("error: {err}");
            std::process::exit(2);
        });
    let (backend, args) = extract_backend_arg(args).unwrap_or_else(|err| {
        eprintln!("error: {err}");
        std::process::exit(2);
    });
    if args
        .iter()
        .take_while(|arg| *arg != "--")
        .any(|arg| arg == "--help" || arg == "-h")
    {
        println!(
            "Experimental options:\n  --slotted              Transform slotted source before evaluation\n  --slotted-no-aliasing  Restrict matching to the nested reference's aliasing policy\n  --backend <main|dd>    Select the execution backend\n"
        );
    }
    let proof_mode = args.iter().take_while(|arg| *arg != "--").any(|arg| {
        matches!(
            arg.to_str(),
            Some("--proofs" | "--proof-testing" | "--proof-extraction" | "--term-encoding")
        )
    });
    if slotted && proof_mode {
        eprintln!("error: --slotted cannot be combined with term/proof encoding");
        std::process::exit(2);
    }
    #[cfg(feature = "dd-backend")]
    if slotted && backend == Backend::Dd {
        eprintln!("error: --slotted currently requires --backend main");
        std::process::exit(2);
    }
    #[cfg(feature = "dd-backend")]
    let args = if matches!(backend, Backend::Dd) {
        strip_term_encoding_arg(args)
    } else {
        args
    };
    let egraph = match backend {
        Backend::Main if proof_mode || slotted => {
            egglog_experimental::new_experimental_egraph_with_native_schedule()
        }
        Backend::Main => egglog_experimental::new_experimental_egraph(),
        #[cfg(feature = "dd-backend")]
        Backend::Dd => egglog_experimental::new_experimental_egraph_with_backend_for_proofs(
            Box::new(egglog_experimental_dd::EGraph::new()),
        ),
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
) -> Result<(bool, bool, Vec<OsString>), String> {
    let (mut slotted, mut no_aliasing) = (false, false);
    let mut filtered = Vec::new();
    let mut positional = false;
    for arg in args {
        match arg.to_str() {
            Some("--") => {
                positional = true;
                filtered.push(arg);
            }
            Some("--slotted") if !positional => slotted = true,
            Some("--slotted-no-aliasing") if !positional => no_aliasing = true,
            _ => filtered.push(arg),
        }
    }
    if no_aliasing && !slotted {
        return Err("--slotted-no-aliasing requires --slotted".into());
    }
    Ok((slotted, no_aliasing, filtered))
}

fn extract_backend_arg<I>(args: I) -> Result<(Backend, Vec<OsString>), String>
where
    I: IntoIterator<Item = OsString>,
{
    let mut backend = Backend::Main;
    let mut saw_backend = false;
    let mut filtered = Vec::new();
    let mut iter = args.into_iter();
    while let Some(arg) = iter.next() {
        match arg.to_str() {
            Some("--backend") => {
                if saw_backend {
                    return Err("--backend may only be passed once".to_string());
                }
                let Some(value) = iter.next() else {
                    return Err("--backend requires one of: main, dd".to_string());
                };
                backend = parse_backend(value.to_str())?;
                saw_backend = true;
            }
            Some(value) if value.starts_with("--backend=") => {
                if saw_backend {
                    return Err("--backend may only be passed once".to_string());
                }
                backend = parse_backend(value.strip_prefix("--backend="))?;
                saw_backend = true;
            }
            _ => filtered.push(arg),
        }
    }
    Ok((backend, filtered))
}

/// The DD backend always runs under the term encoding, so `--term-encoding` is
/// redundant there; drop it before handing the arguments to the CLI.
#[cfg(feature = "dd-backend")]
fn strip_term_encoding_arg(args: Vec<OsString>) -> Vec<OsString> {
    args.into_iter()
        .filter(|arg| arg.to_str() != Some("--term-encoding"))
        .collect()
}

fn parse_backend(value: Option<&str>) -> Result<Backend, String> {
    match value {
        Some("main") => Ok(Backend::Main),
        #[cfg(feature = "dd-backend")]
        Some("dd") => Ok(Backend::Dd),
        #[cfg(not(feature = "dd-backend"))]
        Some("dd") => Err(
            "backend \"dd\" requires building egglog-experimental with --features dd-backend"
                .to_string(),
        ),
        Some(other) => Err(format!(
            "unknown backend {other:?}; expected one of: main, dd"
        )),
        None => Err("backend value must be valid UTF-8".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_main_backend() {
        assert_eq!(parse_backend(Some("main")), Ok(Backend::Main));
    }

    #[cfg(not(feature = "dd-backend"))]
    #[test]
    fn explains_how_to_enable_dd_backend() {
        assert_eq!(
            parse_backend(Some("dd")),
            Err(
                "backend \"dd\" requires building egglog-experimental with --features dd-backend"
                    .to_string()
            )
        );
    }

    #[cfg(feature = "dd-backend")]
    #[test]
    fn parses_enabled_dd_backend() {
        assert_eq!(parse_backend(Some("dd")), Ok(Backend::Dd));
    }

    #[cfg(feature = "dd-backend")]
    #[test]
    fn dd_backend_arg_filtering_drops_term_encoding() {
        let args = ["egglog", "--backend", "dd", "--term-encoding", "prog.egg"]
            .into_iter()
            .map(OsString::from);
        let (backend, rest) = extract_backend_arg(args).unwrap();
        assert_eq!(backend, Backend::Dd);
        assert_eq!(
            strip_term_encoding_arg(rest),
            vec![OsString::from("egglog"), OsString::from("prog.egg")]
        );
    }
}
