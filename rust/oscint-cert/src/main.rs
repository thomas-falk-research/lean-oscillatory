//! Command line of the checker.
//!
//!   oscint-cert check <certificate.json|-> --statements <statements.json>
//!   oscint-cert make <kind> --inputs '<json>' --statements <statements.json> [--claim-bits N]
//!
//! Exit codes: 0 CERTIFIED (or certificate written), 1 REJECTED,
//! 2 UNRESOLVED, 3 usage or input error.

#![forbid(unsafe_code)]

use oscint_cert::check::{check_guarded, load_statements, make, StatementList};
use std::io::{Read, Write};
use std::process::ExitCode;

const USAGE: &str = "usage:\n  oscint-cert check <certificate.json|-> --statements <statements.json>\n  oscint-cert make <kind> --inputs '<json>' --statements <statements.json> [--claim-bits N]";

fn usage_error(message: &str) -> ExitCode {
    eprintln!("oscint-cert: {message}\n{USAGE}");
    ExitCode::from(3)
}

/// Positional arguments, and options with their values.
type SplitArgs = (Vec<String>, Vec<(String, String)>);

/// Splits the arguments after the subcommand into positionals and options.
fn split_args(args: &[String], options: &[&str]) -> Result<SplitArgs, String> {
    let mut positional = Vec::new();
    let mut named = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        if options.contains(&a.as_str()) {
            let value = args.get(i + 1).ok_or_else(|| format!("{a} needs a value"))?;
            if named.iter().any(|(k, _): &(String, String)| k == a) {
                return Err(format!("{a} given twice"));
            }
            named.push((a.clone(), value.clone()));
            i += 2;
        } else if a.starts_with("--") {
            return Err(format!("unknown option {a}"));
        } else {
            positional.push(a.clone());
            i += 1;
        }
    }
    Ok((positional, named))
}

fn option<'a>(named: &'a [(String, String)], key: &str) -> Option<&'a str> {
    named.iter().find(|(k, _)| k == key).map(|(_, v)| v.as_str())
}

fn read_statements(path: Option<&str>) -> Result<StatementList, String> {
    let path = path.ok_or_else(|| "--statements <statements.json> is required".to_string())?;
    let bytes = std::fs::read(path).map_err(|e| format!("cannot read {path}: {e}"))?;
    load_statements(&bytes)
}

fn print_json(value: &serde_json::Value) -> Result<(), String> {
    let text = serde_json::to_string_pretty(value).map_err(|e| e.to_string())?;
    let mut out = std::io::stdout().lock();
    writeln!(out, "{text}")
        .and_then(|()| out.flush())
        .map_err(|e| e.to_string())
}

fn main() -> ExitCode {
    let args: Vec<String> = match std::env::args_os().skip(1).map(|a| a.into_string()).collect() {
        Ok(a) => a,
        Err(_) => return usage_error("arguments must be UTF-8"),
    };
    let Some(command) = args.first() else {
        return usage_error("no subcommand");
    };
    match command.as_str() {
        "check" => {
            let (positional, named) = match split_args(&args[1..], &["--statements"]) {
                Ok(r) => r,
                Err(e) => return usage_error(&e),
            };
            if positional.len() != 1 {
                return usage_error("check takes exactly one certificate path (or -)");
            }
            let stmts = match read_statements(option(&named, "--statements")) {
                Ok(s) => s,
                Err(e) => return usage_error(&e),
            };
            let path = positional[0].as_str();
            let cert = if path == "-" {
                let mut buffer = Vec::new();
                match std::io::stdin().lock().read_to_end(&mut buffer) {
                    Ok(_) => buffer,
                    Err(e) => return usage_error(&format!("cannot read standard input: {e}")),
                }
            } else {
                match std::fs::read(path) {
                    Ok(b) => b,
                    Err(e) => return usage_error(&format!("cannot read {path}: {e}")),
                }
            };
            let (status, verdict) = check_guarded(&cert, &stmts);
            match print_json(&verdict) {
                Ok(()) => ExitCode::from(status.exit_code()),
                Err(e) => usage_error(&format!("cannot write the verdict: {e}")),
            }
        }
        "make" => {
            let (positional, named) =
                match split_args(&args[1..], &["--statements", "--inputs", "--claim-bits"]) {
                    Ok(r) => r,
                    Err(e) => return usage_error(&e),
                };
            if positional.len() != 1 {
                return usage_error("make takes exactly one kind");
            }
            let Some(inputs) = option(&named, "--inputs") else {
                return usage_error("--inputs '<json>' is required");
            };
            let claim_bits = match option(&named, "--claim-bits") {
                None => 96,
                Some(s) => match s.parse::<u64>() {
                    Ok(b) if (8..=240).contains(&b) => b,
                    _ => return usage_error("--claim-bits must be an integer from 8 to 240"),
                },
            };
            let stmts = match read_statements(option(&named, "--statements")) {
                Ok(s) => s,
                Err(e) => return usage_error(&e),
            };
            let made = std::panic::catch_unwind(|| make(&positional[0], inputs, &stmts, claim_bits));
            match made {
                Ok(Ok(cert)) => match print_json(&cert) {
                    Ok(()) => ExitCode::SUCCESS,
                    Err(e) => usage_error(&format!("cannot write the certificate: {e}")),
                },
                Ok(Err(e)) => {
                    eprintln!("oscint-cert: no certificate made: {e}");
                    ExitCode::from(3)
                }
                Err(_) => {
                    eprintln!("oscint-cert: internal error while making the certificate");
                    ExitCode::from(3)
                }
            }
        }
        "--help" | "-h" | "help" => {
            println!("{USAGE}");
            ExitCode::SUCCESS
        }
        other => usage_error(&format!("unknown subcommand {other:?}")),
    }
}
