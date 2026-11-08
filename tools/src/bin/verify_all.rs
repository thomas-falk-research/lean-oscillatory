// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! `verify-all`: runs each verification target with `make` and prints one line per step and a final verdict:
//! PASS only if every step passed; INCOMPLETE if none failed but some step was skipped (exit status 3 from the
//! step: nothing to check yet); FAIL otherwise. Exit 0 / 3 / 1 respectively.
//! `verify_all --only STEP [--only STEP …]` runs only the named steps, in the order of `STEPS` (same verdict rules;
//! the header says which steps ran, so a partial run is never mistaken for a full one).

use std::process::Command;

const STEPS: &[&str] =
    &["verify-toolchain", "tools-test", "guard", "lean", "lean-replay", "commit", "comparator", "stamp-verify", "statements-check"];

/// The steps selected by `--only` arguments (all steps without any); an unknown step is an error naming the valid ones.
pub fn select(args: &[String]) -> Result<Vec<&'static str>, String> {
    let mut only = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--only" => only.push(it.next().ok_or("--only needs a step name")?.clone()),
            other => return Err(format!("unknown argument {other:?}; usage: verify_all [--only STEP]...")),
        }
    }
    for o in &only {
        if !STEPS.contains(&o.as_str()) {
            return Err(format!("unknown step {o:?}; steps: {}", STEPS.join(", ")));
        }
    }
    Ok(STEPS.iter().copied().filter(|s| only.is_empty() || only.iter().any(|o| o == s)).collect())
}

pub fn verdict(codes: &[Option<i32>]) -> (&'static str, i32) {
    if codes.iter().any(|c| !matches!(c, Some(0) | Some(3))) {
        ("FAIL", 1)
    } else if codes.contains(&Some(3)) {
        ("INCOMPLETE", 3)
    } else {
        ("PASS", 0)
    }
}

/// System tools the steps need, with the package that provides them (lessons 20: a fresh machine without `zstd` and
/// `bwrap` ran 50 minutes before `verify-toolchain` and `lean-replay` failed on them).
const TOOLS: &[(&str, &str)] = &[
    ("lake", "elan (README: Re-check)"),
    ("cargo", "rustup (tools/rust-toolchain.toml)"),
    ("zstd", "zstd (apt-get install zstd)"),
    ("bwrap", "bubblewrap (apt-get install bubblewrap; it needs unprivileged user namespaces)"),
    ("git", "git"),
    ("tar", "tar"),
];

/// The tools from `TOOLS` that are not on `path` (a `PATH`-style list).
pub fn missing(path: &str) -> Vec<(&'static str, &'static str)> {
    TOOLS
        .iter()
        .copied()
        .filter(|(t, _)| !std::env::split_paths(path).any(|d| d.join(t).is_file()))
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let steps = match select(&args) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("verify_all: {e}");
            std::process::exit(2);
        }
    };
    let partial = steps.len() < STEPS.len();
    let miss = missing(&std::env::var("PATH").unwrap_or_default());
    let mut problems: Vec<String> =
        miss.iter().map(|(t, pkg)| format!("`{t}` is not on PATH; install {pkg}")).collect();
    // `stamp-verify` reads the stamped commits from history (lessons 9, 21).
    let shallow = Command::new("git").args(["rev-parse", "--is-shallow-repository"]).output();
    if matches!(&shallow, Ok(o) if String::from_utf8_lossy(&o.stdout).trim() == "true") {
        problems.push("the clone is shallow, so stamped commits are missing; run `git fetch --unshallow`".into());
    }
    if !problems.is_empty() {
        for p in &problems {
            println!("verify-all: FAIL: {p}");
        }
        println!("RESULT FAIL (preflight: {} problem(s); nothing was run)", problems.len());
        std::process::exit(1);
    }
    let mut codes = Vec::new();
    let mut lines = Vec::new();
    for s in &steps {
        let st = Command::new("make").args(["--no-print-directory", s]).status();
        let code = st.ok().and_then(|s| s.code());
        // make reports a recipe's exit status 3 as its own status 2; the recipes signal "skipped" by
        // writing build/skipped/<step> instead.
        let skipped = std::path::Path::new("build/skipped").join(s).exists();
        let c = match code {
            Some(0) if skipped => Some(3),
            other => other,
        };
        lines.push(format!("{:<11} {s}", match c { Some(0) => "PASS", Some(3) => "SKIPPED", _ => "FAIL" }));
        codes.push(c);
    }
    println!("\n== verify-all{}", if partial { format!(" (partial: --only {})", steps.join(" ")) } else { String::new() });
    for l in &lines {
        println!("{l}");
    }
    let (v, code) = verdict(&codes);
    println!("RESULT {v}{}", if partial { " (partial run, not a full verification)" } else { "" });
    std::process::exit(code);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn never_pass_when_skipped() {
        assert_eq!(verdict(&[Some(0), Some(0)]).0, "PASS");
        assert_eq!(verdict(&[Some(0), Some(3)]).0, "INCOMPLETE");
        assert_eq!(verdict(&[Some(3), Some(2)]).0, "FAIL");
        assert_eq!(verdict(&[None]).0, "FAIL");
    }

    #[test]
    fn missing_tools_are_named() {
        let m = missing("/nonexistent-dir-for-test");
        assert_eq!(m.len(), TOOLS.len());
        assert!(m.iter().any(|(t, p)| *t == "bwrap" && p.contains("bubblewrap")));
    }

    #[test]
    fn only_selects_in_step_order_and_rejects_unknown() {
        let a = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert_eq!(select(&a(&[])).unwrap().len(), STEPS.len());
        assert_eq!(select(&a(&["--only", "lean", "--only", "guard"])).unwrap(), vec!["guard", "lean"]);
        assert!(select(&a(&["--only", "nope"])).unwrap_err().contains("steps: verify-toolchain"));
        assert!(select(&a(&["--only"])).is_err());
        assert!(select(&a(&["lean"])).is_err());
    }
}
