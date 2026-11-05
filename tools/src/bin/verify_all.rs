#![forbid(unsafe_code)]
//! `verify-all`: runs each verification target with `make` and prints one line per step and a final verdict:
//! PASS only if every step passed; INCOMPLETE if none failed but some step was skipped (exit status 3 from the
//! step: nothing to check yet); FAIL otherwise. Exit 0 / 3 / 1 respectively.

use std::process::Command;

const STEPS: &[&str] = &["verify-toolchain", "tools-test", "guard", "lean", "lean-replay", "commit", "comparator", "stamp-verify"];

pub fn verdict(codes: &[Option<i32>]) -> (&'static str, i32) {
    if codes.iter().any(|c| !matches!(c, Some(0) | Some(3))) {
        ("FAIL", 1)
    } else if codes.contains(&Some(3)) {
        ("INCOMPLETE", 3)
    } else {
        ("PASS", 0)
    }
}

fn main() {
    let mut codes = Vec::new();
    let mut lines = Vec::new();
    for s in STEPS {
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
    println!("\n== verify-all");
    for l in &lines {
        println!("{l}");
    }
    let (v, code) = verdict(&codes);
    println!("RESULT {v}");
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
}
