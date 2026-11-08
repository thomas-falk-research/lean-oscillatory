// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! `audit AUDIT_OUTPUT ROOT NAMES_OUT`: checks the stdout of `lake env lean Axioms.lean`.
//! Every `AUDIT <name> <axioms>` line must list `none` or a subset of {propext, Classical.choice, Quot.sound};
//! the `AUDIT-TOTAL n clean` line must agree with the lines; and `n` must equal the guard's count of
//! `theorem`/`lemma` declarations under ROOT. Writes the audited names (one per line) to NAMES_OUT.

use std::fs;
use std::path::Path;

#[path = "guard.rs"]
#[allow(dead_code)]
mod guard;

const PERMITTED: &[&str] = &["propext", "Classical.choice", "Quot.sound"];

pub fn check(out: &str, expected: usize) -> Result<Vec<String>, String> {
    let mut names = Vec::new();
    let mut total: Option<(usize, usize)> = None;
    for line in out.lines() {
        let t: Vec<&str> = line.split_whitespace().collect();
        match t.as_slice() {
            ["AUDIT", name, axs] => {
                if *axs != "none" && !axs.split(',').all(|a| PERMITTED.contains(&a)) {
                    return Err(format!("{name} uses non-permitted axioms: {axs}"));
                }
                names.push(name.to_string());
            }
            ["AUDIT-TOTAL", n, c] => {
                total = Some((n.parse().map_err(|_| "bad total")?, c.parse().map_err(|_| "bad total")?));
            }
            _ if line.starts_with("AUDIT") => return Err(format!("malformed audit line: {line}")),
            _ => {}
        }
    }
    let (n, c) = total.ok_or("no AUDIT-TOTAL line (audit did not run to completion)")?;
    if n != names.len() || c != n {
        return Err(format!("AUDIT-TOTAL {n} {c} disagrees with {} audited line(s)", names.len()));
    }
    if n == 0 {
        return Err("empty audit".into());
    }
    if n != expected {
        return Err(format!("audit enumerated {n} theorem(s) but the sources declare {expected}"));
    }
    Ok(names)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 4 {
        eprintln!("usage: audit AUDIT_OUTPUT ROOT NAMES_OUT");
        std::process::exit(2);
    }
    let out = fs::read_to_string(&a[1]).unwrap_or_default();
    let expected = guard::scan(Path::new(&a[2])).theorems;
    match check(&out, expected) {
        Ok(names) => {
            fs::write(&a[3], names.join("\n") + "\n").expect("write names");
            println!("axiom audit: {} of {} theorems clean (permitted: {})", names.len(), expected, PERMITTED.join(", "));
        }
        Err(e) => {
            println!("axiom audit: FAIL: {e}");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn clean_and_subsets_pass() {
        let o = "AUDIT A.x propext,Classical.choice,Quot.sound\nAUDIT A.y none\nAUDIT A.z propext\nAUDIT-TOTAL 3 3\n";
        assert_eq!(check(o, 3).unwrap().len(), 3);
    }
    #[test]
    fn failures() {
        assert!(check("AUDIT A.x sorryAx\nAUDIT-TOTAL 1 0\n", 1).is_err());
        assert!(check("AUDIT A.x propext,A.x._native.native_decide.ax_1\nAUDIT-TOTAL 1 0\n", 1).is_err());
        assert!(check("AUDIT A.x none\n", 1).is_err());
        assert!(check("AUDIT A.x none\nAUDIT-TOTAL 1 1\n", 2).is_err());
        assert!(check("AUDIT-TOTAL 0 0\n", 0).is_err());
        assert!(check("AUDIT A.x none\nAUDIT-TOTAL 2 2\n", 2).is_err());
    }
}
