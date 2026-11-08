// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! `toolchain ROOT`: checks the pins in `ROOT/toolchain.sha256` (`<sha256>  <file>  <url>` lines): downloads
//! each file to `ROOT/build/toolchain/` unless already present with the pinned hash, checks the hash, then
//! extracts the Lean archive and requires it to be byte-identical (`diff -r`) to the installed toolchain
//! (`lake env printenv LEAN_SYSROOT`), and requires `ROOT/lean-toolchain` to name the archive's version.

use oscint_tools::sys::{run, sha256_file};
use std::fs;
use std::path::Path;
use std::process::Command;

fn go(root: &Path) -> Result<Vec<String>, String> {
    let pins = fs::read_to_string(root.join("toolchain.sha256")).map_err(|e| format!("toolchain.sha256: {e}"))?;
    let dir = root.join("build/toolchain");
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let mut report = Vec::new();
    let mut archive = None;
    for l in pins.lines().filter(|l| !l.trim().is_empty()) {
        let t: Vec<&str> = l.split_whitespace().collect();
        let [h, name, url] = t[..] else { return Err(format!("bad pin line: {l}")) };
        let p = dir.join(name);
        if !p.exists() || sha256_file(&p)? != h {
            let (ok, _, e) = run(Command::new("curl").args(["-sSfL", "-m", "1800", "-o"]).arg(&p).arg(url))?;
            if !ok {
                return Err(format!("download {url}: {e}"));
            }
        }
        let got = sha256_file(&p)?;
        if got != h {
            return Err(format!("{name}: sha256 {got}, pinned {h}"));
        }
        report.push(format!("{name}: sha256 {h} OK"));
        if name.ends_with(".tar.zst") {
            archive = Some(name.to_string());
        }
    }
    let archive = archive.ok_or("no .tar.zst archive pinned")?;
    let stem = archive.trim_end_matches(".tar.zst");
    let version = stem.trim_start_matches("lean-").trim_end_matches("-linux");
    let tc = fs::read_to_string(root.join("lean-toolchain")).map_err(|e| e.to_string())?;
    if tc.trim() != format!("leanprover/lean4:v{version}") {
        return Err(format!("lean-toolchain is `{}`, pinned archive is v{version}", tc.trim()));
    }
    let x = dir.join("extract");
    let _ = fs::remove_dir_all(&x);
    fs::create_dir_all(&x).map_err(|e| e.to_string())?;
    let (ok, _, e) = run(Command::new("tar").arg("--zstd").arg("-xf").arg(dir.join(&archive)).arg("-C").arg(&x))?;
    if !ok {
        return Err(format!("tar: {e}"));
    }
    let (ok, sysroot, e) = run(Command::new("lake").current_dir(root).args(["env", "printenv", "LEAN_SYSROOT"]))?;
    if !ok {
        return Err(format!("lake env: {e}"));
    }
    let sysroot = sysroot.trim();
    let (same, o, e) = run(Command::new("diff").arg("-rq").arg(x.join(stem)).arg(sysroot))?;
    if !same {
        return Err(format!("installed toolchain {sysroot} differs from the pinned archive: {}{}", o.lines().take(5).collect::<Vec<_>>().join("; "), e));
    }
    let _ = fs::remove_dir_all(&x);
    report.push(format!("installed toolchain {sysroot} is byte-identical to {archive}"));
    Ok(report)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 2 {
        eprintln!("usage: toolchain ROOT");
        std::process::exit(2);
    }
    match go(Path::new(&a[1])) {
        Ok(r) => r.iter().for_each(|l| println!("verify-toolchain: {l}")),
        Err(e) => {
            println!("verify-toolchain: FAIL: {e}");
            std::process::exit(1);
        }
    }
}
