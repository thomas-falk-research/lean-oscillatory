// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! Statement matching against the frozen challenge.
//! One comparator configuration per milestone (`comparator.json`, `comparator-S2S3.json`, ...), each frozen by
//! its own stamp (`stamps/pins.txt` line `challenge:<config> <stamp dir>`).
//! `challenge export ROOT CONFIG`: reads `ROOT/CONFIG`, builds the `challenge_module` and exports its
//! `theorem_names` (plus the constants the comparator requires) with `leanexport` into
//! `build/challenge/<stem>.ndjson` (`make stamp` records its SHA-256).
//! `challenge check ROOT CONFIG STAMPDIR`: exit 3 (skipped) if no challenge theorem of CONFIG is declared in
//! the library yet (per `build/audited.txt`), failure if only some are; otherwise re-exports, requires the export's SHA-256 to appear as a `challenge-export`
//! line of `STAMPDIR/manifest.txt` (so the challenge judged is the stamped one: `lake comparator
//! --challenge-from-export` does not check provenance itself), then runs
//! `lake comparator --config CONFIG --challenge-from-export <export> --paranoid`.

use oscint_tools::json;
use oscint_tools::sys::{run, sha256_file};
use std::fs;
use std::path::Path;
use std::process::Command;

/// Constants `lake comparator` requires to be present in a challenge export (permitted axioms and the kernel's
/// built-in extensions): copied from its `Exporting #[…]` line under Lean v4.35.0 (2026-11-05).
pub const REQUIRED: &[&str] = &[
    "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "propext", "Quot.sound", "Classical.choice", "Nat.add", "Nat.sub",
    "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String",
    "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
];

/// Export file stem: `comparator.json` keeps its historical name `challenge`.
fn stem(config: &str) -> String {
    let s = config.trim_end_matches(".json");
    if s == "comparator" { "challenge".to_string() } else { s.trim_start_matches("comparator-").to_string() }
}

fn export(root: &Path, config: &str) -> Result<std::path::PathBuf, String> {
    let cfg = json::parse(&fs::read_to_string(root.join(config)).map_err(|e| format!("{config}: {e}"))?)?;
    let module = cfg.get("challenge_module").and_then(|v| v.as_str()).ok_or("comparator.json: challenge_module")?;
    let names: Vec<&str> = cfg.get("theorem_names").and_then(|v| v.as_arr()).ok_or("comparator.json: theorem_names")?
        .iter().filter_map(|v| v.as_str()).collect();
    if names.is_empty() {
        return Err("comparator.json lists no theorems".into());
    }
    if cfg.get("definition_names").and_then(|v| v.as_arr()).is_none_or(|v| !v.is_empty()) {
        return Err("comparator.json: definition_names must be present and empty".into());
    }
    let dir = root.join("build/challenge");
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let out = dir.join(format!("{}.ndjson", stem(config)));
    let (ok, _, e) = run(Command::new("lake").current_dir(root).args(["build", module]))?;
    if !ok {
        return Err(format!("lake build {module}: {e}"));
    }
    let mut args = vec!["env", "leanexport", module, "--"];
    args.extend(names.iter().copied());
    args.extend(REQUIRED.iter().copied());
    let res = Command::new("lake").current_dir(root).args(&args).output().map_err(|e| e.to_string())?;
    if !res.status.success() || !res.stderr.is_empty() {
        return Err(format!("leanexport: {}", String::from_utf8_lossy(&res.stderr)));
    }
    fs::write(&out, &res.stdout).map_err(|e| e.to_string())?;
    println!("challenge: export {} sha256 {}", out.display(), sha256_file(&out)?);
    Ok(out)
}

/// Which challenge theorems the built library already declares (from the audit's name list).
fn solved(root: &Path, names: &[&str]) -> Result<usize, String> {
    let audited = fs::read_to_string(root.join("build/audited.txt"))
        .map_err(|e| format!("build/audited.txt (run make lean first): {e}"))?;
    let have: Vec<&str> = audited.lines().collect();
    Ok(names.iter().filter(|n| have.contains(n)).count())
}

/// Ok(false): nothing to judge yet (no challenge theorem is declared in the library).
fn check(root: &Path, config: &str, stamp: &Path) -> Result<bool, String> {
    let cfg = json::parse(&fs::read_to_string(root.join(config)).map_err(|e| format!("{config}: {e}"))?)?;
    let names: Vec<&str> = cfg.get("theorem_names").and_then(|v| v.as_arr()).ok_or("comparator.json: theorem_names")?
        .iter().filter_map(|v| v.as_str()).collect();
    match solved(root, &names)? {
        0 => return Ok(false),
        k if k < names.len() => {
            return Err(format!("only {k} of {} challenge theorems are declared; a partial solution is not judged", names.len()))
        }
        _ => {}
    }
    // The configuration itself (theorem names, permitted axioms) must be the stamped one (adversarial review
    // 2026-11-06, MINOR 5).
    let ch = sha256_file(&root.join(config))?;
    let manifest0 = fs::read_to_string(stamp.join("manifest.txt")).map_err(|e| format!("stamp manifest: {e}"))?;
    if !manifest0.lines().any(|l| l == format!("{ch}  {config}")) {
        return Err(format!("{config} (sha256 {ch}) is not the file recorded in {}/manifest.txt", stamp.display()));
    }
    let out = export(root, config)?;
    let h = sha256_file(&out)?;
    let manifest = fs::read_to_string(stamp.join("manifest.txt")).map_err(|e| format!("stamp manifest: {e}"))?;
    // Tied to this configuration's export file name (S4b adversarial review, NIT 7), not to any stamped export.
    let fname = out.file_name().map(|f| f.to_string_lossy().into_owned()).unwrap_or_default();
    if !manifest.lines().any(|l| l == format!("challenge-export {h}  {fname}")) {
        return Err(format!("challenge export {fname} (sha256 {h}) is not in {}/manifest.txt", stamp.display()));
    }
    println!("challenge: export sha256 {h} matches the stamped manifest");
    let (ok, o, e) = run(Command::new("lake").current_dir(root)
        .args(["comparator", "--config", config, "--challenge-from-export"]).arg(&out).arg("--paranoid"))?;
    print!("{o}{e}");
    if !ok || o.to_lowercase().contains("panic") || !o.contains("Your solution is okay!") {
        return Err("lake comparator rejected the solution (no acceptance line)".into());
    }
    Ok(true)
}

/// The comparator configurations in ROOT (`comparator*.json`), sorted.
fn configs(root: &Path) -> Vec<String> {
    let mut v: Vec<String> = fs::read_dir(root)
        .map(|rd| rd.flatten().map(|e| e.file_name().to_string_lossy().into_owned()).collect())
        .unwrap_or_default();
    v.retain(|n| n.starts_with("comparator") && n.ends_with(".json"));
    v.sort();
    v
}

/// The stamp a configuration is pinned to (`challenge:<config> <dir>` in `stamps/pins.txt`).
fn pinned(root: &Path, config: &str) -> Option<String> {
    let pins = fs::read_to_string(root.join("stamps/pins.txt")).ok()?;
    let key = format!("challenge:{config}");
    pins.lines()
        .filter(|l| !l.starts_with('#'))
        .filter_map(|l| l.split_once(' ').filter(|(k, _)| *k == key).map(|(_, d)| d.trim().to_string()))
        .last()
}

/// Judges every configuration; Ok(false) if any is unpinned or not yet solved (and none failed).
fn check_all(root: &Path) -> Result<bool, String> {
    let mut complete = true;
    for c in configs(root) {
        let Some(stamp) = pinned(root, &c) else {
            println!("comparator: {c} is not pinned to a stamp yet");
            complete = false;
            continue;
        };
        if check(root, &c, Path::new(&stamp)).map_err(|e| format!("{c}: {e}"))? {
            println!("comparator: {c} accepted against {stamp}");
        } else {
            println!("comparator: {c}: no challenge theorem is declared yet");
            complete = false;
        }
    }
    Ok(complete)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let r = match a.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        [_, "export", root, config] => export(Path::new(root), config).map(|_| ()),
        [_, "export-all", root] => configs(Path::new(root)).iter().try_for_each(|c| export(Path::new(root), c).map(|_| ())),
        [_, "check-all", root] => match check_all(Path::new(root)) {
            Ok(true) => Ok(()),
            Ok(false) => {
                println!("comparator: INCOMPLETE");
                std::process::exit(3);
            }
            Err(e) => Err(e),
        },
        _ => {
            eprintln!("usage: challenge export ROOT CONFIG | challenge export-all ROOT | challenge check-all ROOT");
            std::process::exit(2);
        }
    };
    if let Err(e) = r {
        println!("challenge: FAIL: {e}");
        std::process::exit(1);
    }
}
