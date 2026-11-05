#![forbid(unsafe_code)]
//! `challenge ROOT STAMPDIR`: statement matching against the frozen challenge.
//! Reads `ROOT/comparator.json`, re-exports its `theorem_names` (plus the constants the comparator requires) from
//! the `challenge_module` with `leanexport` into `build/challenge/challenge.ndjson`, requires that export's SHA-256
//! to appear as a `challenge-export` line of `STAMPDIR/manifest.txt` (so the challenge judged is the stamped one:
//! `lake comparator --challenge-from-export` does not check provenance itself), then runs
//! `lake comparator --challenge-from-export build/challenge/challenge.ndjson --paranoid`.

use oscint_tools::json;
use oscint_tools::sys::{run, sha256_file};
use std::fs;
use std::path::Path;
use std::process::Command;

/// Constants `lake comparator` requires to be present in a challenge export (permitted axioms and the kernel's
/// built-in extensions), as listed in its `Exporting #[…]` line for Lean v4.35.0.
pub const REQUIRED: &[&str] = &[
    "propext", "Quot.sound", "Classical.choice", "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Nat", "Nat.zero",
    "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.gcd", "Nat.beq", "Nat.ble", "Nat.land",
    "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "Nat.pow", "Nat.log2", "String", "String.ofList",
    "Eq", "Eq.refl", "Bool", "Bool.true", "Bool.false", "outParam",
];

fn go(root: &Path, stamp: &Path) -> Result<(), String> {
    let cfg = json::parse(&fs::read_to_string(root.join("comparator.json")).map_err(|e| e.to_string())?)?;
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
    let out = dir.join("challenge.ndjson");
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
    let h = sha256_file(&out)?;
    let manifest = fs::read_to_string(stamp.join("manifest.txt")).map_err(|e| format!("stamp manifest: {e}"))?;
    if !manifest.lines().any(|l| l.starts_with(&format!("challenge-export {h}"))) {
        return Err(format!("challenge export sha256 {h} is not in {}/manifest.txt", stamp.display()));
    }
    println!("challenge: export sha256 {h} matches the stamped manifest");
    let (ok, o, e) = run(Command::new("lake").current_dir(root)
        .args(["comparator", "--challenge-from-export"]).arg(&out).arg("--paranoid"))?;
    print!("{o}{e}");
    if !ok || o.to_lowercase().contains("panic") {
        return Err("lake comparator rejected the solution".into());
    }
    Ok(())
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 3 {
        eprintln!("usage: challenge ROOT STAMPDIR");
        std::process::exit(2);
    }
    if let Err(e) = go(Path::new(&a[1]), Path::new(&a[2])) {
        println!("challenge: FAIL: {e}");
        std::process::exit(1);
    }
}
