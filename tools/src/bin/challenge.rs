#![forbid(unsafe_code)]
//! Statement matching against the frozen challenge.
//! `challenge export ROOT`: reads `ROOT/comparator.json`, builds the `challenge_module` and exports its
//! `theorem_names` (plus the constants the comparator requires) with `leanexport` into
//! `build/challenge/challenge.ndjson` (`make stamp` records its SHA-256).
//! `challenge check ROOT STAMPDIR`: exit 3 (skipped) if no challenge theorem is declared in the library yet
//! (per `build/audited.txt`), failure if only some are; otherwise re-exports, requires the export's SHA-256 to appear as a `challenge-export`
//! line of `STAMPDIR/manifest.txt` (so the challenge judged is the stamped one: `lake comparator
//! --challenge-from-export` does not check provenance itself), then runs
//! `lake comparator --challenge-from-export build/challenge/challenge.ndjson --paranoid`.

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

fn export(root: &Path) -> Result<std::path::PathBuf, String> {
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
fn check(root: &Path, stamp: &Path) -> Result<bool, String> {
    let cfg = json::parse(&fs::read_to_string(root.join("comparator.json")).map_err(|e| e.to_string())?)?;
    let names: Vec<&str> = cfg.get("theorem_names").and_then(|v| v.as_arr()).ok_or("comparator.json: theorem_names")?
        .iter().filter_map(|v| v.as_str()).collect();
    match solved(root, &names)? {
        0 => return Ok(false),
        k if k < names.len() => {
            return Err(format!("only {k} of {} challenge theorems are declared; a partial solution is not judged", names.len()))
        }
        _ => {}
    }
    let out = export(root)?;
    let h = sha256_file(&out)?;
    let manifest = fs::read_to_string(stamp.join("manifest.txt")).map_err(|e| format!("stamp manifest: {e}"))?;
    if !manifest.lines().any(|l| l.starts_with(&format!("challenge-export {h}"))) {
        return Err(format!("challenge export sha256 {h} is not in {}/manifest.txt", stamp.display()));
    }
    println!("challenge: export sha256 {h} matches the stamped manifest");
    let (ok, o, e) = run(Command::new("lake").current_dir(root)
        .args(["comparator", "--challenge-from-export"]).arg(&out).arg("--paranoid"))?;
    print!("{o}{e}");
    if !ok || o.to_lowercase().contains("panic") || !o.contains("Your solution is okay!") {
        return Err("lake comparator rejected the solution (no acceptance line)".into());
    }
    Ok(true)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let r = match a.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        [_, "export", root] => export(Path::new(root)).map(|_| ()),
        [_, "check", root, stamp] => match check(Path::new(root), Path::new(stamp)) {
            Ok(true) => Ok(()),
            Ok(false) => {
                println!("comparator: SKIPPED: no challenge theorem is declared in the library yet");
                std::process::exit(3);
            }
            Err(e) => Err(e),
        },
        _ => {
            eprintln!("usage: challenge export ROOT | challenge check ROOT STAMPDIR");
            std::process::exit(2);
        }
    };
    if let Err(e) = r {
        println!("challenge: FAIL: {e}");
        std::process::exit(1);
    }
}
